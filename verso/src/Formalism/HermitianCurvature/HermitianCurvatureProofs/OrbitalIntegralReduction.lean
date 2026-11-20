import Formalism.HermitianCurvature.ThetaExistenceInductiveFromPieces
import Formalism.HermitianCurvature.HermitianCurvatureProofs.KernelNonzeroModulusDeterminantEq
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FirstKernelExplicitFormula
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegralLatticeRefinementIdentity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.GramKernelHermitian

noncomputable section

open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.P.A5x5 Formalism.FourierDecayAlt.P.A5x8 Formalism.FourierDecayAlt.P.A6x8 Filter Topology

namespace Formalism.FourierDecayAlt.P.OrbitalIntegralReduction

section Defs

variable {K : Type} [CommRing K]

abbrev Pr (n : ℕ) : Type := {p : Fin n × Fin n // p.1 < p.2}

def EE {n : ℕ} (y : Pr n → K) : Matrix (Fin n) (Fin n) K :=
  fun i j => if h : i < j then y ⟨(i, j), h⟩ else 0

def bx (R : Subring K) (Λ : AddSubgroup K) (ι : Type) [Fintype ι] (f : (ι → K) → ℂ) : ℂ :=
  (volL R Λ : ℂ) ^ Fintype.card ι * ∑ᶠ y : ι → K ⧸ Λ, f (fun i => Quotient.out (y i))

def BInv (Λ : AddSubgroup K) {ι : Type} (f : (ι → K) → ℂ) : Prop :=
  ∀ x l : ι → K, (∀ i, l i ∈ Λ) → f (x + l) = f x

def BSupp (L : AddSubgroup K) {ι : Type} (f : (ι → K) → ℂ) : Prop :=
  ∀ x, f x ≠ 0 → ∀ i, x i ∈ L

def HH {n : ℕ} (t : K) (d : Fin n → K) (y : Pr n → K) : Matrix (Fin n) (Fin n) K :=
  fun i j => if i = j then d i else if h : i < j then y ⟨(i, j), h⟩
    else if j.val + 1 = i.val then t else 0

def ZZ {n : ℕ} (t : K) (d : Fin n → K) (y : Pr n → K) : Matrix (Fin n) (Fin n) K :=
  (HH t d y).submatrix Fin.rev id

def Hm {m : ℕ} (t c : K) (ξ : Fin m → K) (u : Matrix (Fin (m + 1)) (Fin (m + 1)) K) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) K :=
  fun i j => Fin.cases
    (∑ k : Fin m, ξ (Fin.rev k) * (t * u k.castSucc j) + if j = Fin.last m then c else 0)
    (fun i' => t * u i'.castSucc j) i

def IsHess {A : Type} [CommRing A] {n : ℕ} (t : A) (M : Matrix (Fin n) (Fin n) A) : Prop :=
  ∀ i j : Fin n, (j.val + 1 = i.val → M i j = t) ∧ (j.val + 1 < i.val → M i j = 0)

def sg {A : Type} [CommRing A] : ∀ {n : ℕ}, Matrix (Fin n) (Fin n) A → A
  | 0, _ => 0
  | 1, _ => 0
  | (n + 2), M => M 0 0 * sg (M.submatrix (Fin.succ : Fin (n + 1) → Fin (n + 2)) Fin.succ) +
      M 0 1 * ∏ k : Fin n, M k.succ.succ k.succ.succ

def Bd (R : Subring K) (ϖ : Kˣ) (k : ℕ) (x : K) : Prop := (ϖ : K) ^ k * x ∈ R

def Sm (R : Subring K) (ϖ : Kˣ) (k : ℕ) (x : K) : Prop := ∃ r ∈ R, x = (ϖ : K) ^ k * r

def x0 {m : ℕ} (D' : K) (x : Fin m → K) : K := D' * Ring.inverse (∏ k, x k)

def xt {m : ℕ} (D' : K) (x : Fin m → K) : Fin (m + 1) → K := Fin.cons (x0 D' x) x

def sd {m : ℕ} (i : Fin m) : Pr (m + 1) := ⟨(i.castSucc, i.succ), Fin.castSucc_lt_succ⟩

def g1 {m : ℕ} (D' : K) (x : Fin m → K) (y : Pr (m + 1) → K) : K :=
  x0 D' x * ∑ i : Fin m, y (sd i) * Ring.inverse (xt D' x i.castSucc) * Ring.inverse (xt D' x i.succ)

open Classical in

def GG (R : Subring K) (ψ : AddChar K ℂ) (Φ : ∀ n : ℕ, Matrix (Fin n) (Fin n) K → ℂ) {m : ℕ} (D' : K)
    (x : Fin m → K) (y : Pr (m + 1) → K) : ℂ :=
  if ∀ k, IsUnit (x k) then
    (((modK R (∏ k, x k))⁻¹ : ℝ) : ℂ) * Φ (m + 1) (ZZ 0 (xt D' x) y) * ψ (g1 D' x y) else 0

def ee {m : ℕ} : Fin m ⊕ Pr (m + 1) → Pr (m + 1) ⊕ Fin m
  | Sum.inl i => Sum.inl (sd i)
  | Sum.inr p => if h : p.1.1 = 0 then Sum.inr (p.1.2.pred (by
        intro h2; have := p.2; rw [h, h2] at this; exact lt_irrefl _ this))
      else Sum.inl ⟨((p.1.1.pred h).castSucc, p.1.2), by
        have := p.2
        rw [Fin.lt_def] at this ⊢
        simp only [Fin.val_castSucc, Fin.val_pred]
        omega⟩

def xs {m : ℕ} (n : Pr (m + 1) → K) : Fin m → K := fun i => n (sd i)

def ys {m : ℕ} (n : Pr (m + 1) → K) (τ : Fin m → K) : Pr (m + 1) → K :=
  fun p => Sum.elim n τ (ee (Sum.inr p))

end Defs

section Cst

variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]

structure Cst (R : Subring K) (ϖ : Kˣ) (L₀ Λ₀ : AddSubgroup K) (Q : Set K) (a b : ℕ) : Prop where
  adic : Adic R ϖ
  L0 : ∀ x ∈ L₀, Bd R ϖ a x
  Qb : ∀ d ∈ Q, Bd R ϖ a d
  Qi : ∀ d ∈ Q, ∀ d' : K, d * d' = 1 → Bd R ϖ a d'
  abelian₂ : ∀ x, Sm R ϖ b x → x ∈ Λ₀

end Cst

section BD

variable {K : Type} [CommRing K] {R : Subring K} {ϖ : Kˣ}

/- English proof (translation)
Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_le h`. Establish `: (ϖ : K) ^ (k + d) * x = (ϖ : K) ^ d * ((ϖ : K) ^ k * x)` using `by ring`. Unfold `Bd`. Rewrite using `[this]`. Conclude with `R.mul_mem (R.pow_mem hϖ d) hx`.
-/
theorem Bd.mono (hϖ : (ϖ : K) ∈ R) {k l : ℕ} (h : k ≤ l) {x : K} (hx : Bd R ϖ k x) : Bd R ϖ l x := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  have : (ϖ : K) ^ (k + d) * x = (ϖ : K) ^ d * ((ϖ : K) ^ k * x) := by ring
  unfold Bd
  rw [this]
  exact R.mul_mem (R.pow_mem hϖ d) hx

/- English proof (translation)
The claim follows from `R.mul_mem (R.pow_mem hϖ k) hx`.
-/
theorem Bd.of_mem (hϖ : (ϖ : K) ∈ R) {x : K} (hx : x ∈ R) (k : ℕ) : Bd R ϖ k x :=
  R.mul_mem (R.pow_mem hϖ k) hx

/- English proof (translation)
Unfold `Bd`. Rewrite using `[mul_add]`. Conclude with `R.add_mem hx hy`.
-/
theorem Bd.add {k : ℕ} {x y : K} (hx : Bd R ϖ k x) (hy : Bd R ϖ k y) : Bd R ϖ k (x + y) := by
  unfold Bd; rw [mul_add]; exact R.add_mem hx hy

/- English proof (translation)
Unfold `Bd`. Rewrite using `[mul_neg]`. Conclude with `R.neg_mem hx`.
-/
theorem Bd.neg {k : ℕ} {x : K} (hx : Bd R ϖ k x) : Bd R ϖ k (-x) := by
  unfold Bd; rw [mul_neg]; exact R.neg_mem hx

/- English proof (translation)
Rewrite using `[sub_eq_add_neg]`. Conclude with `hx.add hy.neg`.
-/
theorem Bd.sub {k : ℕ} {x y : K} (hx : Bd R ϖ k x) (hy : Bd R ϖ k y) : Bd R ϖ k (x - y) := by
  rw [sub_eq_add_neg]; exact hx.add hy.neg

/- English proof (translation)
Establish `: (ϖ : K) ^ (k + l) * (x * y) = ((ϖ : K) ^ k * x) * ((ϖ : K) ^ l * y)` using `by ring`. Unfold `Bd`. Rewrite using `[this]`. Conclude with `R.mul_mem hx hy`.
-/
theorem Bd.mul {k l : ℕ} {x y : K} (hx : Bd R ϖ k x) (hy : Bd R ϖ l y) : Bd R ϖ (k + l) (x * y) := by
  have : (ϖ : K) ^ (k + l) * (x * y) = ((ϖ : K) ^ k * x) * ((ϖ : K) ^ l * y) := by ring
  unfold Bd; rw [this]; exact R.mul_mem hx hy

/- English proof (translation)
Unfold `Bd`. Rewrite using `[← mul_assoc]`. Conclude with `R.mul_mem hx hy`.
-/
theorem Bd.mul_mem {k : ℕ} {x y : K} (hx : Bd R ϖ k x) (hy : y ∈ R) : Bd R ϖ k (x * y) := by
  unfold Bd; rw [← mul_assoc]; exact R.mul_mem hx hy

/- English proof (translation)
Unfold `Bd`. Rewrite using `[Finset.mul_sum]`. Conclude with `R.sum_mem h`.
-/
theorem Bd.sum {ι : Type} {k : ℕ} (S : Finset ι) (f : ι → K) (h : ∀ i ∈ S, Bd R ϖ k (f i)) :
    Bd R ϖ k (∑ i ∈ S, f i) := by
  unfold Bd; rw [Finset.mul_sum]; exact R.sum_mem h

/- English proof (translation)
Establish `: (ϖ : K) ^ (S.card * k) * ∏ i ∈ S, f i = ∏ i ∈ S, ((ϖ : K) ^ k * f i)`. Rewrite using `[Finset.prod_mul_distrib, Finset.prod_const, ← pow_mul, mul_comm k]`. Unfold `Bd`. Rewrite using `[this]`. Conclude with `R.prod_mem h`.
-/
theorem Bd.prod {ι : Type} {k : ℕ} (S : Finset ι) (f : ι → K) (h : ∀ i ∈ S, Bd R ϖ k (f i)) :
    Bd R ϖ (S.card * k) (∏ i ∈ S, f i) := by
  have : (ϖ : K) ^ (S.card * k) * ∏ i ∈ S, f i = ∏ i ∈ S, ((ϖ : K) ^ k * f i) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, ← pow_mul, mul_comm k]
  unfold Bd; rw [this]; exact R.prod_mem h

/- English proof (translation)
Establish `: (ϖ : K) ^ (n * k) * x ^ n = ((ϖ : K) ^ k * x) ^ n`. Rewrite using `[mul_pow, ← pow_mul, mul_comm k]`. Unfold `Bd`. Rewrite using `[this]`. Conclude with `R.pow_mem hx n`.
-/
theorem Bd.pow {k : ℕ} {x : K} (hx : Bd R ϖ k x) (n : ℕ) : Bd R ϖ (n * k) (x ^ n) := by
  have : (ϖ : K) ^ (n * k) * x ^ n = ((ϖ : K) ^ k * x) ^ n := by
    rw [mul_pow, ← pow_mul, mul_comm k]
  unfold Bd; rw [this]; exact R.pow_mem hx n

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨r, hr, rfl⟩`. Simplify using `using hr`. Introduce `h; exact ⟨x, h, by simp⟩`.
-/
theorem sm_zero_iff {x : K} : Sm R ϖ 0 x ↔ x ∈ R := by
  constructor
  · rintro ⟨r, hr, rfl⟩; simpa using hr
  · intro h; exact ⟨x, h, by simp⟩

/- English proof (translation)
Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_le h`. Take `⟨r, hr, rfl⟩` from `hx`. Conclude with `⟨(ϖ : K) ^ d * r, R.mul_mem (R.pow_mem hϖ d) hr, by ring⟩`.
-/
theorem Sm.mono (hϖ : (ϖ : K) ∈ R) {k l : ℕ} (h : l ≤ k) {x : K} (hx : Sm R ϖ k x) : Sm R ϖ l x := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  obtain ⟨r, hr, rfl⟩ := hx
  exact ⟨(ϖ : K) ^ d * r, R.mul_mem (R.pow_mem hϖ d) hr, by ring⟩

/- English proof (translation)
Take `⟨r, hr, rfl⟩` from `hx`. Conclude with `R.mul_mem (R.pow_mem hϖ k) hr`.
-/
theorem Sm.mem (hϖ : (ϖ : K) ∈ R) {k : ℕ} {x : K} (hx : Sm R ϖ k x) : x ∈ R := by
  obtain ⟨r, hr, rfl⟩ := hx
  exact R.mul_mem (R.pow_mem hϖ k) hr

/- English proof (translation)
Assemble the required witnesses or components as `⟨0, R.zero_mem, by simp⟩`.
-/
theorem Sm.zero (k : ℕ) : Sm R ϖ k 0 := ⟨0, R.zero_mem, by simp⟩

/- English proof (translation)
Take `⟨r, hr, rfl⟩` from `hx`. Take `⟨q, hq, rfl⟩` from `hy`. Conclude with `⟨r + q, R.add_mem hr hq, by ring⟩`.
-/
theorem Sm.add {k : ℕ} {x y : K} (hx : Sm R ϖ k x) (hy : Sm R ϖ k y) : Sm R ϖ k (x + y) := by
  obtain ⟨r, hr, rfl⟩ := hx
  obtain ⟨q, hq, rfl⟩ := hy
  exact ⟨r + q, R.add_mem hr hq, by ring⟩

/- English proof (translation)
Take `⟨r, hr, rfl⟩` from `hx`. Conclude with `⟨-r, R.neg_mem hr, by ring⟩`.
-/
theorem Sm.neg {k : ℕ} {x : K} (hx : Sm R ϖ k x) : Sm R ϖ k (-x) := by
  obtain ⟨r, hr, rfl⟩ := hx
  exact ⟨-r, R.neg_mem hr, by ring⟩

/- English proof (translation)
Rewrite using `[sub_eq_add_neg]`. Conclude with `hx.add hy.neg`.
-/
theorem Sm.sub {k : ℕ} {x y : K} (hx : Sm R ϖ k x) (hy : Sm R ϖ k y) : Sm R ϖ k (x - y) := by
  rw [sub_eq_add_neg]; exact hx.add hy.neg

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => simpa using Sm.zero k`. Consider the case `insert i S hi ih`. Rewrite using `[Finset.sum_insert hi]`. Conclude with `(h i (Finset.mem_insert_self _ _)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))`.
-/
theorem Sm.sum {ι : Type} {k : ℕ} (S : Finset ι) (f : ι → K) (h : ∀ i ∈ S, Sm R ϖ k (f i)) :
    Sm R ϖ k (∑ i ∈ S, f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using Sm.zero k
  | insert i S hi ih =>
    rw [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/- English proof (translation)
Take `⟨r, hr, rfl⟩` from `hx`. Conclude with `⟨r * y, R.mul_mem hr hy, by ring⟩`.
-/
theorem Sm.mul_mem {k : ℕ} {x y : K} (hx : Sm R ϖ k x) (hy : y ∈ R) : Sm R ϖ k (x * y) := by
  obtain ⟨r, hr, rfl⟩ := hx
  exact ⟨r * y, R.mul_mem hr hy, by ring⟩

/- English proof (translation)
Take `⟨r, hr, rfl⟩` from `hx`. Take `⟨q, hq, rfl⟩` from `hy`. Conclude with `⟨r * q, R.mul_mem hr hq, by ring⟩`.
-/
theorem Sm.mul {k l : ℕ} {x y : K} (hx : Sm R ϖ k x) (hy : Sm R ϖ l y) : Sm R ϖ (k + l) (x * y) := by
  obtain ⟨r, hr, rfl⟩ := hx
  obtain ⟨q, hq, rfl⟩ := hy
  exact ⟨r * q, R.mul_mem hr hq, by ring⟩

/- English proof (translation)
Take `⟨r, hr, rfl⟩` from `hx`. Conclude with `⟨r * ((ϖ : K) ^ l * y), R.mul_mem hr hy, by ring⟩`.
-/
theorem Sm.mul_bd {k l : ℕ} {x y : K} (hx : Sm R ϖ (k + l) x) (hy : Bd R ϖ l y) :
    Sm R ϖ k (x * y) := by
  obtain ⟨r, hr, rfl⟩ := hx
  exact ⟨r * ((ϖ : K) ^ l * y), R.mul_mem hr hy, by ring⟩

/- English proof (translation)
The claim follows from `Bd.of_mem hϖ (hx.mem hϖ) l`.
-/
theorem Sm.bd (hϖ : (ϖ : K) ∈ R) {k : ℕ} {x : K} (hx : Sm R ϖ k x) (l : ℕ) : Bd R ϖ l x :=
  Bd.of_mem hϖ (hx.mem hϖ) l

/- English proof (translation)
Establish `h1 : ((ϖ⁻¹ : Kˣ) : K) ^ k * (ϖ : K) ^ k = 1` using `by rw [← mul_pow]; simp`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `⟨_, h, by rw [← mul_assoc, h1, one_mul]⟩`. Introduce and unpack `⟨r, hr, rfl⟩`.

Unfold `Bd`. Rewrite using `[← mul_assoc, mul_comm ((ϖ : K) ^ k), h1, one_mul]`. Conclude with `hr`.
-/
theorem bd_iff_sm_mul {k : ℕ} {x : K} : Bd R ϖ k x ↔ ∃ r ∈ R, x = ((ϖ⁻¹ : Kˣ) : K) ^ k * r := by
  have h1 : ((ϖ⁻¹ : Kˣ) : K) ^ k * (ϖ : K) ^ k = 1 := by rw [← mul_pow]; simp
  constructor
  · intro h
    exact ⟨_, h, by rw [← mul_assoc, h1, one_mul]⟩
  · rintro ⟨r, hr, rfl⟩
    unfold Bd
    rw [← mul_assoc, mul_comm ((ϖ : K) ^ k), h1, one_mul]
    exact hr

variable [TopologicalSpace K] [IsTopologicalRing K]

/- English proof (translation)
Take `⟨r, hr, rfl⟩` from `hε`. Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_le hk`. Take `⟨v, hv, e⟩` from `h.unit_one ((ϖ : K) ^ (1 + d) * r) ⟨(ϖ : K) ^ d * r, R.mul_mem (R.pow_mem h.mem d) hr, by ring⟩`. Conclude with `⟨v, hv, e, -(r * v), R.neg_mem (R.mul_mem hr hv), by linear_combination e⟩`.
-/
theorem Sm.one_add_inv (h : Adic R ϖ) {k : ℕ} (hk : 1 ≤ k) {ε : K} (hε : Sm R ϖ k ε) :
    ∃ v ∈ R, (1 + ε) * v = 1 ∧ Sm R ϖ k (v - 1) := by
  obtain ⟨r, hr, rfl⟩ := hε
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  obtain ⟨v, hv, e⟩ := h.unit_one ((ϖ : K) ^ (1 + d) * r)
    ⟨(ϖ : K) ^ d * r, R.mul_mem (R.pow_mem h.mem d) hr, by ring⟩
  exact ⟨v, hv, e, -(r * v), R.neg_mem (R.mul_mem hr hv), by linear_combination e⟩

/- English proof (translation)
Take `⟨a, ha⟩` from `hC.elim_directed_cover (fun a : ℕ => {x : K | (ϖ : K) ^ a * x ∈ R}) (fun a => h.isOpen.preimage (continuous_const.mul continuous_id)) (fun x _ => by`. Take `⟨m, hm⟩` from `h.absorb x`. Conclude with `Set.mem_iUnion.2 ⟨m, hm⟩)`. Use the proof step `(Monotone.directed_le (by`. Introduce `a b hab x hx`.

Conclude with `Bd.mono h.mem hab hx))`. Conclude with `⟨a, fun x hx => ha hx⟩`.
-/
theorem adic_bounded (h : Adic R ϖ) {C : Set K} (hC : IsCompact C) : ∃ a : ℕ, ∀ x ∈ C, Bd R ϖ a x := by
  obtain ⟨a, ha⟩ := hC.elim_directed_cover (fun a : ℕ => {x : K | (ϖ : K) ^ a * x ∈ R})
    (fun a => h.isOpen.preimage (continuous_const.mul continuous_id))
    (fun x _ => by
      obtain ⟨m, hm⟩ := h.absorb x
      exact Set.mem_iUnion.2 ⟨m, hm⟩)
    (Monotone.directed_le (by
      intro a b hab x hx
      exact Bd.mono h.mem hab hx))
  exact ⟨a, fun x hx => ha hx⟩

/- English proof (translation)
Establish `hu : IsUnit x` using `IsUnit.of_mul_eq_one y h`. Take `⟨u, rfl⟩` from `hu`. Rewrite using `[Ring.inverse_unit]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem ringInverse_eq {x y : K} (h : x * y = 1) : Ring.inverse x = y := by
  have hu : IsUnit x := IsUnit.of_mul_eq_one y h
  obtain ⟨u, rfl⟩ := hu
  rw [Ring.inverse_unit]
  calc ((u⁻¹ : Kˣ) : K) = ((u⁻¹ : Kˣ) : K) * ((u : K) * y) := by rw [h, mul_one]
    _ = y := by rw [← mul_assoc]; simp

/- English proof (translation)
Use `(hD.selfDual r).2 hr 1 R.one_mem` as an intermediate fact. Simplify using `using this`.
-/
theorem psi_R {ψ : AddChar K ℂ} (hD : LocalDatum K R ψ) {r : K} (hr : r ∈ R) : ψ r = 1 := by
  have := (hD.selfDual r).2 hr 1 R.one_mem
  simpa using this

/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.A5x6.modK_eq_one R d e hd he h`.
-/
theorem modK_unitR {d e : K} (hd : d ∈ R) (he : e ∈ R) (h : d * e = 1) : modK R d = 1 :=
  Formalism.FourierDecayAlt.P.A5x6.modK_eq_one R d e hd he h

/- English proof (translation)
Take `⟨x, rfl⟩` from `hx`. Take `⟨y, rfl⟩` from `hy`. Conclude with `modK_mul h.isOpen h.isCompact x y`.
-/
theorem modK_mul_isUnit (h : Adic R ϖ) {x y : K} (hx : IsUnit x) (hy : IsUnit y) :
    modK R (x * y) = modK R x * modK R y := by
  obtain ⟨x, rfl⟩ := hx
  obtain ⟨y, rfl⟩ := hy
  exact modK_mul h.isOpen h.isCompact x y

end BD

section TK

/- English proof (translation)
Use `finsum_eq_of_bijective (fun q => π₂ (s₁ q)) ⟨?_, ?_⟩ ?_` and prove the remaining obligations. Introduce `q q' h`. Use `(hk _ _).2 h` as an intermediate fact. Rewrite `this` using `[h₁, h₁]`. Then use the resulting hypothesis. Introduce `q`.

Use `⟨π₁ (s₂ q), ?_⟩` and prove the remaining obligations. Use `show π₂ (s₁ (π₁ (s₂ q))) = q`. Rewrite using `[(hk _ _).1 (h₁ (π₁ (s₂ q))), h₂]`. Introduce `q`. Conclude with `hf _ _ ((hk _ _).2 (h₂ _).symm)`.
-/
theorem tk_reindex {X Q₁ Q₂ : Type} (π₁ : X → Q₁) (π₂ : X → Q₂) (s₁ : Q₁ → X) (s₂ : Q₂ → X)
    (h₁ : ∀ q, π₁ (s₁ q) = q) (h₂ : ∀ q, π₂ (s₂ q) = q)
    (hk : ∀ x x', π₁ x = π₁ x' ↔ π₂ x = π₂ x') (f : X → ℂ)
    (hf : ∀ x x', π₁ x = π₁ x' → f x = f x') : ∑ᶠ q, f (s₁ q) = ∑ᶠ q, f (s₂ q) := by
  refine finsum_eq_of_bijective (fun q => π₂ (s₁ q)) ⟨?_, ?_⟩ ?_
  · intro q q' h
    have := (hk _ _).2 h
    rwa [h₁, h₁] at this
  · intro q
    refine ⟨π₁ (s₂ q), ?_⟩
    show π₂ (s₁ (π₁ (s₂ q))) = q
    rw [(hk _ _).1 (h₁ (π₁ (s₂ q))), h₂]
  · intro q
    exact hf _ _ ((hk _ _).2 (h₂ _).symm)

variable {K : Type} [CommRing K]

/- English proof (translation)
Take `⟨h, hh⟩` from `QuotientAddGroup.mk_out_eq_add Λ x`. Rewrite using `[hh]`. Simplify using the standard rewrite rules.
-/
theorem tk_out_sub (Λ : AddSubgroup K) (x : K) : (Quotient.out (x : K ⧸ Λ) : K) - x ∈ Λ := by
  obtain ⟨h, hh⟩ := QuotientAddGroup.mk_out_eq_add Λ x
  rw [hh]; simp

/- English proof (translation)
Rewrite using `[QuotientAddGroup.eq]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `Λ.neg_mem h` as an intermediate fact. Simplify `this` using `[sub_eq_add_neg, add_comm]`.

Introduce `h`. Use `Λ.neg_mem h` as an intermediate fact. Simplify `this` using `[sub_eq_add_neg, add_comm]`.
-/
theorem tk_mk_eq (Λ : AddSubgroup K) (x y : K) : ((x : K ⧸ Λ) = (y : K ⧸ Λ)) ↔ x - y ∈ Λ := by
  rw [QuotientAddGroup.eq]
  constructor
  · intro h
    have := Λ.neg_mem h
    simpa [sub_eq_add_neg, add_comm] using this
  · intro h
    have := Λ.neg_mem h
    simpa [sub_eq_add_neg, add_comm] using this

variable [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K} {ψ : AddChar K ℂ}

/- English proof (translation)
Simplify using `[intK, bx]`.
-/
theorem intK_eq_bx (Λ : AddSubgroup K) (d : ℕ) (f : (Fin d → K) → ℂ) :
    intK R Λ d f = bx R Λ (Fin d) f := by
  simp [intK, bx]

/- English proof (translation)
Establish `: f = g` using `funext h`. Rewrite using `[this]`.
-/
theorem bx_congr (Λ : AddSubgroup K) {ι : Type} [Fintype ι] {f g : (ι → K) → ℂ} (h : ∀ x, f x = g x) :
    bx R Λ ι f = bx R Λ ι g := by
  have : f = g := funext h
  rw [this]

/- English proof (translation)
Simplify using `[bx]`.
-/
theorem bx_zero (Λ : AddSubgroup K) {ι : Type} [Fintype ι] : bx R Λ ι (fun _ => 0) = 0 := by
  simp [bx]

/- English proof (translation)
Unfold `bx`. Rewrite using `[← mul_finsum]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem bx_mul_left (Λ : AddSubgroup K) {ι : Type} [Fintype ι] (a : ℂ) (f : (ι → K) → ℂ) :
    bx R Λ ι (fun x => a * f x) = a * bx R Λ ι f := by
  unfold bx
  rw [← mul_finsum]
  ring

/- English proof (translation)
Use `⟨hΛ.1.inter hΛ'.1, ?_⟩` and prove the remaining obligations. Establish `hc : IsClosed (Λ' : Set K)` using `AddSubgroup.isClosed_of_isOpen Λ' hΛ'.1`. Conclude with `hΛ.2.inter_right hc`.
-/
theorem tk_lat_inf {Λ Λ' : AddSubgroup K} (hΛ : IsLat Λ) (hΛ' : IsLat Λ') : IsLat (Λ ⊓ Λ') := by
  refine ⟨hΛ.1.inter hΛ'.1, ?_⟩
  have hc : IsClosed (Λ' : Set K) := AddSubgroup.isClosed_of_isOpen Λ' hΛ'.1
  exact hΛ.2.inter_right hc

/- English proof (translation)
Establish `hR` using `lat_R hD.isOpen hD.isCompact`. Establish `hne : Λ'.relIndex Λ ≠ 0` using `relIndex_ne_zero hΛ'.1 hΛ.2`. Establish `: Finite (Λ ⧸ Λ'.addSubgroupOf Λ)` using `Nat.finite_of_card_ne_zero hne`. Set `e : (ι → K ⧸ Λ') ≃ (ι → K ⧸ Λ) × (ι → Λ ⧸ Λ'.addSubgroupOf Λ)` to `(Equiv.piCongrRight fun _ => AddSubgroup.quotientEquivProdOfLE hle).trans (Equiv.arrowProdEquivProdArrow _ _ _)`. Establish `key : ∑ᶠ y : ι → K ⧸ Λ', f (fun i => Quotient.out (y i)) = ((Λ'.relIndex Λ : ℂ)) ^ Fintype.card ι * ∑ᶠ y : ι → K ⧸ Λ, f (fun i => Quotient.out (y i))`.

Establish `hc : (Nat.card (ι → Λ ⧸ Λ'.addSubgroupOf Λ) : ℂ) = ((Λ'.relIndex Λ : ℂ)) ^ Fintype.card ι`. Rewrite using `[Nat.card_fun]`. Simplify using `[AddSubgroup.relIndex, AddSubgroup.index]`. Rewrite using `[← hc, ← Formalism.FourierDecayAlt.P.A6x3.finsum_fst e (fun y : ι → K ⧸ Λ => f (fun i => Quotient.out (y i)))]`. Use `finsum_congr fun y => ?_` and prove the remaining obligations.

Use `hf (fun i => Quotient.out (y i)) (fun i => (Quotient.out (AddSubgroup.quotientEquivProdOfLE hle (y i)).1 : K) - (Quotient.out (y i) : K)) (fun i => Formalism.FourierDecayAlt.P.A6x3.out_sub_mem hle (y i))` as an intermediate fact. Rewrite using `[← this]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using `[e]`.

Unfold `bx`. Rewrite using `[key, Formalism.FourierDecayAlt.P.A6x3.volL_refine hR (Formalism.FourierDecayAlt.P.A6x3.lat_iff.1 hΛ') (Formalism.FourierDecayAlt.P.A6x3.lat_iff.1 hΛ) hle]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem tk_refine (hD : LocalDatum K R ψ) {ι : Type} [Fintype ι] {Λ Λ' : AddSubgroup K}
    (hΛ : IsLat Λ) (hΛ' : IsLat Λ') (hle : Λ' ≤ Λ) (f : (ι → K) → ℂ) (hf : BInv Λ f) :
    bx R Λ' ι f = bx R Λ ι f := by
  have hR := lat_R hD.isOpen hD.isCompact
  have hne : Λ'.relIndex Λ ≠ 0 := relIndex_ne_zero hΛ'.1 hΛ.2
  have : Finite (Λ ⧸ Λ'.addSubgroupOf Λ) := Nat.finite_of_card_ne_zero hne
  let e : (ι → K ⧸ Λ') ≃ (ι → K ⧸ Λ) × (ι → Λ ⧸ Λ'.addSubgroupOf Λ) :=
    (Equiv.piCongrRight fun _ => AddSubgroup.quotientEquivProdOfLE hle).trans
      (Equiv.arrowProdEquivProdArrow _ _ _)
  have key : ∑ᶠ y : ι → K ⧸ Λ', f (fun i => Quotient.out (y i)) =
      ((Λ'.relIndex Λ : ℂ)) ^ Fintype.card ι * ∑ᶠ y : ι → K ⧸ Λ, f (fun i => Quotient.out (y i)) := by
    have hc : (Nat.card (ι → Λ ⧸ Λ'.addSubgroupOf Λ) : ℂ) =
        ((Λ'.relIndex Λ : ℂ)) ^ Fintype.card ι := by
      rw [Nat.card_fun]
      simp [AddSubgroup.relIndex, AddSubgroup.index]
    rw [← hc, ← Formalism.FourierDecayAlt.P.A6x3.finsum_fst e (fun y : ι → K ⧸ Λ => f (fun i => Quotient.out (y i)))]
    refine finsum_congr fun y => ?_
    have := hf (fun i => Quotient.out (y i))
      (fun i => (Quotient.out (AddSubgroup.quotientEquivProdOfLE hle (y i)).1 : K) -
        (Quotient.out (y i) : K)) (fun i => Formalism.FourierDecayAlt.P.A6x3.out_sub_mem hle (y i))
    rw [← this]
    congr 1
    funext i
    simp [e]
  unfold bx
  rw [key, Formalism.FourierDecayAlt.P.A6x3.volL_refine hR (Formalism.FourierDecayAlt.P.A6x3.lat_iff.1 hΛ')
    (Formalism.FourierDecayAlt.P.A6x3.lat_iff.1 hΛ) hle]
  push_cast
  ring

/- English proof (translation)
Rewrite using `[← tk_refine hD hΛ (tk_lat_inf hΛ hΛ') inf_le_left f h, ← tk_refine hD hΛ' (tk_lat_inf hΛ hΛ') inf_le_right f h']`.
-/
theorem bx_indep (hD : LocalDatum K R ψ) {ι : Type} [Fintype ι] {Λ Λ' : AddSubgroup K}
    (hΛ : IsLat Λ) (hΛ' : IsLat Λ') (f : (ι → K) → ℂ) (h : BInv Λ f) (h' : BInv Λ' f) :
    bx R Λ ι f = bx R Λ' ι f := by
  rw [← tk_refine hD hΛ (tk_lat_inf hΛ hΛ') inf_le_left f h,
    ← tk_refine hD hΛ' (tk_lat_inf hΛ hΛ') inf_le_right f h']

/- English proof (translation)
Take `⟨t, ht⟩` from `hC.elim_finite_subcover (fun q : Q => {y : K | y - s q ∈ Λ}) (fun q => hΛ.preimage (continuous_id.sub continuous_const)) (fun y _ => by`. Take `⟨q, hq⟩` from `hsurj y`. Conclude with `Set.mem_iUnion.2 ⟨q, hq⟩)`. Use `t.finite_toSet.subset ?_` and prove the remaining obligations. Introduce `q hq`.

Take `⟨q', hq', h⟩` from `Set.mem_iUnion₂.1 (ht hq)`. Rewrite using `[hinj q q' h]`. Conclude with `hq'`.
-/
theorem tk_fin_cpt {Q : Type} (Λ : AddSubgroup K) (hΛ : IsOpen (Λ : Set K)) (s : Q → K)
    (hinj : ∀ q q', s q - s q' ∈ Λ → q = q') (hsurj : ∀ y : K, ∃ q, y - s q ∈ Λ) {C : Set K}
    (hC : IsCompact C) : {q | s q ∈ C}.Finite := by
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover (fun q : Q => {y : K | y - s q ∈ Λ})
    (fun q => hΛ.preimage (continuous_id.sub continuous_const))
    (fun y _ => by
      obtain ⟨q, hq⟩ := hsurj y
      exact Set.mem_iUnion.2 ⟨q, hq⟩)
  refine t.finite_toSet.subset ?_
  intro q hq
  obtain ⟨q', hq', h⟩ := Set.mem_iUnion₂.1 (ht hq)
  rw [hinj q q' h]
  exact hq'

/- English proof (translation)
Establish `h1 : ∀ i, {z : K ⧸ Λ | (Quotient.out z : K) ∈ C i}.Finite` using `fun i => tk_fin_cpt Λ hΛ (fun z : K ⧸ Λ => (Quotient.out z : K)) (fun q q' h => by`. Use `(tk_mk_eq Λ _ _).2 h` as an intermediate fact. Rewrite using `[QuotientAddGroup.out_eq', QuotientAddGroup.out_eq'] at this)` and apply the resulting hypothesis. Use the proof step `(fun y => ⟨(y : K ⧸ Λ), by`. Use `Λ.neg_mem (tk_out_sub Λ y)` as an intermediate fact.

Simplify using `using this⟩) (hC i)`. Use `(Set.Finite.pi' h1).subset ?_` and prove the remaining obligations. Introduce `y hy i`. Conclude with `hy i`.
-/
theorem tk_fin_box {ι : Type} [Finite ι] (Λ : AddSubgroup K) (hΛ : IsOpen (Λ : Set K))
    (C : ι → Set K) (hC : ∀ i, IsCompact (C i)) :
    {y : ι → K ⧸ Λ | ∀ i, (Quotient.out (y i) : K) ∈ C i}.Finite := by
  have h1 : ∀ i, {z : K ⧸ Λ | (Quotient.out z : K) ∈ C i}.Finite := fun i =>
    tk_fin_cpt Λ hΛ (fun z : K ⧸ Λ => (Quotient.out z : K))
      (fun q q' h => by
        have := (tk_mk_eq Λ _ _).2 h
        rwa [QuotientAddGroup.out_eq', QuotientAddGroup.out_eq'] at this)
      (fun y => ⟨(y : K ⧸ Λ), by
        have := Λ.neg_mem (tk_out_sub Λ y)
        simpa using this⟩) (hC i)
  refine (Set.Finite.pi' h1).subset ?_
  intro y hy i
  exact hy i

/- English proof (translation)
Unfold `bx`. Rewrite using `[← mul_finsum, Fintype.card_sum, pow_add, mul_assoc]`. Use `congr 2`. Rewrite using `[← finsum_comp_equiv (Equiv.sumArrowEquivProdArrow ι κ (K ⧸ Λ)).symm]`. Establish `hfin : (Function.support (fun p : (ι → K ⧸ Λ) × (κ → K ⧸ Λ) => f (fun i => Quotient.out ((Equiv.sumArrowEquivProdArrow ι κ (K ⧸ Λ)).symm p i)))).Finite`.

Use `((tk_fin_box Λ hΛ.1 (fun _ : ι => (L : Set K)) (fun _ => hL.2)).prod (tk_fin_box Λ hΛ.1 (fun _ : κ => (L : Set K)) (fun _ => hL.2))).subset ?_` and prove the remaining obligations. Introduce `p hp`. Use `hs _ hp` as an intermediate fact. Conclude with `⟨fun i => this (Sum.inl i), fun i => this (Sum.inr i)⟩`. Rewrite using `[finsum_curry _ hfin]`.

Use `finsum_congr fun a => finsum_congr fun b => ?_` and prove the remaining obligations. Use `congr 1`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `rcases i with i | i <;> rfl`.
-/
theorem bx_sum (_hD : LocalDatum K R ψ) {ι κ : Type} [Fintype ι] [Fintype κ] {Λ L : AddSubgroup K}
    (hΛ : IsLat Λ) (hL : IsLat L) (f : (ι ⊕ κ → K) → ℂ) (hs : BSupp L f) :
    bx R Λ (ι ⊕ κ) f = bx R Λ ι (fun a => bx R Λ κ (fun b => f (Sum.elim a b))) := by
  unfold bx
  rw [← mul_finsum, Fintype.card_sum, pow_add, mul_assoc]
  congr 2
  rw [← finsum_comp_equiv (Equiv.sumArrowEquivProdArrow ι κ (K ⧸ Λ)).symm]
  have hfin : (Function.support (fun p : (ι → K ⧸ Λ) × (κ → K ⧸ Λ) =>
      f (fun i => Quotient.out ((Equiv.sumArrowEquivProdArrow ι κ (K ⧸ Λ)).symm p i)))).Finite := by
    refine ((tk_fin_box Λ hΛ.1 (fun _ : ι => (L : Set K)) (fun _ => hL.2)).prod
      (tk_fin_box Λ hΛ.1 (fun _ : κ => (L : Set K)) (fun _ => hL.2))).subset ?_
    intro p hp
    have := hs _ hp
    exact ⟨fun i => this (Sum.inl i), fun i => this (Sum.inr i)⟩
  rw [finsum_curry _ hfin]
  refine finsum_congr fun a => finsum_congr fun b => ?_
  congr 1
  funext i
  rcases i with i | i <;> rfl

/- English proof (translation)
Unfold `bx`. Rewrite using `[Fintype.card_congr e]`. Use `congr 1`. Rewrite using `[← finsum_comp_equiv (Equiv.arrowCongr e (Equiv.refl (K ⧸ Λ)))]`. Both sides reduce to the same expression.
-/
theorem bx_equiv {ι κ : Type} [Fintype ι] [Fintype κ] (e : ι ≃ κ) (Λ : AddSubgroup K)
    (f : (κ → K) → ℂ) : bx R Λ κ f = bx R Λ ι (fun a => f (fun k => a (e.symm k))) := by
  unfold bx
  rw [Fintype.card_congr e]
  congr 1
  rw [← finsum_comp_equiv (Equiv.arrowCongr e (Equiv.refl (K ⧸ Λ)))]
  rfl

/- English proof (translation)
Establish `hR` using `lat_R hD.isOpen hD.isCompact`. Establish `hai : (a : K) * ((a⁻¹ : Kˣ) : K) = 1` using `by simp`. Establish `hia : ((a⁻¹ : Kˣ) : K) * (a : K) = 1` using `by simp`. Use `set Λ₂ : AddSubgroup K := mulLat ((a⁻¹ : Kˣ) : K) Λ with hΛ₂`. Establish `hL2 : IsLat Λ₂` using `Formalism.FourierDecayAlt.P.A6x3.lat_iff.2 (Formalism.FourierDecayAlt.P.A6x3.lat_mulLat a⁻¹ (Formalism.FourierDecayAlt.P.A6x3.lat_iff.1 hΛ))`.

Establish `hmem : ∀ x : K, x ∈ Λ₂ ↔ (a : K) * x ∈ Λ`. Introduce `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, hw, rfl⟩ show (a : K) * (((a⁻¹ : Kˣ) : K) * w) ∈ Λ`. Rewrite using `[← mul_assoc, hai, one_mul]`.

Conclude with `hw`. Introduce `hx`. Conclude with `⟨_, hx, by show ((a⁻¹ : Kˣ) : K) * ((a : K) * x) = x`. Rewrite using `[← mul_assoc, hia, one_mul]⟩`. Establish `h2 : BInv Λ₂ (fun N : ι → K => f ((a : K) • N))`.

Introduce `x l hl`. Use `show f ((a : K) • (x + l)) = f ((a : K) • x)`. Rewrite using `[smul_add]`. Conclude with `h _ _ (fun i => (hmem _).1 (hl i))`. Rewrite using `[bx_indep hD hΛ' hL2 _ h' h2]`.

Establish `hsum : ∑ᶠ y : ι → K ⧸ Λ₂, f ((a : K) • fun i => (Quotient.out (y i) : K)) = ∑ᶠ y : ι → K ⧸ Λ, f (fun i => Quotient.out (y i))`. Use `tk_reindex (X := ι → K) (fun x i => ((x i : K) : K ⧸ Λ₂)) (fun x i => (((a : K) * x i : K) : K ⧸ Λ)) (fun q i => (Quotient.out (q i) : K)) (fun q i => ((a⁻¹ : Kˣ) : K) * (Quotient.out (q i) : K)) (fun q => funext fun i => QuotientAddGroup.out_eq' _) (fun q => funext fun i => by s …` as an intermediate fact. Rewrite using `[← mul_assoc, hai, one_mul]`. Conclude with `QuotientAddGroup.out_eq' _)`. Use the proof step `(fun x x' => by`.

Prove the components needed by the constructor for the conclusion. Introduce `e`. Use function extensionality and compare the values at `i`. Use `(tk_mk_eq Λ₂ _ _).1 (congrFun e i)` as an intermediate fact. Use `(tk_mk_eq Λ _ _).2 ?_` and prove the remaining obligations.

Rewrite using `[← mul_sub]`. Conclude with `(hmem _).1 this`. Introduce `e`. Use function extensionality and compare the values at `i`. Use `(tk_mk_eq Λ _ _).1 (congrFun e i)` as an intermediate fact.

Use `(tk_mk_eq Λ₂ _ _).2 ((hmem _).2 ?_)` and prove the remaining obligations. Rewrite using `[mul_sub]`. Conclude with `this)`. Use the proof step `(fun x => f ((a : K) • x))`. Use the proof step `(fun x x' e => by`.

Use `h2 x' (x - x') (fun i => (tk_mk_eq Λ₂ _ _).1 (congrFun e i))` as an intermediate fact. Simplify using `using this)`. Rewrite using `[this]`. Use `finsum_congr fun q => ?_` and prove the remaining obligations. Use `congr 1`.

Use function extensionality and compare the values at `i`. Use `show (a : K) * (((a⁻¹ : Kˣ) : K) * (Quotient.out (q i) : K)) = _`. Rewrite using `[← mul_assoc, hai, one_mul]`. Unfold `bx`. Rewrite using `[hsum, hΛ₂, Formalism.FourierDecayAlt.P.A6x3.volL_mulLat hR a⁻¹ (Formalism.FourierDecayAlt.P.A6x3.lat_iff.1 hΛ)]`.

Establish `hm : modK R (a : K) * modK R ((a⁻¹ : Kˣ) : K) = 1`. Rewrite using `[← modK_mul hD.isOpen hD.isCompact a a⁻¹, hai, modK_one]`. Establish `hm' : (modK R (a : K) : ℂ) * (modK R ((a⁻¹ : Kˣ) : K) : ℂ) = 1` using `by exact_mod_cast hm`. Use `push_cast`. Rewrite using `[← mul_assoc, ← mul_pow, ← mul_assoc, hm', one_mul]`.
-/
theorem bx_scale (hD : LocalDatum K R ψ) {ι : Type} [Fintype ι] (a : Kˣ) {Λ Λ' : AddSubgroup K}
    (hΛ : IsLat Λ) (hΛ' : IsLat Λ') (f : (ι → K) → ℂ) (h : BInv Λ f)
    (h' : BInv Λ' (fun N => f ((a : K) • N))) :
    (modK R (a : K) : ℂ) ^ Fintype.card ι * bx R Λ' ι (fun N => f ((a : K) • N)) = bx R Λ ι f := by
  have hR := lat_R hD.isOpen hD.isCompact
  have hai : (a : K) * ((a⁻¹ : Kˣ) : K) = 1 := by simp
  have hia : ((a⁻¹ : Kˣ) : K) * (a : K) = 1 := by simp
  set Λ₂ : AddSubgroup K := mulLat ((a⁻¹ : Kˣ) : K) Λ with hΛ₂
  have hL2 : IsLat Λ₂ :=
    Formalism.FourierDecayAlt.P.A6x3.lat_iff.2 (Formalism.FourierDecayAlt.P.A6x3.lat_mulLat a⁻¹ (Formalism.FourierDecayAlt.P.A6x3.lat_iff.1 hΛ))
  have hmem : ∀ x : K, x ∈ Λ₂ ↔ (a : K) * x ∈ Λ := by
    intro x
    constructor
    · rintro ⟨w, hw, rfl⟩
      show (a : K) * (((a⁻¹ : Kˣ) : K) * w) ∈ Λ
      rw [← mul_assoc, hai, one_mul]; exact hw
    · intro hx
      exact ⟨_, hx, by
        show ((a⁻¹ : Kˣ) : K) * ((a : K) * x) = x
        rw [← mul_assoc, hia, one_mul]⟩
  have h2 : BInv Λ₂ (fun N : ι → K => f ((a : K) • N)) := by
    intro x l hl
    show f ((a : K) • (x + l)) = f ((a : K) • x)
    rw [smul_add]
    exact h _ _ (fun i => (hmem _).1 (hl i))
  rw [bx_indep hD hΛ' hL2 _ h' h2]
  have hsum : ∑ᶠ y : ι → K ⧸ Λ₂, f ((a : K) • fun i => (Quotient.out (y i) : K)) =
      ∑ᶠ y : ι → K ⧸ Λ, f (fun i => Quotient.out (y i)) := by
    have := tk_reindex (X := ι → K) (fun x i => ((x i : K) : K ⧸ Λ₂))
      (fun x i => (((a : K) * x i : K) : K ⧸ Λ)) (fun q i => (Quotient.out (q i) : K))
      (fun q i => ((a⁻¹ : Kˣ) : K) * (Quotient.out (q i) : K))
      (fun q => funext fun i => QuotientAddGroup.out_eq' _)
      (fun q => funext fun i => by
        show ((((a : K) * (((a⁻¹ : Kˣ) : K) * (Quotient.out (q i) : K)) : K)) : K ⧸ Λ) = q i
        rw [← mul_assoc, hai, one_mul]; exact QuotientAddGroup.out_eq' _)
      (fun x x' => by
        constructor
        · intro e
          funext i
          have := (tk_mk_eq Λ₂ _ _).1 (congrFun e i)
          refine (tk_mk_eq Λ _ _).2 ?_
          rw [← mul_sub]; exact (hmem _).1 this
        · intro e
          funext i
          have := (tk_mk_eq Λ _ _).1 (congrFun e i)
          refine (tk_mk_eq Λ₂ _ _).2 ((hmem _).2 ?_)
          rw [mul_sub]; exact this)
      (fun x => f ((a : K) • x))
      (fun x x' e => by
        have := h2 x' (x - x') (fun i => (tk_mk_eq Λ₂ _ _).1 (congrFun e i))
        simpa using this)
    rw [this]
    refine finsum_congr fun q => ?_
    congr 1
    funext i
    show (a : K) * (((a⁻¹ : Kˣ) : K) * (Quotient.out (q i) : K)) = _
    rw [← mul_assoc, hai, one_mul]
  unfold bx
  rw [hsum, hΛ₂, Formalism.FourierDecayAlt.P.A6x3.volL_mulLat hR a⁻¹ (Formalism.FourierDecayAlt.P.A6x3.lat_iff.1 hΛ)]
  have hm : modK R (a : K) * modK R ((a⁻¹ : Kˣ) : K) = 1 := by
    rw [← modK_mul hD.isOpen hD.isCompact a a⁻¹, hai, modK_one]
  have hm' : (modK R (a : K) : ℂ) * (modK R ((a⁻¹ : Kˣ) : K) : ℂ) = 1 := by exact_mod_cast hm
  push_cast
  rw [← mul_assoc, ← mul_pow, ← mul_assoc, hm', one_mul]

end TK

section TKG

variable {V : Type} [AddCommGroup V]

/- English proof (translation)
Take `⟨h, hh⟩` from `QuotientAddGroup.mk_out_eq_add M x`. Rewrite using `[hh]`. Simplify using the standard rewrite rules.
-/
theorem tk_out_subG (M : AddSubgroup V) (x : V) : (Quotient.out (x : V ⧸ M) : V) - x ∈ M := by
  obtain ⟨h, hh⟩ := QuotientAddGroup.mk_out_eq_add M x
  rw [hh]; simp

/- English proof (translation)
Rewrite using `[QuotientAddGroup.eq]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `M.neg_mem h` as an intermediate fact. Simplify `this` using `[sub_eq_add_neg, add_comm]`.

Introduce `h`. Use `M.neg_mem h` as an intermediate fact. Simplify `this` using `[sub_eq_add_neg, add_comm]`.
-/
theorem tk_mk_eqG (M : AddSubgroup V) (x y : V) : ((x : V ⧸ M) = (y : V ⧸ M)) ↔ x - y ∈ M := by
  rw [QuotientAddGroup.eq]
  constructor
  · intro h
    have := M.neg_mem h
    simpa [sub_eq_add_neg, add_comm] using this
  · intro h
    have := M.neg_mem h
    simpa [sub_eq_add_neg, add_comm] using this

/- English proof (translation)
Establish `h1 : (AddSubgroup.quotientEquivProdOfLE h y).1 = ((Quotient.out y : V) : V ⧸ M)` using `by conv_lhs => rw [← QuotientAddGroup.out_eq' y]`. Both sides reduce to the same expression. Rewrite using `[h1]`. Conclude with `tk_out_subG M _`.
-/
theorem tk_out_sub_mem {M' M : AddSubgroup V} (h : M' ≤ M) (y : V ⧸ M') :
    (Quotient.out (AddSubgroup.quotientEquivProdOfLE h y).1 : V) - (Quotient.out y : V) ∈ M := by
  have h1 : (AddSubgroup.quotientEquivProdOfLE h y).1 = ((Quotient.out y : V) : V ⧸ M) := by
    conv_lhs => rw [← QuotientAddGroup.out_eq' y]
    rfl
  rw [h1]
  exact tk_out_subG M _

def tk_S (V₀ M : AddSubgroup V) (f : V → ℂ) : ℂ :=
  (gi M V₀ : ℂ) * ∑ᶠ y : V ⧸ M, f (Quotient.out y)

open Classical in
/- English proof (translation)
Rewrite using `[finsum_eq_single _ ((c : V) : V ⧸ N)]`. Rewrite using `[if_pos (tk_out_subG N c)]`. Introduce `y hy`. Rewrite using `[if_neg]`. Introduce `h`.

Apply `hy` to reduce the goal to its premises. Use `(tk_mk_eqG N _ _).2 h` as an intermediate fact. Rewrite `this` using `[QuotientAddGroup.out_eq']`. Then use the resulting hypothesis.
-/
theorem tk_ind_sum (N : AddSubgroup V) (c : V) :
    ∑ᶠ y : V ⧸ N, (if (Quotient.out y : V) - c ∈ N then (1 : ℂ) else 0) = 1 := by
  rw [finsum_eq_single _ ((c : V) : V ⧸ N)]
  · rw [if_pos (tk_out_subG N c)]
  · intro y hy
    rw [if_neg]
    intro h
    apply hy
    have := (tk_mk_eqG N _ _).2 h
    rwa [QuotientAddGroup.out_eq'] at this

variable [TopologicalSpace V] [IsTopologicalAddGroup V]

/- English proof (translation)
Assemble the required witnesses or components as `⟨hM.op.inter hN.op, hM.cp.inter_right (AddSubgroup.isClosed_of_isOpen N hN.op)⟩`.
-/
theorem tk_lat_infG {M N : AddSubgroup V} (hM : Lat M) (hN : Lat N) : Lat (M ⊓ N) :=
  ⟨hM.op.inter hN.op, hM.cp.inter_right (AddSubgroup.isClosed_of_isOpen N hN.op)⟩

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => simpa using hM`. Consider the case `insert q S _ ih`. Rewrite using `[Finset.inf_insert, ← inf_assoc, inf_comm M, inf_assoc]`. Conclude with `tk_lat_infG (hN q) ih`.
-/
theorem tk_lat_finset_inf {Q : Type} {M : AddSubgroup V} (hM : Lat M) (N : Q → AddSubgroup V)
    (hN : ∀ q, Lat (N q)) (S : Finset Q) : Lat (M ⊓ S.inf N) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using hM
  | insert q S _ ih =>
    rw [Finset.inf_insert, ← inf_assoc, inf_comm M, inf_assoc]
    exact tk_lat_infG (hN q) ih

/- English proof (translation)
Establish `hne : M'.relIndex M ≠ 0` using `relIndex_ne_zero hM'.op hM.cp`. Establish `: Finite (M ⧸ M'.addSubgroupOf M)` using `Nat.finite_of_card_ne_zero hne`. Establish `key : ∑ᶠ y : V ⧸ M', f (Quotient.out y) = (M'.relIndex M : ℂ) * ∑ᶠ y : V ⧸ M, f (Quotient.out y)`. Rewrite using `[← show Nat.card (M ⧸ M'.addSubgroupOf M) = M'.relIndex M from rfl, ← Formalism.FourierDecayAlt.P.A6x3.finsum_fst (AddSubgroup.quotientEquivProdOfLE hle) (fun y : V ⧸ M => f (Quotient.out y))]`. Use `finsum_congr fun y => ?_` and prove the remaining obligations.

Use `hf (Quotient.out y) _ (tk_out_sub_mem hle y)` as an intermediate fact. Rewrite using `[← this]`. Use `congr 1`. Normalize the expressions using the abelian group laws. Establish `hg : gi M V₀ = (M'.relIndex M : ℝ) * gi M' V₀`.

Rewrite using `[← gi_trans hM hM' h0]`. Use `congr 1`. Rewrite using `[gi, AddSubgroup.relIndex_eq_one.2 hle]`. Simplify using the standard rewrite rules. Unfold `tk_S`.

Rewrite using `[key, hg]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem tk_S_refine {V₀ M M' : AddSubgroup V} (h0 : Lat V₀) (hM : Lat M) (hM' : Lat M')
    (hle : M' ≤ M) (f : V → ℂ) (hf : ∀ v, ∀ l ∈ M, f (v + l) = f v) :
    tk_S V₀ M' f = tk_S V₀ M f := by
  have hne : M'.relIndex M ≠ 0 := relIndex_ne_zero hM'.op hM.cp
  have : Finite (M ⧸ M'.addSubgroupOf M) := Nat.finite_of_card_ne_zero hne
  have key : ∑ᶠ y : V ⧸ M', f (Quotient.out y) =
      (M'.relIndex M : ℂ) * ∑ᶠ y : V ⧸ M, f (Quotient.out y) := by
    rw [← show Nat.card (M ⧸ M'.addSubgroupOf M) = M'.relIndex M from rfl,
      ← Formalism.FourierDecayAlt.P.A6x3.finsum_fst (AddSubgroup.quotientEquivProdOfLE hle)
        (fun y : V ⧸ M => f (Quotient.out y))]
    refine finsum_congr fun y => ?_
    have := hf (Quotient.out y) _ (tk_out_sub_mem hle y)
    rw [← this]
    congr 1
    abel
  have hg : gi M V₀ = (M'.relIndex M : ℝ) * gi M' V₀ := by
    rw [← gi_trans hM hM' h0]
    congr 1
    rw [gi, AddSubgroup.relIndex_eq_one.2 hle]
    simp
  unfold tk_S
  rw [key, hg]
  push_cast
  ring

open Classical in
/- English proof (translation)
Rewrite using `[tk_S_refine h0 hN hM' hle]`. Unfold `tk_S`. Rewrite using `[tk_ind_sum, mul_one]`. Introduce `v l hl`. Establish `: v + l - c ∈ N ↔ v - c ∈ N`.

Establish `e : v + l - c = (v - c) + l` using `by abel`. Rewrite using `[e]`. Conclude with `N.add_mem_cancel_right hl`. Simplify using `only [this]`.
-/
theorem tk_S_ind {V₀ N M' : AddSubgroup V} (h0 : Lat V₀) (hN : Lat N) (hM' : Lat M')
    (hle : M' ≤ N) (c : V) :
    tk_S V₀ M' (fun v => if v - c ∈ N then (1 : ℂ) else 0) = (gi N V₀ : ℂ) := by
  rw [tk_S_refine h0 hN hM' hle]
  · unfold tk_S
    rw [tk_ind_sum, mul_one]
  · intro v l hl
    have : v + l - c ∈ N ↔ v - c ∈ N := by
      have e : v + l - c = (v - c) + l := by abel
      rw [e]
      exact N.add_mem_cancel_right hl
    simp only [this]

open Classical in
/- English proof (translation)
Assume the negation of the conclusion as `hinf`. Establish `h1` using `tk_S_ind h0 hN hM' hle c`. Unfold `tk_S at h1`. Rewrite `h1` using `[finsum_of_infinite_support hinf, mul_zero]`. Use `gi_pos hN h0` as an intermediate fact.

Establish `h2 : (gi N V₀ : ℂ) ≠ 0` using `by exact_mod_cast this.ne'`. Conclude with `h2 h1.symm`.
-/
theorem tk_ind_fin {V₀ N M' : AddSubgroup V} (h0 : Lat V₀) (hN : Lat N) (hM' : Lat M')
    (hle : M' ≤ N) (c : V) :
    (Function.support fun y : V ⧸ M' =>
      (if (Quotient.out y : V) - c ∈ N then (1 : ℂ) else 0)).Finite := by
  by_contra hinf
  have h1 := tk_S_ind h0 hN hM' hle c
  unfold tk_S at h1
  rw [finsum_of_infinite_support hinf, mul_zero] at h1
  have := gi_pos hN h0
  have h2 : (gi N V₀ : ℂ) ≠ 0 := by exact_mod_cast this.ne'
  exact h2 h1.symm

/- English proof (translation)
Use `set S := hfin.toFinset with hS`. Establish `hM' : Lat (M ⊓ S.inf N)` using `tk_lat_finset_inf hM N hN S`. Establish `hle : ∀ q ∈ S, M ⊓ S.inf N ≤ N q` using `fun q hq => inf_le_right.trans (Finset.inf_le hq)`. Establish `hdec : ∀ v, f v = ∑ q ∈ S, f (c q) * (if v - c q ∈ N q then (1 : ℂ) else 0)`. Introduce `v`.

Take `⟨q₀, hq₀, huniq⟩` from `hpart v`. Establish `hv : f v = f (c q₀)`. Use `hf q₀ _ hq₀` as an intermediate fact. Rewrite `this` using `[add_sub_cancel]`. Then use the resulting hypothesis. Establish `hterm : ∀ q ∈ S, f (c q) * (if v - c q ∈ N q then (1 : ℂ) else 0) = if q = q₀ then f (c q₀) else 0`.

Introduce `q _`. Distinguish the cases in `hq : q = q₀`. Substitute `hq` using the available equality. Simplify using `[hq₀]`. Rewrite using `[if_neg hq, if_neg (fun h => hq (huniq q h)), mul_zero]`.

Rewrite using `[Finset.sum_congr rfl hterm, Finset.sum_ite_eq', hv]`. Distinguish the cases in `hq : q₀ ∈ S`. Rewrite using `[if_pos hq]`. Rewrite using `[if_neg hq]`. Assume the negation of the conclusion as `hne`.

Conclude with `hq (by rw [hS, Set.Finite.mem_toFinset]; exact hne)`. Rewrite using `[← tk_S_refine h0 hM hM' inf_le_left f hinv]`. Establish `h1 : ∑ᶠ y : V ⧸ (M ⊓ S.inf N), f (Quotient.out y) = ∑ q ∈ S, f (c q) * ∑ᶠ y : V ⧸ (M ⊓ S.inf N), (if (Quotient.out y : V) - c q ∈ N q then (1 : ℂ) else 0)`. Establish `hy : ∀ y : V ⧸ (M ⊓ S.inf N), f (Quotient.out y) = ∑ q ∈ S, f (c q) * (if (Quotient.out y : V) - c q ∈ N q then (1 : ℂ) else 0)` using `fun y => hdec _`. Rewrite using `[finsum_congr hy, finsum_sum_comm]`.

Conclude with `Finset.sum_congr rfl fun q _ => (mul_finsum _ _).symm`. Introduce `q hq`. Use `(tk_ind_fin h0 (hN q) hM' (hle q hq) (c q)).subset ?_` and prove the remaining obligations. Introduce `y hy`. Simplify using `only [Function.mem_support] at hy ⊢`.

Conclude with `right_ne_zero_of_mul hy`. Unfold `tk_S`. Rewrite using `[h1, Finset.mul_sum, finsum_eq_sum_of_support_subset (s := S)]`. Use `Finset.sum_congr rfl fun q hq => ?_` and prove the remaining obligations. Use `tk_S_ind h0 (hN q) hM' (hle q hq) (c q)` as an intermediate fact.

Unfold `tk_S at this`. Rewrite using `[← this]`. Expand and normalize the polynomial expressions, which then agree. Introduce `q hq`. Simplify using `only [Function.mem_support] at hq`.

Rewrite using `[hS, Set.Finite.coe_toFinset]`. Conclude with `right_ne_zero_of_mul hq`.
-/
theorem tk_cells {V₀ : AddSubgroup V} (h0 : Lat V₀) {Q : Type} (c : Q → V) (N : Q → AddSubgroup V)
    (hN : ∀ q, Lat (N q)) (hpart : ∀ v, ∃! q, v - c q ∈ N q) (f : V → ℂ)
    (hf : ∀ q, ∀ w ∈ N q, f (c q + w) = f (c q)) (hfin : {q | f (c q) ≠ 0}.Finite)
    {M : AddSubgroup V} (hM : Lat M) (hinv : ∀ v, ∀ l ∈ M, f (v + l) = f v) :
    tk_S V₀ M f = ∑ᶠ q, (gi (N q) V₀ : ℂ) * f (c q) := by
  classical
  set S := hfin.toFinset with hS
  have hM' : Lat (M ⊓ S.inf N) := tk_lat_finset_inf hM N hN S
  have hle : ∀ q ∈ S, M ⊓ S.inf N ≤ N q := fun q hq => inf_le_right.trans (Finset.inf_le hq)
  have hdec : ∀ v, f v = ∑ q ∈ S, f (c q) * (if v - c q ∈ N q then (1 : ℂ) else 0) := by
    intro v
    obtain ⟨q₀, hq₀, huniq⟩ := hpart v
    have hv : f v = f (c q₀) := by
      have := hf q₀ _ hq₀
      rwa [add_sub_cancel] at this
    have hterm : ∀ q ∈ S, f (c q) * (if v - c q ∈ N q then (1 : ℂ) else 0) =
        if q = q₀ then f (c q₀) else 0 := by
      intro q _
      by_cases hq : q = q₀
      · subst hq; simp [hq₀]
      · rw [if_neg hq, if_neg (fun h => hq (huniq q h)), mul_zero]
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq', hv]
    by_cases hq : q₀ ∈ S
    · rw [if_pos hq]
    · rw [if_neg hq]
      by_contra hne
      exact hq (by rw [hS, Set.Finite.mem_toFinset]; exact hne)
  rw [← tk_S_refine h0 hM hM' inf_le_left f hinv]
  have h1 : ∑ᶠ y : V ⧸ (M ⊓ S.inf N), f (Quotient.out y) =
      ∑ q ∈ S, f (c q) * ∑ᶠ y : V ⧸ (M ⊓ S.inf N),
        (if (Quotient.out y : V) - c q ∈ N q then (1 : ℂ) else 0) := by
    have hy : ∀ y : V ⧸ (M ⊓ S.inf N), f (Quotient.out y) =
        ∑ q ∈ S, f (c q) * (if (Quotient.out y : V) - c q ∈ N q then (1 : ℂ) else 0) :=
      fun y => hdec _
    rw [finsum_congr hy, finsum_sum_comm]
    · exact Finset.sum_congr rfl fun q _ => (mul_finsum _ _).symm
    · intro q hq
      refine (tk_ind_fin h0 (hN q) hM' (hle q hq) (c q)).subset ?_
      intro y hy
      simp only [Function.mem_support] at hy ⊢
      exact right_ne_zero_of_mul hy
  unfold tk_S
  rw [h1, Finset.mul_sum, finsum_eq_sum_of_support_subset (s := S)]
  · refine Finset.sum_congr rfl fun q hq => ?_
    have := tk_S_ind h0 (hN q) hM' (hle q hq) (c q)
    unfold tk_S at this
    rw [← this]
    ring
  · intro q hq
    simp only [Function.mem_support] at hq
    rw [hS, Set.Finite.coe_toFinset]
    exact right_ne_zero_of_mul hq

end TKG

section TKB

variable {K : Type} [CommRing K]

/- English proof (translation)
Set `φ : (ι → B) →+ (ι → K)` to `AddMonoidHom.compLeft B.subtype ι`. Establish `h1 : (⊤ : AddSubgroup (ι → B)).map φ = AddSubgroup.pi Set.univ (fun _ : ι => B)`. Use extensionality with `v`. Simplify using `only [AddSubgroup.mem_map, AddSubgroup.mem_top, true_and, AddSubgroup.mem_pi, Set.mem_univ, forall_true_left]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨w, rfl⟩ i`. Conclude with `(w i).2`. Introduce `h`. Conclude with `⟨fun i => ⟨v i, h i⟩, rfl⟩`. Establish `h2 : (AddSubgroup.pi Set.univ (fun _ : ι => A)).comap φ = AddSubgroup.pi Set.univ (fun _ : ι => A.addSubgroupOf B)`.

Use extensionality with `v`. Simplify using `only [AddSubgroup.mem_comap, AddSubgroup.mem_pi, Set.mem_univ, forall_true_left, AddSubgroup.mem_addSubgroupOf]`. Both sides reduce to the same expression. Rewrite using `[← h1, ← AddSubgroup.relIndex_comap, AddSubgroup.relIndex_top_right, h2, AddSubgroup.index_pi]`. Simplify using `[AddSubgroup.relIndex]`.
-/
theorem tk_relIndex_pi {ι : Type} [Fintype ι] (A B : AddSubgroup K) :
    (AddSubgroup.pi Set.univ (fun _ : ι => A)).relIndex (AddSubgroup.pi Set.univ (fun _ : ι => B)) =
      (A.relIndex B) ^ Fintype.card ι := by
  let φ : (ι → B) →+ (ι → K) := AddMonoidHom.compLeft B.subtype ι
  have h1 : (⊤ : AddSubgroup (ι → B)).map φ = AddSubgroup.pi Set.univ (fun _ : ι => B) := by
    ext v
    simp only [AddSubgroup.mem_map, AddSubgroup.mem_top, true_and, AddSubgroup.mem_pi, Set.mem_univ,
      forall_true_left]
    constructor
    · rintro ⟨w, rfl⟩ i
      exact (w i).2
    · intro h
      exact ⟨fun i => ⟨v i, h i⟩, rfl⟩
  have h2 : (AddSubgroup.pi Set.univ (fun _ : ι => A)).comap φ =
      AddSubgroup.pi Set.univ (fun _ : ι => A.addSubgroupOf B) := by
    ext v
    simp only [AddSubgroup.mem_comap, AddSubgroup.mem_pi, Set.mem_univ, forall_true_left,
      AddSubgroup.mem_addSubgroupOf]
    rfl
  rw [← h1, ← AddSubgroup.relIndex_comap, AddSubgroup.relIndex_top_right, h2, AddSubgroup.index_pi]
  simp [AddSubgroup.relIndex]

/- English proof (translation)
Unfold `gi LL volL`. Rewrite using `[tk_relIndex_pi, tk_relIndex_pi]`. Use `push_cast`. Rewrite using `[div_pow]`.
-/
theorem tk_gi_pi {ι : Type} [Fintype ι] (R : Subring K) (Λ : AddSubgroup K) :
    gi (AddSubgroup.pi Set.univ (fun _ : ι => Λ)) (LL R ι) = volL R Λ ^ Fintype.card ι := by
  unfold gi LL volL
  rw [tk_relIndex_pi, tk_relIndex_pi]
  push_cast
  rw [div_pow]

/- English proof (translation)
Unfold `bx tk_S`. Rewrite using `[tk_gi_pi]`. Use `push_cast`. Use `congr 1`. Use `tk_reindex (X := ι → K) (fun x i => ((x i : K) : K ⧸ Λ)) (fun x => (x : (ι → K) ⧸ AddSubgroup.pi Set.univ (fun _ : ι => Λ))) (fun q i => (Quotient.out (q i) : K)) (fun q => Quotient.out q) (fun q => funext fun i => QuotientAddGroup.out_eq' _) (fun q => QuotientAddGroup.out_eq' _) …` and prove the remaining obligations.

Rewrite using `[tk_mk_eqG]`. Simplify using `only [AddSubgroup.mem_pi, Set.mem_univ, forall_true_left]`. Prove the components needed by the constructor for the conclusion. Introduce `e i`. Conclude with `(tk_mk_eqG Λ _ _).1 (congrFun e i)`.

Introduce `e`. Use function extensionality and compare the values at `i`. Conclude with `(tk_mk_eqG Λ _ _).2 (e i)`. Use `hf x' (x - x') (fun i => (tk_mk_eqG Λ _ _).1 (congrFun e i))` as an intermediate fact. Simplify using `using this`.
-/
theorem tk_bx_eq_S {ι : Type} [Fintype ι] (R : Subring K) (Λ : AddSubgroup K) (f : (ι → K) → ℂ)
    (hf : BInv Λ f) :
    bx R Λ ι f = tk_S (LL R ι) (AddSubgroup.pi Set.univ (fun _ : ι => Λ)) f := by
  unfold bx tk_S
  rw [tk_gi_pi]
  push_cast
  congr 1
  refine tk_reindex (X := ι → K) (fun x i => ((x i : K) : K ⧸ Λ))
    (fun x => (x : (ι → K) ⧸ AddSubgroup.pi Set.univ (fun _ : ι => Λ)))
    (fun q i => (Quotient.out (q i) : K)) (fun q => Quotient.out q)
    (fun q => funext fun i => QuotientAddGroup.out_eq' _) (fun q => QuotientAddGroup.out_eq' _)
    (fun x x' => ?_) f (fun x x' e => ?_)
  · rw [tk_mk_eqG]
    simp only [AddSubgroup.mem_pi, Set.mem_univ, forall_true_left]
    constructor
    · intro e i
      exact (tk_mk_eqG Λ _ _).1 (congrFun e i)
    · intro e
      funext i
      exact (tk_mk_eqG Λ _ _).2 (e i)
  · have := hf x' (x - x') (fun i => (tk_mk_eqG Λ _ _).1 (congrFun e i))
    simpa using this

variable [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K} {ψ : AddChar K ℂ}

/- English proof (translation)
Establish `e : ((AddSubgroup.pi Set.univ (fun _ : ι => Λ) : AddSubgroup (ι → K)) : Set (ι → K)) = Set.pi Set.univ (fun _ => (Λ : Set K))`. Use extensionality with `v`. Simplify using `[AddSubgroup.mem_pi]`. Prove the components needed by the constructor for the conclusion. Rewrite using `[e]`.

Conclude with `isOpen_set_pi Set.finite_univ (fun _ _ => hΛ.1)`. Rewrite using `[e]`. Conclude with `isCompact_univ_pi (fun _ => hΛ.2)`.
-/
theorem tk_lat_pi {ι : Type} [Fintype ι] {Λ : AddSubgroup K} (hΛ : IsLat Λ) :
    Lat (AddSubgroup.pi Set.univ (fun _ : ι => Λ)) := by
  have e : ((AddSubgroup.pi Set.univ (fun _ : ι => Λ) : AddSubgroup (ι → K)) : Set (ι → K)) =
      Set.pi Set.univ (fun _ => (Λ : Set K)) := by
    ext v; simp [AddSubgroup.mem_pi]
  constructor
  · rw [e]; exact isOpen_set_pi Set.finite_univ (fun _ _ => hΛ.1)
  · rw [e]; exact isCompact_univ_pi (fun _ => hΛ.2)

/- English proof (translation)
Establish `hL : Lat (LL R ι)` using `lat_LL hD.isOpen hD.isCompact`. Establish `hG : Good R ι` using `good_equiv (Fintype.equivFin ι).symm (good_fin hD _)`. Establish `hmem : ∀ q (v : ι → K), v - c q ∈ (LL R ι).map (mv (M q)) ↔ ∃ r : ι → K, (∀ i, r i ∈ R) ∧ v = c q + M q *ᵥ r`. Introduce `q v`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨r, hr, e⟩`. Use `⟨r, mem_LL.1 hr, ?_⟩` and prove the remaining obligations. Rewrite `e` using `[mv_apply]`. Rewrite using `[e]`. Normalize the expressions using the abelian group laws.

Introduce and unpack `⟨r, hr, e⟩`. Use `⟨r, mem_LL.2 hr, ?_⟩` and prove the remaining obligations. Rewrite using `[mv_apply, e]`. Normalize the expressions using the abelian group laws. Rewrite using `[tk_bx_eq_S R Λ f hinv, tk_cells hL c (fun q => (LL R ι).map (mv (M q))) (fun q => lat_map (hM q) hL) ?_ f ?_ hfin (tk_lat_pi hΛ) ?_]`.

Use `finsum_congr fun q => ?_` and prove the remaining obligations. Rewrite using `[← hG (M q) (hM q)]`. Both sides reduce to the same expression. Introduce `v`. Take `⟨q, hq, hu⟩` from `hpart v`.

Conclude with `⟨q, (hmem q v).2 hq, fun q' hq' => hu q' ((hmem q' v).1 hq')⟩`. Introduce and unpack `q _ ⟨r, hr, rfl⟩`. Conclude with `hf q r (mem_LL.1 hr)`. Introduce `v l hl`. Conclude with `hinv v l (fun i => by`.

Use `(AddSubgroup.mem_pi _).1 hl i (Set.mem_univ i)` as an intermediate fact. Conclude with `this)`.
-/
theorem bx_cells (hD : LocalDatum K R ψ) {ι : Type} [Fintype ι] [DecidableEq ι] {Q : Type}
    (c : Q → ι → K) (M : Q → Matrix ι ι K) (hM : ∀ q, IsUnit (M q).det)
    (hpart : ∀ v : ι → K, ∃! q, ∃ r : ι → K, (∀ i, r i ∈ R) ∧ v = c q + M q *ᵥ r)
    (f : (ι → K) → ℂ) (hf : ∀ q (r : ι → K), (∀ i, r i ∈ R) → f (c q + M q *ᵥ r) = f (c q))
    (hfin : {q | f (c q) ≠ 0}.Finite) {Λ : AddSubgroup K} (hΛ : IsLat Λ) (hinv : BInv Λ f) :
    bx R Λ ι f = ∑ᶠ q, (modK R (M q).det : ℂ) * f (c q) := by
  have hL : Lat (LL R ι) := lat_LL hD.isOpen hD.isCompact
  have hG : Good R ι := good_equiv (Fintype.equivFin ι).symm (good_fin hD _)
  have hmem : ∀ q (v : ι → K), v - c q ∈ (LL R ι).map (mv (M q)) ↔
      ∃ r : ι → K, (∀ i, r i ∈ R) ∧ v = c q + M q *ᵥ r := by
    intro q v
    constructor
    · rintro ⟨r, hr, e⟩
      refine ⟨r, mem_LL.1 hr, ?_⟩
      rw [mv_apply] at e
      rw [e]; abel
    · rintro ⟨r, hr, e⟩
      refine ⟨r, mem_LL.2 hr, ?_⟩
      rw [mv_apply, e]; abel
  rw [tk_bx_eq_S R Λ f hinv, tk_cells hL c (fun q => (LL R ι).map (mv (M q)))
    (fun q => lat_map (hM q) hL) ?_ f ?_ hfin (tk_lat_pi hΛ) ?_]
  · refine finsum_congr fun q => ?_
    rw [← hG (M q) (hM q)]
    rfl
  · intro v
    obtain ⟨q, hq, hu⟩ := hpart v
    exact ⟨q, (hmem q v).2 hq, fun q' hq' => hu q' ((hmem q' v).1 hq')⟩
  · rintro q _ ⟨r, hr, rfl⟩
    exact hf q r (mem_LL.1 hr)
  · intro v l hl
    exact hinv v l (fun i => by
      have := (AddSubgroup.mem_pi _).1 hl i (Set.mem_univ i)
      exact this)

/- English proof (translation)
Establish `hmk : ∀ z : KR R, (Submodule.Quotient.mk (Quotient.out z : K) : KR R) = z` using `fun z => Quotient.out_eq z`. Establish `hMi : ∀ w : ι → K, M⁻¹ *ᵥ (M *ᵥ w) = w`. Introduce `w`. Rewrite using `[mulVec_mulVec, nonsing_inv_mul _ hM, one_mulVec]`. Establish `hiM : ∀ w : ι → K, M *ᵥ (M⁻¹ *ᵥ w) = w`.

Introduce `w`. Rewrite using `[mulVec_mulVec, mul_nonsing_inv _ hM, one_mulVec]`. Rewrite using `[bx_cells hD (fun q : ι → KR R => M *ᵥ (fun i => (Quotient.out (q i) : K)) + b) (fun _ => M) (fun _ => hM) ?_ f ?_ ?_ hΛ hinv, mul_finsum]`. Introduce `v`. Use `⟨fun i => Submodule.Quotient.mk ((M⁻¹ *ᵥ (v - b)) i), ⟨fun i => (M⁻¹ *ᵥ (v - b)) i - (Quotient.out (Submodule.Quotient.mk ((M⁻¹ *ᵥ (v - b)) i) : KR R) : K), ?_, ?_⟩, ?_⟩` and prove the remaining obligations.

Introduce `i`. Conclude with `(Formalism.FourierDecayAlt.P.A5x3.mk_eq_mk R _ _).1 (hmk _).symm`. Establish `key : ∀ w o : ι → K, w = M⁻¹ *ᵥ (v - b) → v = M *ᵥ o + b + M *ᵥ (fun i => w i - o i)`. Introduce `w o hw`. Establish `e : o + (fun i => w i - o i) = w` using `by funext i; simp`.

Combine the equalities or inequalities in the displayed calculation. Conclude with `key _ _ rfl`. Introduce and unpack `q ⟨r, hr, e⟩`. Use function extensionality and compare the values at `i`. Establish `e3 : M⁻¹ *ᵥ (v - b) = (fun i => (Quotient.out (q i) : K)) + r`.

Rewrite using `[e]`. Establish `: M *ᵥ (fun i => (Quotient.out (q i) : K)) + b + M *ᵥ r - b = M *ᵥ ((fun i => (Quotient.out (q i) : K)) + r)`. Rewrite using `[mulVec_add]`. Normalize the expressions using the abelian group laws. Rewrite using `[this, hMi]`.

Rewrite using `[e3, ← hmk (q i)]`. Use `(Formalism.FourierDecayAlt.P.A5x3.mk_eq_mk R _ _).2 ?_` and prove the remaining obligations. Simplify using `using R.neg_mem (hr i)`. Introduce `q r hr`. Use `hR (fun i => (Quotient.out (q i) : K)) r hr` as an intermediate fact.

Rewrite using `[← this, mulVec_add]`. Use `congr 1`. Normalize the expressions using the abelian group laws. Establish `hB : IsCompact (Set.pi Set.univ (fun _ : ι => (L : Set K)))` using `isCompact_univ_pi (fun _ => hL.2)`. Establish `hT : Continuous fun x : ι → K => M⁻¹ *ᵥ (x - b)` using `Continuous.matrix_mulVec continuous_const (continuous_id.sub continuous_const)`.

Establish `hC : ∀ i, IsCompact ((fun x : ι → K => x i) '' ((fun x : ι → K => M⁻¹ *ᵥ (x - b)) '' Set.pi Set.univ (fun _ : ι => (L : Set K))))` using `fun i => (hB.image hT).image (continuous_apply i)`. Establish `h1 : ∀ i, {z : KR R | (Quotient.out z : K) ∈ (fun x : ι → K => x i) '' ((fun x : ι → K => M⁻¹ *ᵥ (x - b)) '' Set.pi Set.univ (fun _ : ι => (L : Set K)))}.Finite` using `fun i => tk_fin_cpt R.toAddSubgroup hD.isOpen (fun z : KR R => (Quotient.out z : K)) (fun q q' h => by`. Use `(Formalism.FourierDecayAlt.P.A5x3.mk_eq_mk R _ _).2 h` as an intermediate fact. Rewrite using `[hmk, hmk] at this)` and apply the resulting hypothesis. Use the proof step `(fun y => ⟨Submodule.Quotient.mk y, (Formalism.FourierDecayAlt.P.A5x3.mk_eq_mk R _ _).1 (hmk _).symm⟩) (hC i)`.

Use `(Set.Finite.pi' h1).subset ?_` and prove the remaining obligations. Introduce `q hq i`. Use `⟨M⁻¹ *ᵥ (M *ᵥ (fun i => (Quotient.out (q i) : K)) + b - b), ⟨M *ᵥ (fun i => (Quotient.out (q i) : K)) + b, Set.mem_univ_pi.2 (hs _ hq), rfl⟩, ?_⟩` and prove the remaining obligations. Use `show (M⁻¹ *ᵥ (M *ᵥ (fun i => (Quotient.out (q i) : K)) + b - b)) i = _`. Rewrite using `[add_sub_cancel_right, hMi]`.
-/
theorem bx_lin (hD : LocalDatum K R ψ) {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι K)
    (hM : IsUnit M.det) (b : ι → K) {Λ L : AddSubgroup K} (hΛ : IsLat Λ) (hL : IsLat L)
    (f : (ι → K) → ℂ) (hinv : BInv Λ f) (hs : BSupp L f)
    (hR : ∀ ξ r : ι → K, (∀ i, r i ∈ R) → f (M *ᵥ (ξ + r) + b) = f (M *ᵥ ξ + b)) :
    bx R Λ ι f = (modK R M.det : ℂ) *
      ∑ᶠ q : ι → KR R, f (M *ᵥ (fun i => Quotient.out (q i)) + b) := by
  have hmk : ∀ z : KR R, (Submodule.Quotient.mk (Quotient.out z : K) : KR R) = z :=
    fun z => Quotient.out_eq z
  have hMi : ∀ w : ι → K, M⁻¹ *ᵥ (M *ᵥ w) = w := by
    intro w; rw [mulVec_mulVec, nonsing_inv_mul _ hM, one_mulVec]
  have hiM : ∀ w : ι → K, M *ᵥ (M⁻¹ *ᵥ w) = w := by
    intro w; rw [mulVec_mulVec, mul_nonsing_inv _ hM, one_mulVec]
  rw [bx_cells hD (fun q : ι → KR R => M *ᵥ (fun i => (Quotient.out (q i) : K)) + b) (fun _ => M)
    (fun _ => hM) ?_ f ?_ ?_ hΛ hinv, mul_finsum]
  · intro v
    refine ⟨fun i => Submodule.Quotient.mk ((M⁻¹ *ᵥ (v - b)) i), ⟨fun i => (M⁻¹ *ᵥ (v - b)) i -
      (Quotient.out (Submodule.Quotient.mk ((M⁻¹ *ᵥ (v - b)) i) : KR R) : K), ?_, ?_⟩, ?_⟩
    · intro i
      exact (Formalism.FourierDecayAlt.P.A5x3.mk_eq_mk R _ _).1 (hmk _).symm
    · have key : ∀ w o : ι → K, w = M⁻¹ *ᵥ (v - b) →
          v = M *ᵥ o + b + M *ᵥ (fun i => w i - o i) := by
        intro w o hw
        have e : o + (fun i => w i - o i) = w := by funext i; simp
        calc v = M *ᵥ w + b := by rw [hw, hiM]; abel
          _ = M *ᵥ (o + fun i => w i - o i) + b := by rw [e]
          _ = M *ᵥ o + b + M *ᵥ (fun i => w i - o i) := by rw [mulVec_add]; abel
      exact key _ _ rfl
    · rintro q ⟨r, hr, e⟩
      funext i
      have e3 : M⁻¹ *ᵥ (v - b) = (fun i => (Quotient.out (q i) : K)) + r := by
        rw [e]
        have : M *ᵥ (fun i => (Quotient.out (q i) : K)) + b + M *ᵥ r - b =
            M *ᵥ ((fun i => (Quotient.out (q i) : K)) + r) := by
          rw [mulVec_add]; abel
        rw [this, hMi]
      rw [e3, ← hmk (q i)]
      refine (Formalism.FourierDecayAlt.P.A5x3.mk_eq_mk R _ _).2 ?_
      simpa using R.neg_mem (hr i)
  · intro q r hr
    have := hR (fun i => (Quotient.out (q i) : K)) r hr
    rw [← this, mulVec_add]
    congr 1
    abel
  · have hB : IsCompact (Set.pi Set.univ (fun _ : ι => (L : Set K))) :=
      isCompact_univ_pi (fun _ => hL.2)
    have hT : Continuous fun x : ι → K => M⁻¹ *ᵥ (x - b) :=
      Continuous.matrix_mulVec continuous_const (continuous_id.sub continuous_const)
    have hC : ∀ i, IsCompact ((fun x : ι → K => x i) ''
        ((fun x : ι → K => M⁻¹ *ᵥ (x - b)) '' Set.pi Set.univ (fun _ : ι => (L : Set K)))) :=
      fun i => (hB.image hT).image (continuous_apply i)
    have h1 : ∀ i, {z : KR R | (Quotient.out z : K) ∈ (fun x : ι → K => x i) ''
        ((fun x : ι → K => M⁻¹ *ᵥ (x - b)) '' Set.pi Set.univ (fun _ : ι => (L : Set K)))}.Finite :=
      fun i => tk_fin_cpt R.toAddSubgroup hD.isOpen (fun z : KR R => (Quotient.out z : K))
        (fun q q' h => by
          have := (Formalism.FourierDecayAlt.P.A5x3.mk_eq_mk R _ _).2 h
          rwa [hmk, hmk] at this)
        (fun y => ⟨Submodule.Quotient.mk y, (Formalism.FourierDecayAlt.P.A5x3.mk_eq_mk R _ _).1 (hmk _).symm⟩) (hC i)
    refine (Set.Finite.pi' h1).subset ?_
    intro q hq i
    refine ⟨M⁻¹ *ᵥ (M *ᵥ (fun i => (Quotient.out (q i) : K)) + b - b),
      ⟨M *ᵥ (fun i => (Quotient.out (q i) : K)) + b, Set.mem_univ_pi.2 (hs _ hq), rfl⟩, ?_⟩
    show (M⁻¹ *ᵥ (M *ᵥ (fun i => (Quotient.out (q i) : K)) + b - b)) i = _
    rw [add_sub_cancel_right, hMi]

end TKB

section LU

section LUalg

variable {K : Type} [CommRing K]

def lu_co {n : ℕ} (u : Matrix (Fin n) (Fin n) K) : Pr n → K := fun p => u p.1.1 p.1.2

def lu_M {n : ℕ} (u : Matrix (Fin n) (Fin n) K) : Matrix (Pr n) (Pr n) K :=
  fun p p' => if p'.1.2 = p.1.2 then u p.1.1 p'.1.1 else 0

/- English proof (translation)
Simplify using `[EE, h]`.
-/
theorem lu_EE_lt {n : ℕ} (y : Pr n → K) {i j : Fin n} (h : i < j) : EE y i j = y ⟨(i, j), h⟩ := by
  simp [EE, h]

/- English proof (translation)
Simplify using `[EE, h]`.
-/
theorem lu_EE_not_lt {n : ℕ} (y : Pr n → K) {i j : Fin n} (h : ¬ i < j) : EE y i j = 0 := by
  simp [EE, h]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `i j hij`. Establish `hij' : j < i` using `hij`. Rewrite using `[Matrix.add_apply, Matrix.one_apply_ne (ne_of_gt hij'), lu_EE_not_lt y (not_lt.2 hij'.le), add_zero]`. Introduce `i`.

Rewrite using `[Matrix.add_apply, Matrix.one_apply_eq, lu_EE_not_lt y (lt_irrefl i), add_zero]`.
-/
theorem lu_up {n : ℕ} (y : Pr n → K) : IsUpUni (1 + EE y) := by
  constructor
  · intro i j hij
    have hij' : j < i := hij
    rw [Matrix.add_apply, Matrix.one_apply_ne (ne_of_gt hij'), lu_EE_not_lt y (not_lt.2 hij'.le),
      add_zero]
  · intro i
    rw [Matrix.add_apply, Matrix.one_apply_eq, lu_EE_not_lt y (lt_irrefl i), add_zero]

/- English proof (translation)
Use function extensionality and compare the values at `p`. Take `⟨⟨i, j⟩, h⟩` from `p`. Establish `h' : i < j` using `h`. Use `show (1 + EE y) i j = _`. Rewrite using `[Matrix.add_apply, Matrix.one_apply_ne (ne_of_lt h'), lu_EE_lt y h', zero_add]`.
-/
theorem lu_co_EE {n : ℕ} (y : Pr n → K) : lu_co (1 + EE y) = y := by
  funext p
  obtain ⟨⟨i, j⟩, h⟩ := p
  have h' : i < j := h
  show (1 + EE y) i j = _
  rw [Matrix.add_apply, Matrix.one_apply_ne (ne_of_lt h'), lu_EE_lt y h', zero_add]

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.add_apply]`. Break down `lt_trichotomy i j with h | h | h` into its components or cases. Rewrite using `[Matrix.one_apply_ne (ne_of_lt h), lu_EE_lt _ h, zero_add]`. Both sides reduce to the same expression.

Substitute `h` using the available equality. Rewrite using `[Matrix.one_apply_eq, lu_EE_not_lt _ (lt_irrefl i), add_zero, hu.2 i]`. Rewrite using `[Matrix.one_apply_ne (ne_of_gt h), lu_EE_not_lt _ (not_lt.2 h.le), add_zero]`. Conclude with `(hu.1 h).symm`.
-/
theorem lu_eq {n : ℕ} {u : Matrix (Fin n) (Fin n) K} (hu : IsUpUni u) : 1 + EE (lu_co u) = u := by
  ext i j
  rw [Matrix.add_apply]
  rcases lt_trichotomy i j with h | h | h
  · rw [Matrix.one_apply_ne (ne_of_lt h), lu_EE_lt _ h, zero_add]; rfl
  · subst h
    rw [Matrix.one_apply_eq, lu_EE_not_lt _ (lt_irrefl i), add_zero, hu.2 i]
  · rw [Matrix.one_apply_ne (ne_of_gt h), lu_EE_not_lt _ (not_lt.2 h.le), add_zero]
    exact (hu.1 h).symm

/- English proof (translation)
Set `G : Fin n × Fin n → K` to `fun q => if h : q.1 < q.2 then (if q.2 = j then g ⟨q, h⟩ else 0) else 0`. Establish `e0 : ∑ p : Pr n, (if p.1.2 = j then g p else 0) = ∑ p : Pr n, G p.1`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Establish `hp : p.1.1 < p.1.2` using `p.2`. Simplify using `only [G, hp, dite_true]`.

Establish `e1 : ∑ p : Pr n, G p.1 = ∑ q : Fin n × Fin n, G q`. Rewrite using `[← Finset.sum_subtype (Finset.univ.filter fun q : Fin n × Fin n => q.1 < q.2) (p := fun q : Fin n × Fin n => q.1 < q.2) (by simp) G, Finset.sum_filter]`. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Distinguish the cases in `h : q.1 < q.2`. Simplify using `[h]`.

Simplify using `[G, h]`. Rewrite using `[e0, e1, Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single j]`. Simplify using `[G]`.

Introduce `l _ hl`. Simplify using `only [G]`. Apply the tactic sequence `split_ifs <;> rfl`. Simplify using the standard rewrite rules.
-/
theorem lu_sum_pairs {n : ℕ} (j : Fin n) (g : Pr n → K) :
    ∑ p : Pr n, (if p.1.2 = j then g p else 0) =
      ∑ k : Fin n, if h : k < j then g ⟨(k, j), h⟩ else 0 := by
  classical
  let G : Fin n × Fin n → K := fun q => if h : q.1 < q.2 then (if q.2 = j then g ⟨q, h⟩ else 0) else 0
  have e0 : ∑ p : Pr n, (if p.1.2 = j then g p else 0) = ∑ p : Pr n, G p.1 := by
    refine Finset.sum_congr rfl fun p _ => ?_
    have hp : p.1.1 < p.1.2 := p.2
    simp only [G, hp, dite_true]
  have e1 : ∑ p : Pr n, G p.1 = ∑ q : Fin n × Fin n, G q := by
    rw [← Finset.sum_subtype (Finset.univ.filter fun q : Fin n × Fin n => q.1 < q.2)
      (p := fun q : Fin n × Fin n => q.1 < q.2) (by simp) G, Finset.sum_filter]
    refine Finset.sum_congr rfl fun q _ => ?_
    by_cases h : q.1 < q.2
    · simp [h]
    · simp [G, h]
  rw [e0, e1, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single j]
  · simp [G]
  · intro l _ hl
    simp only [G]
    split_ifs <;> rfl
  · simp

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.mul_apply]`. Establish `e1 : ∑ k, u i k * EE r k j = ∑ k : Fin n, if h : k < j then u i k * r ⟨(k, j), h⟩ else 0`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Distinguish the cases in `h : k < j`.

Rewrite using `[lu_EE_lt r h, dif_pos h]`. Rewrite using `[lu_EE_not_lt r h, dif_neg h, mul_zero]`. Rewrite using `[e1]`. Distinguish the cases in `hij : i < j`. Rewrite using `[lu_EE_lt _ hij, ← lu_sum_pairs j (fun p => u i p.1.1 * r p)]`.

Simplify using `only [Matrix.mulVec, dotProduct, lu_M]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[lu_EE_not_lt _ hij]`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations.

Distinguish the cases in `h : k < j`. Rewrite using `[dif_pos h]`. Establish `: u i k = 0` using `hu.1 (lt_of_lt_of_le h (not_lt.1 hij))`. Rewrite using `[this, zero_mul]`. Rewrite using `[dif_neg h]`.
-/
theorem lu_mul_EE {n : ℕ} {u : Matrix (Fin n) (Fin n) K} (hu : IsUpUni u) (r : Pr n → K) :
    u * EE r = EE (lu_M u *ᵥ r) := by
  ext i j
  rw [Matrix.mul_apply]
  have e1 : ∑ k, u i k * EE r k j = ∑ k : Fin n, if h : k < j then u i k * r ⟨(k, j), h⟩ else 0 := by
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases h : k < j
    · rw [lu_EE_lt r h, dif_pos h]
    · rw [lu_EE_not_lt r h, dif_neg h, mul_zero]
  rw [e1]
  by_cases hij : i < j
  · rw [lu_EE_lt _ hij, ← lu_sum_pairs j (fun p => u i p.1.1 * r p)]
    simp only [Matrix.mulVec, dotProduct, lu_M]
    refine Finset.sum_congr rfl fun p _ => ?_
    split_ifs <;> simp
  · rw [lu_EE_not_lt _ hij]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases h : k < j
    · rw [dif_pos h]
      have : u i k = 0 := hu.1 (lt_of_lt_of_le h (not_lt.1 hij))
      rw [this, zero_mul]
    · rw [dif_neg h]

/- English proof (translation)
Use extensionality with `i j`. Distinguish the cases in `h : i < j`. Rewrite using `[Matrix.add_apply, lu_EE_lt _ h, lu_EE_lt _ h, lu_EE_lt _ h]`. Both sides reduce to the same expression. Rewrite using `[Matrix.add_apply, lu_EE_not_lt _ h, lu_EE_not_lt _ h, lu_EE_not_lt _ h, add_zero]`.
-/
theorem lu_EE_add {n : ℕ} (y z : Pr n → K) : EE (y + z) = EE y + EE z := by
  ext i j
  by_cases h : i < j
  · rw [Matrix.add_apply, lu_EE_lt _ h, lu_EE_lt _ h, lu_EE_lt _ h]; rfl
  · rw [Matrix.add_apply, lu_EE_not_lt _ h, lu_EE_not_lt _ h, lu_EE_not_lt _ h, add_zero]

/- English proof (translation)
Rewrite using `[Matrix.mul_add, Matrix.mul_one, lu_mul_EE hu, lu_EE_add, ← add_assoc, lu_eq hu]`.
-/
theorem lu_mul {n : ℕ} {u : Matrix (Fin n) (Fin n) K} (hu : IsUpUni u) (r : Pr n → K) :
    u * (1 + EE r) = 1 + EE (lu_co u + lu_M u *ᵥ r) := by
  rw [Matrix.mul_add, Matrix.mul_one, lu_mul_EE hu, lu_EE_add, ← add_assoc, lu_eq hu]

/- English proof (translation)
Establish `hT : (lu_M u).BlockTriangular (fun p : Pr n => p.1.1)`. Introduce `p p' h`. Establish `h' : p'.1.1 < p.1.1` using `h`. Simplify using `only [lu_M]`. Use `split_ifs`.

Conclude with `hu.1 h'`. Both sides reduce to the same expression. Rewrite using `[hT.det_fintype]`. Use `Finset.prod_eq_one fun k _ => ?_` and prove the remaining obligations. Establish `: (lu_M u).toSquareBlock (fun p : Pr n => p.1.1) k = 1`.

Use extensionality with `⟨p, hp⟩ ⟨p', hp'⟩`. Simplify using `only [Matrix.toSquareBlock_def, Matrix.of_apply, lu_M]`. Establish `hp1 : p.1.1 = k` using `hp`. Establish `hp2 : p'.1.1 = k` using `hp'`. Distinguish the cases in `h : p = p'`.

Substitute `h` using the available equality. Simplify using `[hu.2]`. Rewrite using `[Matrix.one_apply_ne (by simpa [Subtype.ext_iff] using h), if_neg]`. Introduce `h2`. Apply `h` to reduce the goal to its premises.

Apply `Subtype.ext` to reduce the goal to its premises. Apply `Prod.ext` to reduce the goal to its premises. Rewrite using `[hp1, hp2]`. Conclude with `h2.symm`. Rewrite using `[this, Matrix.det_one]`.
-/
theorem lu_det {n : ℕ} {u : Matrix (Fin n) (Fin n) K} (hu : IsUpUni u) : (lu_M u).det = 1 := by
  classical
  have hT : (lu_M u).BlockTriangular (fun p : Pr n => p.1.1) := by
    intro p p' h
    have h' : p'.1.1 < p.1.1 := h
    simp only [lu_M]
    split_ifs
    · exact hu.1 h'
    · rfl
  rw [hT.det_fintype]
  refine Finset.prod_eq_one fun k _ => ?_
  have : (lu_M u).toSquareBlock (fun p : Pr n => p.1.1) k = 1 := by
    ext ⟨p, hp⟩ ⟨p', hp'⟩
    simp only [Matrix.toSquareBlock_def, Matrix.of_apply, lu_M]
    have hp1 : p.1.1 = k := hp
    have hp2 : p'.1.1 = k := hp'
    by_cases h : p = p'
    · subst h
      simp [hu.2]
    · rw [Matrix.one_apply_ne (by simpa [Subtype.ext_iff] using h), if_neg]
      intro h2
      apply h
      apply Subtype.ext
      apply Prod.ext
      · rw [hp1, hp2]
      · exact h2.symm
  rw [this, Matrix.det_one]

end LUalg

variable {K : Type} [CommRing K]

def lu_g {n : ℕ} (y : Pr n → K) : upUniG K n :=
  ⟨sec_gl (1 + EE y) (isUpUni_det K (lu_up y)), lu_up y⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem lu_g_m {n : ℕ} (y : Pr n → K) : sec_m (lu_g y) = 1 + EE y := rfl

/- English proof (translation)
Introduce `i j`. Rewrite using `[Matrix.add_apply]`. Use `R.add_mem ?_ ?_` and prove the remaining obligations. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality.

Rewrite using `[Matrix.one_apply_eq]`. Conclude with `R.one_mem`. Rewrite using `[Matrix.one_apply_ne h]`. Conclude with `R.zero_mem`. Distinguish the cases in `h : i < j`.

Rewrite using `[lu_EE_lt _ h]`. Conclude with `hr _`. Rewrite using `[lu_EE_not_lt _ h]`. Conclude with `R.zero_mem`.
-/
theorem lu_int {R : Subring K} {n : ℕ} {r : Pr n → K} (hr : ∀ p, r p ∈ R) : IsInt R (1 + EE r) := by
  intro i j
  rw [Matrix.add_apply]
  refine R.add_mem ?_ ?_
  · by_cases h : i = j
    · subst h; rw [Matrix.one_apply_eq]; exact R.one_mem
    · rw [Matrix.one_apply_ne h]; exact R.zero_mem
  · by_cases h : i < j
    · rw [lu_EE_lt _ h]; exact hr _
    · rw [lu_EE_not_lt _ h]; exact R.zero_mem

/- English proof (translation)
Use `⟨((lu_g v : upUniG K n) : upUniG K n ⧸ intSub R (upUniG K n)), ?_, ?_⟩` and prove the remaining obligations. Take `⟨h, hh⟩` from `QuotientGroup.mk_out_eq_mul (intSub R (upUniG K n)) (lu_g v)`. Establish `hh' : Quotient.out ((lu_g v : upUniG K n) : upUniG K n ⧸ intSub R (upUniG K n)) = lu_g v * h` using `hh`. Use `set u := Quotient.out ((lu_g v : upUniG K n) : upUniG K n ⧸ intSub R (upUniG K n)) with hu`. Establish `hg : lu_g v = u * (h : upUniG K n)⁻¹` using `by rw [hh']; group`.

Establish `hinv : ((h : upUniG K n)⁻¹) ∈ intSub R (upUniG K n)` using `(intSub R (upUniG K n)).inv_mem h.2`. Establish `hr0U : IsUpUni (sec_m ((h : upUniG K n)⁻¹))` using `((h : upUniG K n)⁻¹).2`. Establish `hr0I : IsInt R (sec_m ((h : upUniG K n)⁻¹))` using `hinv.1`. Use `⟨lu_co (sec_m ((h : upUniG K n)⁻¹)), fun p => hr0I _ _, ?_⟩` and prove the remaining obligations. Establish `e1 : sec_m (lu_g v) = sec_m u * sec_m ((h : upUniG K n)⁻¹)` using `congrArg (fun g : upUniG K n => sec_m g) hg`.

Rewrite `e1` using `[lu_g_m, ← lu_eq hr0U, lu_mul u.2]`. Establish `e2` using `congrArg lu_co e1`. Rewrite `e2` using `[lu_co_EE, lu_co_EE]`. Then use the resulting hypothesis. Introduce and unpack `q ⟨r, hr, hv⟩`. Establish `e1 : lu_g v = Quotient.out q * lu_g r`.

Apply `sec_m_ext` to reduce the goal to its premises. Establish `: sec_m (Quotient.out q * lu_g r) = sec_m (Quotient.out q) * sec_m (lu_g r)` using `rfl`. Rewrite using `[this, lu_g_m, lu_g_m, lu_mul (Quotient.out q).2, ← hv]`. Establish `hmem : lu_g r ∈ intSub R (upUniG K n)` using `(sec_mem_int R (lu_g r) (isUpUni_det K (lu_up r))).2 (lu_int hr)`. Establish `e2 : ((Quotient.out q : upUniG K n) : upUniG K n ⧸ intSub R (upUniG K n)) = ((lu_g v : upUniG K n) : upUniG K n ⧸ intSub R (upUniG K n))` using `(sec_left_eq _ _ _).2 ⟨lu_g r, hmem, e1⟩`.

Rewrite using `[← e2]`. Conclude with `(QuotientGroup.out_eq' q).symm`.
-/
theorem lu_part (R : Subring K) (n : ℕ) (v : Pr n → K) :
    ∃! q : upUniG K n ⧸ intSub R (upUniG K n), ∃ r : Pr n → K, (∀ p, r p ∈ R) ∧
      v = lu_co (sec_m (Quotient.out q)) + lu_M (sec_m (Quotient.out q)) *ᵥ r := by
  refine ⟨((lu_g v : upUniG K n) : upUniG K n ⧸ intSub R (upUniG K n)), ?_, ?_⟩
  · obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (intSub R (upUniG K n)) (lu_g v)
    have hh' : Quotient.out ((lu_g v : upUniG K n) : upUniG K n ⧸ intSub R (upUniG K n)) =
        lu_g v * h := hh
    set u := Quotient.out ((lu_g v : upUniG K n) : upUniG K n ⧸ intSub R (upUniG K n)) with hu
    have hg : lu_g v = u * (h : upUniG K n)⁻¹ := by rw [hh']; group
    have hinv : ((h : upUniG K n)⁻¹) ∈ intSub R (upUniG K n) := (intSub R (upUniG K n)).inv_mem h.2
    have hr0U : IsUpUni (sec_m ((h : upUniG K n)⁻¹)) := ((h : upUniG K n)⁻¹).2
    have hr0I : IsInt R (sec_m ((h : upUniG K n)⁻¹)) := hinv.1
    refine ⟨lu_co (sec_m ((h : upUniG K n)⁻¹)), fun p => hr0I _ _, ?_⟩
    have e1 : sec_m (lu_g v) = sec_m u * sec_m ((h : upUniG K n)⁻¹) :=
      congrArg (fun g : upUniG K n => sec_m g) hg
    rw [lu_g_m, ← lu_eq hr0U, lu_mul u.2] at e1
    have e2 := congrArg lu_co e1
    rwa [lu_co_EE, lu_co_EE] at e2
  · rintro q ⟨r, hr, hv⟩
    have e1 : lu_g v = Quotient.out q * lu_g r := by
      apply sec_m_ext
      have : sec_m (Quotient.out q * lu_g r) = sec_m (Quotient.out q) * sec_m (lu_g r) := rfl
      rw [this, lu_g_m, lu_g_m, lu_mul (Quotient.out q).2, ← hv]
    have hmem : lu_g r ∈ intSub R (upUniG K n) :=
      (sec_mem_int R (lu_g r) (isUpUni_det K (lu_up r))).2 (lu_int hr)
    have e2 : ((Quotient.out q : upUniG K n) : upUniG K n ⧸ intSub R (upUniG K n)) =
        ((lu_g v : upUniG K n) : upUniG K n ⧸ intSub R (upUniG K n)) :=
      (sec_left_eq _ _ _).2 ⟨lu_g r, hmem, e1⟩
    rw [← e2]
    exact (QuotientGroup.out_eq' q).symm

variable [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K} {ψ : AddChar K ℂ}

/- English proof (translation)
Establish `hU : ∀ q : upUniG K n ⧸ intSub R (upUniG K n), IsUpUni (sec_m (Quotient.out q))` using `fun q => (Quotient.out q).2`. Establish `key` using `bx_cells hD (Q := upUniG K n ⧸ intSub R (upUniG K n)) (fun q => lu_co (sec_m (Quotient.out q))) (fun q => lu_M (sec_m (Quotient.out q))) (fun q => by rw [lu_det (hU q)]; exact isUnit_one) (lu_part R n) (fun y => f (1 + EE y)) (fun q r hr => by show f (1 + EE (lu_co (sec_m (Quotie …`. Rewrite using `[← lu_mul (hU q), lu_eq (hU q)]`. Conclude with `hinv _ _ (hU q) (lu_up r) (lu_int hr))`. Use the proof step `(by`.

Use `hfin.subset fun q hq => ?_` and prove the remaining obligations. Establish `hq' : f (1 + EE (lu_co (sec_m (Quotient.out q)))) ≠ 0` using `hq`. Rewrite using `[lu_eq (hU q)] at hq')` and apply the resulting hypothesis. Use `hΛ hΛinv`. Rewrite using `[key]`.

Use `finsum_congr fun q => ?_` and prove the remaining obligations. Use `show _ = (modK R (lu_M (sec_m (Quotient.out q))).det : ℂ) * f (1 + EE (lu_co (sec_m (Quotient.out q))))`. Rewrite using `[lu_det (hU q), modK_one, lu_eq (hU q)]`. Simplify using the standard rewrite rules.
-/
theorem sumU (hD : LocalDatum K R ψ) (n : ℕ) (f : Matrix (Fin n) (Fin n) K → ℂ)
    (hinv : ∀ u r : Matrix (Fin n) (Fin n) K, IsUpUni u → IsUpUni r → IsInt R r → f (u * r) = f u)
    (hfin : {q : upUniG K n ⧸ intSub R (upUniG K n) | f (sec_m (Quotient.out q)) ≠ 0}.Finite)
    {Λ : AddSubgroup K} (hΛ : IsLat Λ) (hΛinv : BInv Λ (fun y : Pr n → K => f (1 + EE y))) :
    ∑ᶠ q : upUniG K n ⧸ intSub R (upUniG K n), f (sec_m (Quotient.out q)) =
      bx R Λ (Pr n) (fun y => f (1 + EE y)) := by
  classical
  have hU : ∀ q : upUniG K n ⧸ intSub R (upUniG K n), IsUpUni (sec_m (Quotient.out q)) :=
    fun q => (Quotient.out q).2
  have key := bx_cells hD (Q := upUniG K n ⧸ intSub R (upUniG K n))
    (fun q => lu_co (sec_m (Quotient.out q))) (fun q => lu_M (sec_m (Quotient.out q)))
    (fun q => by rw [lu_det (hU q)]; exact isUnit_one) (lu_part R n) (fun y => f (1 + EE y))
    (fun q r hr => by
      show f (1 + EE (lu_co (sec_m (Quotient.out q)) + lu_M (sec_m (Quotient.out q)) *ᵥ r)) =
        f (1 + EE (lu_co (sec_m (Quotient.out q))))
      rw [← lu_mul (hU q), lu_eq (hU q)]
      exact hinv _ _ (hU q) (lu_up r) (lu_int hr))
    (by
      refine hfin.subset fun q hq => ?_
      have hq' : f (1 + EE (lu_co (sec_m (Quotient.out q)))) ≠ 0 := hq
      rwa [lu_eq (hU q)] at hq')
    hΛ hΛinv
  rw [key]
  refine finsum_congr fun q => ?_
  show _ = (modK R (lu_M (sec_m (Quotient.out q))).det : ℂ) *
    f (1 + EE (lu_co (sec_m (Quotient.out q))))
  rw [lu_det (hU q), modK_one, lu_eq (hU q)]
  simp

end LU

section ST

variable {K : Type} [CommRing K]

def antidiagonalBlock (n : ℕ) (z : Kˣ) : Matrix (Fin n) (Fin n) K :=
  pt (addBlock h0 n z).1 (addBlock h0 n z).2

/- English proof (translation)
Use `show (if (b : ℕ) = revIn [n] a then ((Function.update (fun _ => (1 : Kˣ)) 0 z (blk [n] a) : Kˣ) : K) else 0) = _`. Establish `ha` using `a.2`. Establish `hb` using `b.2`. Simplify using `only [revIn, blk, ha, if_true, Function.update_self]`. Distinguish the cases in `h : b = Fin.rev a`.

Rewrite using `[if_pos h, if_pos]`. Rewrite using `[h, Fin.val_rev]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[if_neg h, if_neg]`. Introduce `h2`.

Apply `h` to reduce the goal to its premises. Apply `Fin.ext` to reduce the goal to its premises. Rewrite using `[Fin.val_rev]`. Use linear arithmetic over natural numbers and integers.
-/
theorem antidiagonal_block_apply (n : ℕ) (z : Kˣ) (a b : Fin n) :
    antidiagonalBlock n z a b = if b = Fin.rev a then (z : K) else 0 := by
  show (if (b : ℕ) = revIn [n] a then
    ((Function.update (fun _ => (1 : Kˣ)) 0 z (blk [n] a) : Kˣ) : K) else 0) = _
  have ha := a.2
  have hb := b.2
  simp only [revIn, blk, ha, if_true, Function.update_self]
  by_cases h : b = Fin.rev a
  · rw [if_pos h, if_pos]
    rw [h, Fin.val_rev]; omega
  · rw [if_neg h, if_neg]
    intro h2
    apply h
    apply Fin.ext
    rw [Fin.val_rev]; omega

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single (Fin.rev i)]`. Rewrite using `[antidiagonal_block_apply, if_pos rfl]`. Simplify using the standard rewrite rules. Introduce `k _ hk`.

Rewrite using `[antidiagonal_block_apply, if_neg hk, zero_mul]`. Simplify using the standard rewrite rules.
-/
theorem antidiagonal_block_mul_left (n : ℕ) (z : Kˣ) (H : Matrix (Fin n) (Fin n) K) :
    antidiagonalBlock n z * H = ((z : K) • H).submatrix Fin.rev id := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.rev i)]
  · rw [antidiagonal_block_apply, if_pos rfl]; simp
  · intro k _ hk
    rw [antidiagonal_block_apply, if_neg hk, zero_mul]
  · simp

/- English proof (translation)
Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single k]`. Rewrite using `[antidiagonal_block_apply, if_pos rfl]`. Introduce `j _ hj`. Rewrite using `[antidiagonal_block_apply, if_neg (fun h2 => hj (Fin.rev_injective h2).symm), mul_zero]`. Simplify using the standard rewrite rules.
-/
theorem mul_antidiagonal_block_reversed (n : ℕ) (z : Kˣ) (G : Matrix (Fin n) (Fin n) K) (i k : Fin n) :
    (G * antidiagonalBlock n z) i (Fin.rev k) = G i k * (z : K) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single k]
  · rw [antidiagonal_block_apply, if_pos rfl]
  · intro j _ hj
    rw [antidiagonal_block_apply, if_neg (fun h2 => hj (Fin.rev_injective h2).symm), mul_zero]
  · simp

/- English proof (translation)
Apply `sec_m_ext` to reduce the goal to its premises. Take `⟨hg, H, hH, e⟩` from `g.2`. Establish `key : ∀ (G H : Matrix (Fin n) (Fin n) K), IsLowUni G → IsLowUni H → G * antidiagonalBlock n z = antidiagonalBlock n z * H → G = 1`. Introduce `G H hG hH e`. Use extensionality with `i k`.

Distinguish the cases in `hik : i = k`. Rewrite using `[hik, hG.2 k, Matrix.one_apply_eq]`. Rewrite using `[Matrix.one_apply_ne hik]`. Break down `lt_or_gt_of_ne hik with h | h` into its components or cases. Conclude with `Formalism.DoubleCosetMeasures.P.Phase.low_zero hG h`.

Establish `e1` using `congrFun (congrFun e i) (Fin.rev k)`. Rewrite `e1` using `[mul_antidiagonal_block_reversed, antidiagonal_block_mul_left]`. Simplify using `only [Matrix.submatrix_apply, id, Matrix.smul_apply, smul_eq_mul] at e1`. Rewrite `e1` using `[Formalism.DoubleCosetMeasures.P.Phase.low_zero hH (Fin.rev_lt_rev.2 h), mul_zero]`. Conclude with `z.isUnit.mul_left_eq_zero.1 e1`.

Conclude with `key _ H hg hH e`.
-/
theorem st_lowW_single (n : ℕ) (z : Kˣ) (g : lowW K (addBlock h0 n z).1 (addBlock h0 n z).2) :
    g = 1 := by
  apply sec_m_ext
  obtain ⟨hg, H, hH, e⟩ := g.2
  have key : ∀ (G H : Matrix (Fin n) (Fin n) K), IsLowUni G → IsLowUni H →
      G * antidiagonalBlock n z = antidiagonalBlock n z * H → G = 1 := by
    intro G H hG hH e
    ext i k
    by_cases hik : i = k
    · rw [hik, hG.2 k, Matrix.one_apply_eq]
    rw [Matrix.one_apply_ne hik]
    rcases lt_or_gt_of_ne hik with h | h
    · exact Formalism.DoubleCosetMeasures.P.Phase.low_zero hG h
    · have e1 := congrFun (congrFun e i) (Fin.rev k)
      rw [mul_antidiagonal_block_reversed, antidiagonal_block_mul_left] at e1
      simp only [Matrix.submatrix_apply, id, Matrix.smul_apply, smul_eq_mul] at e1
      rw [Formalism.DoubleCosetMeasures.P.Phase.low_zero hH (Fin.rev_lt_rev.2 h), mul_zero] at e1
      exact z.isUnit.mul_left_eq_zero.1 e1
  exact key _ H hg hH e

/- English proof (translation)
Unfold `sLow`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Use `split_ifs with h`. Rewrite using `[Matrix.one_apply_ne]`. Introduce `e`.

Use `congrArg Fin.val e` as an intermediate fact. Simplify using `at this`. Both sides reduce to the same expression.
-/
theorem st_sLow_one (n : ℕ) : sLow (1 : Matrix (Fin n) (Fin n) K) = 0 := by
  unfold sLow
  refine Finset.sum_eq_zero fun j _ => ?_
  split_ifs with h
  · rw [Matrix.one_apply_ne]
    intro e
    have := congrArg Fin.val e
    simp at this
  · rfl

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [pt, Matrix.smul_apply, smul_eq_mul]`. Use `split_ifs`. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem st_pt_smul (s : List ℕ) (t : ℕ → Kˣ) (π : Kˣ) :
    pt s (fun b => π * t b) = (π : K) • pt s t := by
  ext a b
  simp only [pt, Matrix.smul_apply, smul_eq_mul]
  split_ifs
  · simp
  · simp

/- English proof (translation)
Use extensionality with `g`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, H, hH, e⟩`. Use `⟨h1, H, hH, ?_⟩` and prove the remaining obligations. Rewrite `e` using `[st_pt_smul, Matrix.mul_smul, Matrix.smul_mul]`.

Use `congrArg (fun X => ((π⁻¹ : Kˣ) : K) • X) e` as an intermediate fact. Simplify `this` using `[smul_smul]`. Introduce and unpack `⟨h1, H, hH, e⟩`. Use `⟨h1, H, hH, ?_⟩` and prove the remaining obligations. Rewrite using `[st_pt_smul, Matrix.mul_smul, Matrix.smul_mul, e]`.
-/
theorem st_lowW_smul (s : List ℕ) (t : ℕ → Kˣ) (π : Kˣ) :
    lowW K s (fun b => π * t b) = lowW K s t := by
  ext g
  constructor
  · rintro ⟨h1, H, hH, e⟩
    refine ⟨h1, H, hH, ?_⟩
    rw [st_pt_smul, Matrix.mul_smul, Matrix.smul_mul] at e
    have := congrArg (fun X => ((π⁻¹ : Kˣ) : K) • X) e
    simpa [smul_smul] using this
  · rintro ⟨h1, H, hH, e⟩
    refine ⟨h1, H, hH, ?_⟩
    rw [st_pt_smul, Matrix.mul_smul, Matrix.smul_mul, e]

/- English proof (translation)
Unfold `orbZ`. Express the relevant statement in the definitionally equal form `sec_m (sec_lowJ h c 1 ξ) * _ * sec_m u = _`. Rewrite using `[sec_lowJ_m, sec_pt, blkM_mul]`. Establish `h1 : sec_m (1 : lowW K h.1 h.2) = 1` using `rfl`. Rewrite using `[h1]`.

Use `congr 2`. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem st_orbZ_low (h : Point K) (c : Kˣ) (ξ : Fin h.1.sum → K)
    (u : upUniG K (addBlock h 1 c).1.sum) :
    orbZ (addBlock h 1 c) (sec_lowJ h c 1 ξ, u) =
      blkM (addBlock_sum h c) (pt h.1 h.2) 0 (ξ ᵥ* pt h.1 h.2) (c : K) * sec_m u := by
  unfold orbZ
  change sec_m (sec_lowJ h c 1 ξ) * _ * sec_m u = _
  rw [sec_lowJ_m, sec_pt, blkM_mul]
  have h1 : sec_m (1 : lowW K h.1 h.2) = 1 := rfl
  rw [h1]
  congr 2
  · simp
  · simp
  · simp
  · simp

/- English proof (translation)
Unfold `phase`. Express the relevant statement in the definitionally equal form `ψ (sLow (sec_m (sec_lowJ h c 1 ξ)) + sUp (sec_m u)) = _`. Rewrite using `[sec_lowJ_m, sec_sLow]`. Establish `h1 : sec_m (1 : lowW K h.1 h.2) = 1` using `rfl`. Rewrite using `[h1, st_sLow_one, Matrix.vecMul_one, zero_add]`.
-/
theorem st_phase_low (h : Point K) (c : Kˣ) (ξ : Fin h.1.sum → K)
    (u : upUniG K (addBlock h 1 c).1.sum) (ψ : AddChar K ℂ) :
    phase ψ ((sec_lowJ h c 1 ξ, u) :
      lowW K (addBlock h 1 c).1 (addBlock h 1 c).2 × upUniG K (addBlock h 1 c).1.sum) =
      ψ (lastE ξ + sUp (sec_m u)) := by
  unfold phase
  change ψ (sLow (sec_m (sec_lowJ h c 1 ξ)) + sUp (sec_m u)) = _
  rw [sec_lowJ_m, sec_sLow]
  have h1 : sec_m (1 : lowW K h.1 h.2) = 1 := rfl
  rw [h1, st_sLow_one, Matrix.vecMul_one, zero_add]

/- English proof (translation)
Apply `Fin.ext` to reduce the goal to its premises. Rewrite using `[eN_inl]`. Both sides reduce to the same expression.
-/
theorem st_eN_inl (m : ℕ) (a : Fin m) :
    eN (rfl : m + 1 = m + 1) (Sum.inl a) = a.castSucc := by
  apply Fin.ext; rw [eN_inl]; rfl

/- English proof (translation)
Apply `Fin.ext` to reduce the goal to its premises. Rewrite using `[eN_inr]`. Both sides reduce to the same expression.
-/
theorem st_eN_inr (m : ℕ) (u : Unit) : eN (rfl : m + 1 = m + 1) (Sum.inr u) = Fin.last m := by
  apply Fin.ext; rw [eN_inr]; rfl

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.mul_apply, ← Equiv.sum_comp (eN (rfl : m + 1 = m + 1)), Fintype.sum_sum_type]`. Take `⟨i, rfl⟩` from `(eN (rfl : m + 1 = m + 1)).surjective i`. Break down `i with i | i` into its components or cases. Simplify using `only [blkM_ll, blkM_lr, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]`.

Rewrite using `[Finset.sum_eq_single (Fin.rev i)]`. Rewrite using `[antidiagonal_block_apply, if_pos rfl, st_eN_inl, st_eN_inl]`. Simplify using `only [Matrix.submatrix_apply, id, Hm, Fin.rev_castSucc, Fin.cases_succ]`. Introduce `k _ hk`. Rewrite using `[antidiagonal_block_apply, if_neg hk, zero_mul]`.

Simplify using the standard rewrite rules. Simplify using `only [blkM_rl, blkM_rr, Finset.univ_unique, Finset.sum_singleton]`. Rewrite using `[st_eN_inr]`. Simplify using `only [Matrix.submatrix_apply, id, Hm, Fin.rev_last, Fin.cases_zero]`. Use `congr 1`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[st_eN_inl, Matrix.vecMul, dotProduct, Finset.sum_eq_single (Fin.rev k)]`. Rewrite using `[antidiagonal_block_apply, if_pos (Fin.rev_rev k).symm]`. Expand and normalize the polynomial expressions, which then agree. Introduce `l _ hl`.

Rewrite using `[antidiagonal_block_apply, if_neg, mul_zero]`. Introduce `h2`. Apply `hl` to reduce the goal to its premises. Rewrite using `[h2, Fin.rev_rev]`. Simplify using the standard rewrite rules.

Distinguish the cases in `hj : j = Fin.last m`. Rewrite using `[if_pos hj, hj, hu.2, mul_one]`. Rewrite using `[if_neg hj, Formalism.DoubleCosetMeasures.P.Phase.up_zero hu (lt_of_le_of_ne (Fin.le_last j) hj), mul_zero]`.
-/
theorem st_blk_Hm (m : ℕ) (t : Kˣ) (c : K) (ξ : Fin m → K)
    (u : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (hu : IsUpUni u) :
    blkM (rfl : m + 1 = m + 1) (antidiagonalBlock m t) 0 (ξ ᵥ* antidiagonalBlock m t) c * u =
      (Hm (t : K) c ξ u).submatrix Fin.rev id := by
  ext i j
  rw [Matrix.mul_apply, ← Equiv.sum_comp (eN (rfl : m + 1 = m + 1)), Fintype.sum_sum_type]
  obtain ⟨i, rfl⟩ := (eN (rfl : m + 1 = m + 1)).surjective i
  rcases i with i | i
  · simp only [blkM_ll, blkM_lr, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
    rw [Finset.sum_eq_single (Fin.rev i)]
    · rw [antidiagonal_block_apply, if_pos rfl, st_eN_inl, st_eN_inl]
      simp only [Matrix.submatrix_apply, id, Hm, Fin.rev_castSucc, Fin.cases_succ]
    · intro k _ hk
      rw [antidiagonal_block_apply, if_neg hk, zero_mul]
    · simp
  · simp only [blkM_rl, blkM_rr, Finset.univ_unique, Finset.sum_singleton]
    rw [st_eN_inr]
    simp only [Matrix.submatrix_apply, id, Hm, Fin.rev_last, Fin.cases_zero]
    congr 1
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [st_eN_inl, Matrix.vecMul, dotProduct, Finset.sum_eq_single (Fin.rev k)]
      · rw [antidiagonal_block_apply, if_pos (Fin.rev_rev k).symm]; ring
      · intro l _ hl
        rw [antidiagonal_block_apply, if_neg, mul_zero]
        intro h2
        apply hl
        rw [h2, Fin.rev_rev]
      · simp
    · by_cases hj : j = Fin.last m
      · rw [if_pos hj, hj, hu.2, mul_one]
      · rw [if_neg hj, Formalism.DoubleCosetMeasures.P.Phase.up_zero hu (lt_of_le_of_ne (Fin.le_last j) hj), mul_zero]

end ST

section ST2

variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ}

/- English proof (translation)
Unfold `omPhi`. Use `symm`. Use `finsum_eq_of_bijective (fun q₂ => ((Quotient.mk _ 1, q₂) : Cos R (addBlock h0 n z))) ⟨?_, ?_⟩ ?_` and prove the remaining obligations. Introduce `a b h`. Conclude with `(Prod.ext_iff.1 h).2`.

Introduce and unpack `⟨q₁, q₂⟩`. Use `⟨q₂, ?_⟩` and prove the remaining obligations. Use `Prod.ext ?_ rfl` and prove the remaining obligations. Use `show Quotient.mk _ 1 = q₁`. Rewrite using `[← Quotient.out_eq q₁, st_lowW_single n z (Quotient.out q₁)]`.

Introduce `q₂`. Establish `hrep : rep R ((Quotient.mk _ 1, q₂) : Cos R (addBlock h0 n z)) = (1, Quotient.out q₂)` using `Prod.ext (st_lowW_single n z _) rfl`. Use `show _ = Φ (addBlock h0 n z).1.sum (orbZ (addBlock h0 n z) (rep R ((Quotient.mk _ 1, q₂) : Cos R (addBlock h0 n z)))) * phase ψ (rep R ((Quotient.mk _ 1, q₂) : Cos R (addBlock h0 n z)))`. Rewrite using `[hrep]`. Use `show _ = Φ n ((1 : Matrix (Fin n) (Fin n) K) * antidiagonalBlock n z * sec_m (Quotient.out q₂)) * ψ (sLow (1 : Matrix (Fin n) (Fin n) K) + sUp (sec_m (Quotient.out q₂)))`.

Rewrite using `[Matrix.one_mul, antidiagonal_block_mul_left, st_sLow_one, zero_add]`.
-/
theorem omPhi_single (n : ℕ) (z : Kˣ) (Φ : ∀ n : ℕ, Matrix (Fin n) (Fin n) K → ℂ) :
    omPhi R ψ (addBlock h0 n z) Φ = ∑ᶠ q : upUniG K n ⧸ intSub R (upUniG K n),
      Φ n (((z : K) • sec_m (Quotient.out q)).submatrix Fin.rev id) *
        ψ (sUp (sec_m (Quotient.out q))) := by
  unfold omPhi
  symm
  refine finsum_eq_of_bijective
    (fun q₂ => ((Quotient.mk _ 1, q₂) : Cos R (addBlock h0 n z))) ⟨?_, ?_⟩ ?_
  · intro a b h
    exact (Prod.ext_iff.1 h).2
  · rintro ⟨q₁, q₂⟩
    refine ⟨q₂, ?_⟩
    refine Prod.ext ?_ rfl
    show Quotient.mk _ 1 = q₁
    rw [← Quotient.out_eq q₁, st_lowW_single n z (Quotient.out q₁)]
  · intro q₂
    have hrep : rep R ((Quotient.mk _ 1, q₂) : Cos R (addBlock h0 n z)) = (1, Quotient.out q₂) :=
      Prod.ext (st_lowW_single n z _) rfl
    show _ = Φ (addBlock h0 n z).1.sum (orbZ (addBlock h0 n z)
        (rep R ((Quotient.mk _ 1, q₂) : Cos R (addBlock h0 n z)))) *
      phase ψ (rep R ((Quotient.mk _ 1, q₂) : Cos R (addBlock h0 n z)))
    rw [hrep]
    show _ = Φ n ((1 : Matrix (Fin n) (Fin n) K) * antidiagonalBlock n z * sec_m (Quotient.out q₂)) *
      ψ (sLow (1 : Matrix (Fin n) (Fin n) K) + sUp (sec_m (Quotient.out q₂)))
    rw [Matrix.one_mul, antidiagonal_block_mul_left, st_sLow_one, zero_add]

/- English proof (translation)
Establish `key` using `integral_points_finite K R ψ hD (w.1, fun b => π * w.2 b)`. Establish `gen : ∀ H : Subgroup (GL (Fin w.1.sum) K), H = lowW K w.1 (fun b => π * w.2 b) → {q : Quotient (QuotientGroup.rightRel (intSub R H)) × (upUniG K w.1.sum ⧸ intSub R (upUniG K w.1.sum)) | IsInt R (sec_m (Quotient.out q.1) * ((π : K) • pt w.1 w.2) * sec_m (Quotient.out q.2))}.Finite`. Introduce `H hH`. Substitute `hH` using the available equality. Establish `e : ((π : K) • pt w.1 w.2) = pt w.1 (fun b => π * w.2 b)` using `(st_pt_smul _ _ _).symm`.

Rewrite using `[e]`. Conclude with `key`. Establish `h2` using `gen (lowW K w.1 w.2) (st_lowW_smul w.1 w.2 π).symm`. Use `h2.subset ?_` and prove the remaining obligations. Introduce `q hq`.

Establish `hq' : IsInt R ((π : K) • (sec_m (Quotient.out q.1) * pt w.1 w.2 * sec_m (Quotient.out q.2)))` using `hq`. Use `show IsInt R (sec_m (Quotient.out q.1) * ((π : K) • pt w.1 w.2) * sec_m (Quotient.out q.2))`. Rewrite using `[Matrix.mul_smul, Matrix.smul_mul]`. Conclude with `hq'`.
-/
theorem st_fin_cos (hD : LocalDatum K R ψ) (w : Point K) (π : Kˣ) :
    {q : Cos R w | IsInt R ((π : K) • orbZ w (rep R q))}.Finite := by
  have key := integral_points_finite K R ψ hD (w.1, fun b => π * w.2 b)
  have gen : ∀ H : Subgroup (GL (Fin w.1.sum) K), H = lowW K w.1 (fun b => π * w.2 b) →
      {q : Quotient (QuotientGroup.rightRel (intSub R H)) ×
        (upUniG K w.1.sum ⧸ intSub R (upUniG K w.1.sum)) |
        IsInt R (sec_m (Quotient.out q.1) * ((π : K) • pt w.1 w.2) *
          sec_m (Quotient.out q.2))}.Finite := by
    intro H hH
    subst hH
    have e : ((π : K) • pt w.1 w.2) = pt w.1 (fun b => π * w.2 b) := (st_pt_smul _ _ _).symm
    rw [e]
    exact key
  have h2 := gen (lowW K w.1 w.2) (st_lowW_smul w.1 w.2 π).symm
  refine h2.subset ?_
  intro q hq
  have hq' : IsInt R ((π : K) • (sec_m (Quotient.out q.1) * pt w.1 w.2 * sec_m (Quotient.out q.2))) := hq
  show IsInt R (sec_m (Quotient.out q.1) * ((π : K) • pt w.1 w.2) * sec_m (Quotient.out q.2))
  rw [Matrix.mul_smul, Matrix.smul_mul]
  exact hq'

/- English proof (translation)
Establish `key` using `integral_points_finite K R ψ hD (addBlock h0 n π)`. Establish `hinj : Function.Injective (fun q₂ : upUniG K n ⧸ intSub R (upUniG K n) => ((Quotient.mk _ 1, q₂) : Cos R (addBlock h0 n π)))`. Introduce `a b h`. Conclude with `(Prod.ext_iff.1 h).2`. Use `(key.preimage (Set.injOn_of_injective hinj)).subset ?_` and prove the remaining obligations.

Introduce `q₂ hq`. Establish `hrep : rep R ((Quotient.mk _ 1, q₂) : Cos R (addBlock h0 n π)) = (1, Quotient.out q₂)` using `Prod.ext (st_lowW_single n π _) rfl`. Use `show IsInt R (orbZ (addBlock h0 n π) (rep R ((Quotient.mk _ 1, q₂) : Cos R (addBlock h0 n π))))`. Rewrite using `[hrep]`. Use `show IsInt R ((1 : Matrix (Fin n) (Fin n) K) * antidiagonalBlock n π * sec_m (Quotient.out q₂))`.

Rewrite using `[Matrix.one_mul, antidiagonal_block_mul_left]`. Introduce `a b`. Conclude with `hq (Fin.rev a) b`.
-/
theorem fin_single (hD : LocalDatum K R ψ) (n : ℕ) (π : Kˣ) :
    {q : upUniG K n ⧸ intSub R (upUniG K n) |
      IsInt R ((π : K) • sec_m (Quotient.out q))}.Finite := by
  have key := integral_points_finite K R ψ hD (addBlock h0 n π)
  have hinj : Function.Injective (fun q₂ : upUniG K n ⧸ intSub R (upUniG K n) =>
      ((Quotient.mk _ 1, q₂) : Cos R (addBlock h0 n π))) := by
    intro a b h
    exact (Prod.ext_iff.1 h).2
  refine (key.preimage (Set.injOn_of_injective hinj)).subset ?_
  intro q₂ hq
  have hrep : rep R ((Quotient.mk _ 1, q₂) : Cos R (addBlock h0 n π)) = (1, Quotient.out q₂) :=
    Prod.ext (st_lowW_single n π _) rfl
  show IsInt R (orbZ (addBlock h0 n π) (rep R ((Quotient.mk _ 1, q₂) : Cos R (addBlock h0 n π))))
  rw [hrep]
  show IsInt R ((1 : Matrix (Fin n) (Fin n) K) * antidiagonalBlock n π * sec_m (Quotient.out q₂))
  rw [Matrix.one_mul, antidiagonal_block_mul_left]
  intro a b
  exact hq (Fin.rev a) b

/- English proof (translation)
Establish `hb` using `sec_low_bij R (addBlock h0 m t) c`. Establish `hb2 : Function.Bijective (fun ξ : Fin m → KR R => ((Quotient.mk _ 1, ξ) : Quotient (QuotientGroup.rightRel (intSub R (lowW K (addBlock h0 m t).1 (addBlock h0 m t).2))) × (Fin (addBlock h0 m t).1.sum → KR R)))`. Prove the components needed by the constructor for the conclusion. Introduce `a b h`. Conclude with `(Prod.ext_iff.1 h).2`.

Introduce and unpack `⟨q₁, ξ⟩`. Use `⟨ξ, Prod.ext ?_ rfl⟩` and prove the remaining obligations. Use `show Quotient.mk _ 1 = q₁`. Rewrite using `[← Quotient.out_eq q₁, st_lowW_single m t (Quotient.out q₁)]`. Establish `hc` using `hb.comp hb2`.

Use `hc using 2 with ξ` and compare the differences between its conclusion and the goal. Use `show _ = Quotient.mk _ (sec_lowJ (addBlock h0 m t) c (Quotient.out _) (outV R ξ))`. Rewrite using `[st_lowW_single m t (Quotient.out _)]`.
-/
theorem st_low_bij (m : ℕ) (t c : Kˣ) :
    Function.Bijective (fun ξ : Fin m → KR R =>
      (Quotient.mk (QuotientGroup.rightRel (intSub R (lowW K (addBlock (addBlock h0 m t) 1 c).1
        (addBlock (addBlock h0 m t) 1 c).2))) (sec_lowJ (addBlock h0 m t) c 1 (outV R ξ)))) := by
  have hb := sec_low_bij R (addBlock h0 m t) c
  have hb2 : Function.Bijective (fun ξ : Fin m → KR R =>
      ((Quotient.mk _ 1, ξ) : Quotient (QuotientGroup.rightRel
        (intSub R (lowW K (addBlock h0 m t).1 (addBlock h0 m t).2))) ×
        (Fin (addBlock h0 m t).1.sum → KR R))) := by
    constructor
    · intro a b h
      exact (Prod.ext_iff.1 h).2
    · rintro ⟨q₁, ξ⟩
      refine ⟨ξ, Prod.ext ?_ rfl⟩
      show Quotient.mk _ 1 = q₁
      rw [← Quotient.out_eq q₁, st_lowW_single m t (Quotient.out q₁)]
  have hc := hb.comp hb2
  convert hc using 2 with ξ
  show _ = Quotient.mk _ (sec_lowJ (addBlock h0 m t) c (Quotient.out _) (outV R ξ))
  rw [st_lowW_single m t (Quotient.out _)]

/- English proof (translation)
Establish `hψ : ∀ r ∈ R, ψ r = 1` using `fun r hr => psi_R hD hr`. Set `w : Point K` to `addBlock (addBlock h0 m t) 1 c`. Set `F : lowW K w.1 w.2 × upUniG K w.1.sum → ℂ` to `fun p => Φ w.1.sum (orbZ w p) * phase ψ p`. Establish `hFinv : ∀ a ∈ intSub R (lowW K w.1 w.2), ∀ b ∈ intSub R (upUniG K w.1.sum), ∀ (x : lowW K w.1 w.2) (y : upUniG K w.1.sum), F (a * x, y * b) = F (x, y)`. Introduce `a ha b hb x y`.

Use `show Φ w.1.sum (orbZ w (a * x, y * b)) * phase ψ ((a * x, y * b) : lowW K w.1 w.2 × upUniG K w.1.sum) = _`. Rewrite using `[inv_orbZ, inv_phase R ψ hψ w a ha b hb x y]`. Use `congr 1`. Conclude with `h1 _ _ _ a.2.1 ha.1 b.2 hb.1`. Establish `hFrep : ∀ p, F (rep R (toCos R p)) = F p`.

Introduce `p`. Take `⟨a, ha, b, hb, e⟩` from `inv_exists R p (rep R (toCos R p)) (inv_toCos_rep R _).symm`. Rewrite using `[e]`. Conclude with `hFinv a ha b hb p.1 p.2`. Establish `hfin : (Function.support (fun q : Cos R w => F (rep R q))).Finite`.

Use `(st_fin_cos hD w π).subset ?_` and prove the remaining obligations. Introduce `q hq`. Establish `h3 : Φ w.1.sum (orbZ w (rep R q)) ≠ 0` using `left_ne_zero_of_mul hq`. Conclude with `h2 _ h3`. Establish `s1 : ∑ᶠ q : Cos R w, F (rep R q) = ∑ᶠ q₂ : upUniG K w.1.sum ⧸ intSub R (upUniG K w.1.sum), ∑ᶠ q₁ : Quotient (QuotientGroup.rightRel (intSub R (lowW K w.1 w.2))), F (rep R ((q₁, q₂) : Cos R w))`.

Rewrite using `[← finsum_comp_equiv (Equiv.prodComm (upUniG K w.1.sum ⧸ intSub R (upUniG K w.1.sum)) (Quotient (QuotientGroup.rightRel (intSub R (lowW K w.1 w.2)))))]`. Rewrite using `[finsum_curry]`. Both sides reduce to the same expression. Conclude with `hfin.preimage (Equiv.injective _).injOn`. Use `show ∑ᶠ q : Cos R w, F (rep R q) = _`.

Rewrite using `[s1]`. Use `finsum_congr fun (q₂ : upUniG K (m + 1) ⧸ intSub R (upUniG K (m + 1))) => ?_` and prove the remaining obligations. Use `symm`. Use `finsum_eq_of_bijective _ (st_low_bij (R := R) m t c) fun ξ => ?_` and prove the remaining obligations. Establish `e : ((Quotient.mk _ (sec_lowJ (addBlock h0 m t) c 1 (outV R ξ)), q₂) : Cos R w) = toCos R (sec_lowJ (addBlock h0 m t) c 1 (outV R ξ), Quotient.out q₂)` using `Prod.ext rfl (Quotient.out_eq q₂).symm`.

Use `show _ = F (rep R ((Quotient.mk _ (sec_lowJ (addBlock h0 m t) c 1 (outV R ξ)), q₂) : Cos R w))`. Rewrite using `[e, hFrep]`. Use `show _ = Φ w.1.sum (orbZ w (sec_lowJ (addBlock h0 m t) c 1 (outV R ξ), Quotient.out q₂)) * phase ψ ((sec_lowJ (addBlock h0 m t) c 1 (outV R ξ), Quotient.out q₂) : lowW K w.1 w.2 × upUniG K w.1.sum)`. Rewrite using `[st_orbZ_low, st_phase_low]`. Use `show _ = Φ (m + 1) (blkM (rfl : m + 1 = m + 1) (antidiagonalBlock m t) 0 (outV R ξ ᵥ* antidiagonalBlock m t) (c : K) * sec_m (Quotient.out q₂)) * ψ (lastE (outV R ξ) + sUp (sec_m (Quotient.out q₂)))`.

Rewrite using `[st_blk_Hm m t (c : K) (outV R ξ) _ (Quotient.out q₂).2]`.
-/
theorem orbital_integral_two_blocks (hD : LocalDatum K R ψ) (m : ℕ) (t c : Kˣ)
    (Φ : ∀ n : ℕ, Matrix (Fin n) (Fin n) K → ℂ) (π : Kˣ)
    (h1 : ∀ Z a b : Matrix (Fin (m + 1)) (Fin (m + 1)) K, IsLowUni a → IsInt R a → IsUpUni b →
      IsInt R b → Φ (m + 1) (a * Z * b) = Φ (m + 1) Z)
    (h2 : ∀ Z : Matrix (Fin (m + 1)) (Fin (m + 1)) K, Φ (m + 1) Z ≠ 0 → IsInt R ((π : K) • Z)) :
    omPhi R ψ (pt2 h0 m t c) Φ =
      ∑ᶠ q : upUniG K (m + 1) ⧸ intSub R (upUniG K (m + 1)), ∑ᶠ ξ : Fin m → KR R,
        Φ (m + 1) ((Hm (t : K) (c : K) (outV R ξ) (sec_m (Quotient.out q))).submatrix Fin.rev id) *
          ψ (lastE (outV R ξ) + sUp (sec_m (Quotient.out q))) := by
  have hψ : ∀ r ∈ R, ψ r = 1 := fun r hr => psi_R hD hr
  let w : Point K := addBlock (addBlock h0 m t) 1 c
  let F : lowW K w.1 w.2 × upUniG K w.1.sum → ℂ := fun p => Φ w.1.sum (orbZ w p) * phase ψ p
  have hFinv : ∀ a ∈ intSub R (lowW K w.1 w.2), ∀ b ∈ intSub R (upUniG K w.1.sum),
      ∀ (x : lowW K w.1 w.2) (y : upUniG K w.1.sum), F (a * x, y * b) = F (x, y) := by
    intro a ha b hb x y
    show Φ w.1.sum (orbZ w (a * x, y * b)) * phase ψ ((a * x, y * b) : lowW K w.1 w.2 × upUniG K w.1.sum) = _
    rw [inv_orbZ, inv_phase R ψ hψ w a ha b hb x y]
    congr 1
    exact h1 _ _ _ a.2.1 ha.1 b.2 hb.1
  have hFrep : ∀ p, F (rep R (toCos R p)) = F p := by
    intro p
    obtain ⟨a, ha, b, hb, e⟩ := inv_exists R p (rep R (toCos R p)) (inv_toCos_rep R _).symm
    rw [e]
    exact hFinv a ha b hb p.1 p.2
  have hfin : (Function.support (fun q : Cos R w => F (rep R q))).Finite := by
    refine (st_fin_cos hD w π).subset ?_
    intro q hq
    have h3 : Φ w.1.sum (orbZ w (rep R q)) ≠ 0 := left_ne_zero_of_mul hq
    exact h2 _ h3
  have s1 : ∑ᶠ q : Cos R w, F (rep R q) =
      ∑ᶠ q₂ : upUniG K w.1.sum ⧸ intSub R (upUniG K w.1.sum),
        ∑ᶠ q₁ : Quotient (QuotientGroup.rightRel (intSub R (lowW K w.1 w.2))),
          F (rep R ((q₁, q₂) : Cos R w)) := by
    rw [← finsum_comp_equiv (Equiv.prodComm (upUniG K w.1.sum ⧸ intSub R (upUniG K w.1.sum))
      (Quotient (QuotientGroup.rightRel (intSub R (lowW K w.1 w.2)))))]
    rw [finsum_curry]
    · rfl
    · exact hfin.preimage (Equiv.injective _).injOn
  show ∑ᶠ q : Cos R w, F (rep R q) = _
  rw [s1]
  refine finsum_congr fun (q₂ : upUniG K (m + 1) ⧸ intSub R (upUniG K (m + 1))) => ?_
  symm
  refine finsum_eq_of_bijective _ (st_low_bij (R := R) m t c) fun ξ => ?_
  have e : ((Quotient.mk _ (sec_lowJ (addBlock h0 m t) c 1 (outV R ξ)), q₂) : Cos R w) =
      toCos R (sec_lowJ (addBlock h0 m t) c 1 (outV R ξ), Quotient.out q₂) :=
    Prod.ext rfl (Quotient.out_eq q₂).symm
  show _ = F (rep R ((Quotient.mk _ (sec_lowJ (addBlock h0 m t) c 1 (outV R ξ)), q₂) : Cos R w))
  rw [e, hFrep]
  show _ = Φ w.1.sum (orbZ w (sec_lowJ (addBlock h0 m t) c 1 (outV R ξ), Quotient.out q₂)) *
    phase ψ ((sec_lowJ (addBlock h0 m t) c 1 (outV R ξ), Quotient.out q₂) :
      lowW K w.1 w.2 × upUniG K w.1.sum)
  rw [st_orbZ_low, st_phase_low]
  show _ = Φ (m + 1) (blkM (rfl : m + 1 = m + 1) (antidiagonalBlock m t) 0 (outV R ξ ᵥ* antidiagonalBlock m t) (c : K) *
    sec_m (Quotient.out q₂)) * ψ (lastE (outV R ξ) + sUp (sec_m (Quotient.out q₂)))
  rw [st_blk_Hm m t (c : K) (outV R ξ) _ (Quotient.out q₂).2]

end ST2

section HS

variable {A : Type} [CommRing A]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem hs_succAbove_one_zero {n : ℕ} : (Fin.succAbove (1 : Fin (n + 2)) 0) = 0 := by
  rfl

/- English proof (translation)
Apply `Fin.succAbove_of_le_castSucc` to reduce the goal to its premises. Rewrite using `[Fin.le_def]`. Simplify using the standard rewrite rules.
-/
theorem hs_succAbove_one_succ {n : ℕ} (i : Fin n) :
    (Fin.succAbove (1 : Fin (n + 2)) i.succ) = i.succ.succ := by
  apply Fin.succAbove_of_le_castSucc
  rw [Fin.le_def]
  simp

/- English proof (translation)
Introduce `i j`. Use `⟨fun e => (h _ _).1 (by simp [e]), fun e => (h _ _).2 (by simpa using e)⟩` and prove the remaining obligations.
-/
theorem hs_isHess_succ {n : ℕ} {t : A} {M : Matrix (Fin (n + 1)) (Fin (n + 1)) A} (h : IsHess t M) :
    IsHess t (M.submatrix Fin.succ Fin.succ) := by
  intro i j
  refine ⟨fun e => (h _ _).1 (by simp [e]), fun e => (h _ _).2 (by simpa using e)⟩

/- English proof (translation)
Introduce `i j`. Prove the components needed by the constructor for the conclusion. Introduce `e`. Take `⟨i', rfl⟩ : ∃ i', i = Fin.succ i'` from `⟨i.pred (by intro h0; simp [h0] at e), by simp⟩`. Rewrite using `[Matrix.submatrix_apply, hs_succAbove_one_succ]`.

Conclude with `(h _ _).1 (by simp at e ⊢; omega)`. Introduce `e`. Take `⟨i', rfl⟩ : ∃ i', i = Fin.succ i'` from `⟨i.pred (by intro h0; simp [h0] at e), by simp⟩`. Rewrite using `[Matrix.submatrix_apply, hs_succAbove_one_succ]`. Conclude with `(h _ _).2 (by simp at e ⊢; omega)`.
-/
theorem hs_isHess_above {n : ℕ} {t : A} {M : Matrix (Fin (n + 2)) (Fin (n + 2)) A} (h : IsHess t M) :
    IsHess t (M.submatrix (Fin.succAbove 1) Fin.succ) := by
  intro i j
  constructor
  · intro e
    obtain ⟨i', rfl⟩ : ∃ i', i = Fin.succ i' := ⟨i.pred (by intro h0; simp [h0] at e), by simp⟩
    rw [Matrix.submatrix_apply, hs_succAbove_one_succ]
    exact (h _ _).1 (by simp at e ⊢; omega)
  · intro e
    obtain ⟨i', rfl⟩ : ∃ i', i = Fin.succ i' := ⟨i.pred (by intro h0; simp [h0] at e), by simp⟩
    rw [Matrix.submatrix_apply, hs_succAbove_one_succ]
    exact (h _ _).2 (by simp at e ⊢; omega)

/- English proof (translation)
Rewrite using `[Matrix.det_succ_column_zero, Fin.sum_univ_succ, Fin.sum_univ_succ]`. Establish `h1 : M 1 0 = t` using `(h _ _).1 (by simp)`. Establish `h2 : ∀ k : Fin n, M k.succ.succ 0 = 0` using `fun k => (h _ _).2 (by simp)`. Establish `h3 : (Fin.succ (0 : Fin (n + 1))) = 1` using `rfl`. Establish `h4 : ((1 : Fin (n + 2)) : ℕ) = 1` using `rfl`.

Simplify using `only [h3, h1, h2, h4, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Fin.succAbove_zero, Fin.val_zero, pow_zero, one_mul, pow_one]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hess_laplace {n : ℕ} {t : A} (M : Matrix (Fin (n + 2)) (Fin (n + 2)) A) (h : IsHess t M) :
    M.det = M 0 0 * (M.submatrix Fin.succ Fin.succ).det -
      t * (M.submatrix (Fin.succAbove 1) Fin.succ).det := by
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ, Fin.sum_univ_succ]
  have h1 : M 1 0 = t := (h _ _).1 (by simp)
  have h2 : ∀ k : Fin n, M k.succ.succ 0 = 0 := fun k => (h _ _).2 (by simp)
  have h3 : (Fin.succ (0 : Fin (n + 1))) = 1 := rfl
  have h4 : ((1 : Fin (n + 2)) : ℕ) = 1 := rfl
  simp only [h3, h1, h2, h4, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Fin.succAbove_zero,
    Fin.val_zero, pow_zero, one_mul, pow_one]
  ring

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `succ n ih`. Consider the cases of `n with`. Consider the case `zero => exact ⟨0, by simp⟩`.

Consider the case `succ k`. Take `⟨r, hr⟩` from `ih (M.submatrix Fin.succ Fin.succ) (hs_isHess_succ h)`. Use `⟨M 0 0 * r - (M.submatrix (Fin.succAbove 1) Fin.succ).det, ?_⟩` and prove the remaining obligations. Rewrite using `[hess_laplace M h, hr, Fin.prod_univ_succ (fun i => M i i)]`. Simplify using `only [Matrix.submatrix_apply]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem hess_one {n : ℕ} {t : A} (M : Matrix (Fin n) (Fin n) A) (h : IsHess t M) :
    ∃ r, M.det = ∏ i, M i i + t * r := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    cases n with
    | zero => exact ⟨0, by simp⟩
    | succ k =>
      obtain ⟨r, hr⟩ := ih (M.submatrix Fin.succ Fin.succ) (hs_isHess_succ h)
      refine ⟨M 0 0 * r - (M.submatrix (Fin.succAbove 1) Fin.succ).det, ?_⟩
      rw [hess_laplace M h, hr, Fin.prod_univ_succ (fun i => M i i)]
      simp only [Matrix.submatrix_apply]
      ring

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem hs_sg_succ {n : ℕ} (M : Matrix (Fin (n + 2)) (Fin (n + 2)) A) :
    sg M = M 0 0 * sg (M.submatrix (Fin.succ : Fin (n + 1) → Fin (n + 2)) Fin.succ) +
      M 0 1 * ∏ k : Fin n, M k.succ.succ k.succ.succ := rfl

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => exact ⟨0, by simp [sg]⟩`. Consider the case `succ n ih`. Consider the cases of `n with`. Consider the case `zero => exact ⟨0, by simp [sg]⟩`.

Consider the case `succ k`. Take `⟨r, hr⟩` from `ih (M.submatrix Fin.succ Fin.succ) (hs_isHess_succ h)`. Take `⟨r', hr'⟩` from `hess_one (M.submatrix (Fin.succAbove 1) Fin.succ) (hs_isHess_above h)`. Use `⟨M 0 0 * r - r', ?_⟩` and prove the remaining obligations. Rewrite using `[hess_laplace M h, hr, hr', hs_sg_succ, Fin.prod_univ_succ (fun i => M i i), Fin.prod_univ_succ (fun i => (M.submatrix (Fin.succAbove 1) Fin.succ) i i)]`.

Simplify using `only [Matrix.submatrix_apply, hs_succAbove_one_zero, hs_succAbove_one_succ]`. Establish `h3 : (Fin.succ (0 : Fin (k + 1))) = 1` using `rfl`. Rewrite using `[h3]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hess_two {n : ℕ} {t : A} (M : Matrix (Fin n) (Fin n) A) (h : IsHess t M) :
    ∃ r, M.det = ∏ i, M i i - t * sg M + t ^ 2 * r := by
  induction n with
  | zero => exact ⟨0, by simp [sg]⟩
  | succ n ih =>
    cases n with
    | zero => exact ⟨0, by simp [sg]⟩
    | succ k =>
      obtain ⟨r, hr⟩ := ih (M.submatrix Fin.succ Fin.succ) (hs_isHess_succ h)
      obtain ⟨r', hr'⟩ := hess_one (M.submatrix (Fin.succAbove 1) Fin.succ) (hs_isHess_above h)
      refine ⟨M 0 0 * r - r', ?_⟩
      rw [hess_laplace M h, hr, hr', hs_sg_succ, Fin.prod_univ_succ (fun i => M i i),
        Fin.prod_univ_succ (fun i => (M.submatrix (Fin.succAbove 1) Fin.succ) i i)]
      simp only [Matrix.submatrix_apply, hs_succAbove_one_zero, hs_succAbove_one_succ]
      have h3 : (Fin.succ (0 : Fin (k + 1))) = 1 := rfl
      rw [h3]
      ring

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp [sg]`. Consider the case `succ n ih`. Use `ih (M.submatrix Fin.succ Fin.succ) (fun i => e i.succ) (fun i => he i.succ)` as an intermediate fact. Rewrite using `[hs_sg_succ, this, Fin.prod_univ_succ (fun i => M i i), Fin.sum_univ_succ, Fin.prod_univ_succ (fun i : Fin (n + 1) => M i.succ i.succ)]`.

Simplify using `only [Matrix.submatrix_apply, Fin.succ_castSucc, Fin.castSucc_zero]`. Establish `h3 : (Fin.succ (0 : Fin (n + 1))) = 1` using `rfl`. Rewrite using `[h3]`. Establish `e0` using `he 0`. Establish `e1` using `he 1`.

Rewrite using `[Fin.prod_univ_succ (fun i : Fin (n + 1) => M i.succ i.succ), h3]`. Take the linear combination `(-(M 0 1 * ∏ k : Fin n, M k.succ.succ k.succ.succ) * (M 1 1 * e 1)) * e0 - (M 0 1 * ∏ k : Fin n, M k.succ.succ k.succ.succ) * e1`.
-/
theorem sg_units {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) A) (e : Fin (n + 1) → A)
    (he : ∀ i, M i i * e i = 1) :
    sg M = (∏ i, M i i) * ∑ i : Fin n, M i.castSucc i.succ * e i.castSucc * e i.succ := by
  induction n with
  | zero => simp [sg]
  | succ n ih =>
    have := ih (M.submatrix Fin.succ Fin.succ) (fun i => e i.succ) (fun i => he i.succ)
    rw [hs_sg_succ, this, Fin.prod_univ_succ (fun i => M i i), Fin.sum_univ_succ,
      Fin.prod_univ_succ (fun i : Fin (n + 1) => M i.succ i.succ)]
    simp only [Matrix.submatrix_apply, Fin.succ_castSucc, Fin.castSucc_zero]
    have h3 : (Fin.succ (0 : Fin (n + 1))) = 1 := rfl
    rw [h3]
    have e0 := he 0
    have e1 := he 1
    rw [Fin.prod_univ_succ (fun i : Fin (n + 1) => M i.succ i.succ), h3]
    linear_combination (-(M 0 1 * ∏ k : Fin n, M k.succ.succ k.succ.succ) * (M 1 1 * e 1)) * e0 -
      (M 0 1 * ∏ k : Fin n, M k.succ.succ k.succ.succ) * e1

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp [sg]`. Consider the case `succ n ih`. Consider the cases of `n with`. Consider the case `zero => simp [sg]`.

Consider the case `succ k`. Rewrite using `[hs_sg_succ, hs_sg_succ, map_add, map_mul, map_mul, map_prod, ih]`. Both sides reduce to the same expression.
-/
theorem hs_sg_map {B : Type} [CommRing B] (f : A →+* B) {n : ℕ} (M : Matrix (Fin n) (Fin n) A) :
    f (sg M) = sg (M.map f) := by
  induction n with
  | zero => simp [sg]
  | succ n ih =>
    cases n with
    | zero => simp [sg]
    | succ k =>
      rw [hs_sg_succ, hs_sg_succ, map_add, map_mul, map_mul, map_prod, ih]
      rfl

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp [sg]`. Consider the case `succ n ih`. Consider the cases of `n with`. Consider the case `zero => simp [sg]`.

Consider the case `succ k`. Establish `h1` using `ih (M.submatrix Fin.succ Fin.succ)`. Establish `h2 : (c • M).submatrix (Fin.succ : Fin (k + 1) → Fin (k + 2)) Fin.succ = c • M.submatrix Fin.succ Fin.succ` using `rfl`. Rewrite using `[hs_sg_succ, hs_sg_succ, h2]`. Simplify using `only [Matrix.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`.

Take the linear combination `(c * M 0 0) * h1`.
-/
theorem hs_sg_smul (c : A) {n : ℕ} (M : Matrix (Fin n) (Fin n) A) :
    c * sg (c • M) = c ^ n * sg M := by
  induction n with
  | zero => simp [sg]
  | succ n ih =>
    cases n with
    | zero => simp [sg]
    | succ k =>
      have h1 := ih (M.submatrix Fin.succ Fin.succ)
      have h2 : (c • M).submatrix (Fin.succ : Fin (k + 1) → Fin (k + 2)) Fin.succ =
          c • M.submatrix Fin.succ Fin.succ := rfl
      rw [hs_sg_succ, hs_sg_succ, h2]
      simp only [Matrix.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const,
        Finset.card_univ, Fintype.card_fin]
      linear_combination (c * M 0 0) * h1

variable {K : Type} [CommRing K] {R : Subring K} {ϖ : Kˣ}

def hs_lift {n a : ℕ} (M : Matrix (Fin n) (Fin n) K) (hM : ∀ i j, Bd R ϖ a (M i j)) :
    Matrix (Fin n) (Fin n) R := fun i j => ⟨(ϖ : K) ^ a * M i j, hM i j⟩

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[hs_lift]`.
-/
theorem hs_lift_map {n a : ℕ} (M : Matrix (Fin n) (Fin n) K) (hM : ∀ i j, Bd R ϖ a (M i j)) :
    (hs_lift M hM).map R.subtype = (ϖ : K) ^ a • M := by
  ext i j
  simp [hs_lift]

/- English proof (translation)
Introduce `i j`. Prove the components needed by the constructor for the conclusion. Introduce `e`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[hs_lift, (h i j).1 e]`.

Introduce `e`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[hs_lift, (h i j).2 e]`.
-/
theorem hs_lift_hess {n a : ℕ} {t : K} (M : Matrix (Fin n) (Fin n) K) (h : IsHess t M)
    (ht : Bd R ϖ a t) (hM : ∀ i j, Bd R ϖ a (M i j)) :
    IsHess (⟨(ϖ : K) ^ a * t, ht⟩ : R) (hs_lift M hM) := by
  intro i j
  constructor
  · intro e
    apply Subtype.ext
    simp [hs_lift, (h i j).1 e]
  · intro e
    apply Subtype.ext
    simp [hs_lift, (h i j).2 e]

/- English proof (translation)
Establish `h` using `RingHom.map_det R.subtype (hs_lift M hM)`. Rewrite `h` using `[RingHom.mapMatrix_apply, hs_lift_map, Matrix.det_smul, Fintype.card_fin]`. Conclude with `h`.
-/
theorem hs_lift_det {n a : ℕ} (M : Matrix (Fin n) (Fin n) K) (hM : ∀ i j, Bd R ϖ a (M i j)) :
    (((hs_lift M hM).det : R) : K) = ((ϖ : K) ^ a) ^ n * M.det := by
  have h := RingHom.map_det R.subtype (hs_lift M hM)
  rw [RingHom.mapMatrix_apply, hs_lift_map, Matrix.det_smul, Fintype.card_fin] at h
  exact h

/- English proof (translation)
Establish `h : ((∏ i, (hs_lift M hM) i i : R) : K) = ∏ i, ((ϖ : K) ^ a * M i i)`. Rewrite using `[← Subring.coe_subtype, map_prod]`. Both sides reduce to the same expression. Rewrite using `[h, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`.
-/
theorem hs_lift_prod {n a : ℕ} (M : Matrix (Fin n) (Fin n) K) (hM : ∀ i j, Bd R ϖ a (M i j)) :
    ((∏ i, (hs_lift M hM) i i : R) : K) = ((ϖ : K) ^ a) ^ n * ∏ i, M i i := by
  have h : ((∏ i, (hs_lift M hM) i i : R) : K) = ∏ i, ((ϖ : K) ^ a * M i i) := by
    rw [← Subring.coe_subtype, map_prod]
    rfl
  rw [h, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/- English proof (translation)
Rewrite using `[← mul_pow, ← mul_pow]`. Simplify using the standard rewrite rules.
-/
theorem hs_inv_pow (a n : ℕ) : (((ϖ⁻¹ : Kˣ) : K) ^ a) ^ n * ((ϖ : K) ^ a) ^ n = 1 := by
  rw [← mul_pow, ← mul_pow]; simp

/- English proof (translation)
Take `⟨r, hr⟩` from `hess_one (hs_lift M hM) (hs_lift_hess M h ht hM)`. Establish `hr' : ((ϖ : K) ^ a) ^ n * M.det = ((ϖ : K) ^ a) ^ n * ∏ i, M i i + (ϖ : K) ^ a * t * (r : K)`. Use `congrArg (fun x : R => (x : K)) hr` as an intermediate fact. Simplify using `only [Subring.coe_add, Subring.coe_mul] at this`. Rewrite `this` using `[hs_lift_det, hs_lift_prod]`.

Conclude with `this`. Establish `hi` using `hs_inv_pow (ϖ := ϖ) a n`. Use `⟨(((ϖ⁻¹ : Kˣ) : K) ^ a) ^ n * ((ϖ : K) ^ a * (r : K)), ?_, ?_⟩` and prove the remaining obligations. Establish `: (ϖ : K) ^ (n * a) * ((((ϖ⁻¹ : Kˣ) : K) ^ a) ^ n * ((ϖ : K) ^ a * (r : K))) = (ϖ : K) ^ a * (r : K)`. Rewrite using `[mul_comm n a, pow_mul]`.

Take the linear combination `((ϖ : K) ^ a * (r : K)) * hi`. Unfold `Bd`. Rewrite using `[this]`. Conclude with `R.mul_mem (R.pow_mem hϖ a) r.2`. Take the linear combination `((((ϖ⁻¹ : Kˣ) : K) ^ a) ^ n) * hr' + (∏ i, M i i - M.det) * hi`.
-/
theorem hess_one_bd (hϖ : (ϖ : K) ∈ R) {n a : ℕ} {t : K} (M : Matrix (Fin n) (Fin n) K) (h : IsHess t M)
    (ht : Bd R ϖ a t) (hM : ∀ i j, Bd R ϖ a (M i j)) :
    ∃ r, Bd R ϖ (n * a) r ∧ M.det = ∏ i, M i i + t * r := by
  obtain ⟨r, hr⟩ := hess_one (hs_lift M hM) (hs_lift_hess M h ht hM)
  have hr' : ((ϖ : K) ^ a) ^ n * M.det =
      ((ϖ : K) ^ a) ^ n * ∏ i, M i i + (ϖ : K) ^ a * t * (r : K) := by
    have := congrArg (fun x : R => (x : K)) hr
    simp only [Subring.coe_add, Subring.coe_mul] at this
    rw [hs_lift_det, hs_lift_prod] at this
    exact this
  have hi := hs_inv_pow (ϖ := ϖ) a n
  refine ⟨(((ϖ⁻¹ : Kˣ) : K) ^ a) ^ n * ((ϖ : K) ^ a * (r : K)), ?_, ?_⟩
  · have : (ϖ : K) ^ (n * a) * ((((ϖ⁻¹ : Kˣ) : K) ^ a) ^ n * ((ϖ : K) ^ a * (r : K))) =
        (ϖ : K) ^ a * (r : K) := by
      rw [mul_comm n a, pow_mul]
      linear_combination ((ϖ : K) ^ a * (r : K)) * hi
    unfold Bd
    rw [this]
    exact R.mul_mem (R.pow_mem hϖ a) r.2
  · linear_combination ((((ϖ⁻¹ : Kˣ) : K) ^ a) ^ n) * hr' + (∏ i, M i i - M.det) * hi

/- English proof (translation)
Take `⟨r, hr⟩` from `hess_two (hs_lift M hM) (hs_lift_hess M h ht hM)`. Establish `hs : ((sg (hs_lift M hM) : R) : K) = sg ((ϖ : K) ^ a • M)`. Use `hs_sg_map R.subtype (hs_lift M hM)` as an intermediate fact. Rewrite `this` using `[hs_lift_map]`. Conclude with `this`.

Establish `hsm` using `hs_sg_smul ((ϖ : K) ^ a) M`. Establish `hr' : ((ϖ : K) ^ a) ^ n * M.det = ((ϖ : K) ^ a) ^ n * ∏ i, M i i - (ϖ : K) ^ a * t * sg ((ϖ : K) ^ a • M) + ((ϖ : K) ^ a * t) ^ 2 * (r : K)`. Use `congrArg (fun x : R => (x : K)) hr` as an intermediate fact. Simplify using `only [Subring.coe_add, Subring.coe_mul, AddSubgroupClass.coe_sub, Subring.coe_pow] at this`. Rewrite `this` using `[hs_lift_det, hs_lift_prod, hs]`.

Conclude with `this`. Establish `hi` using `hs_inv_pow (ϖ := ϖ) a n`. Use `⟨(((ϖ⁻¹ : Kˣ) : K) ^ a) ^ n * (((ϖ : K) ^ a) ^ 2 * (r : K)), ?_, ?_⟩` and prove the remaining obligations. Establish `: (ϖ : K) ^ (n * a) * ((((ϖ⁻¹ : Kˣ) : K) ^ a) ^ n * (((ϖ : K) ^ a) ^ 2 * (r : K))) = ((ϖ : K) ^ a) ^ 2 * (r : K)`. Rewrite using `[mul_comm n a, pow_mul]`.

Take the linear combination `(((ϖ : K) ^ a) ^ 2 * (r : K)) * hi`. Unfold `Bd`. Rewrite using `[this]`. Conclude with `R.mul_mem (R.pow_mem (R.pow_mem hϖ a) 2) r.2`. Take the linear combination `((((ϖ⁻¹ : Kˣ) : K) ^ a) ^ n) * hr' + (∏ i, M i i - t * sg M - M.det) * hi - ((((ϖ⁻¹ : Kˣ) : K) ^ a) ^ n * t) * hsm`.
-/
theorem hess_two_bd (hϖ : (ϖ : K) ∈ R) {n a : ℕ} {t : K} (M : Matrix (Fin n) (Fin n) K)
    (h : IsHess t M) (ht : Bd R ϖ a t) (hM : ∀ i j, Bd R ϖ a (M i j)) :
    ∃ r, Bd R ϖ (n * a) r ∧ M.det = ∏ i, M i i - t * sg M + t ^ 2 * r := by
  obtain ⟨r, hr⟩ := hess_two (hs_lift M hM) (hs_lift_hess M h ht hM)
  have hs : ((sg (hs_lift M hM) : R) : K) = sg ((ϖ : K) ^ a • M) := by
    have := hs_sg_map R.subtype (hs_lift M hM)
    rw [hs_lift_map] at this
    exact this
  have hsm := hs_sg_smul ((ϖ : K) ^ a) M
  have hr' : ((ϖ : K) ^ a) ^ n * M.det =
      ((ϖ : K) ^ a) ^ n * ∏ i, M i i - (ϖ : K) ^ a * t * sg ((ϖ : K) ^ a • M) +
        ((ϖ : K) ^ a * t) ^ 2 * (r : K) := by
    have := congrArg (fun x : R => (x : K)) hr
    simp only [Subring.coe_add, Subring.coe_mul, AddSubgroupClass.coe_sub, Subring.coe_pow] at this
    rw [hs_lift_det, hs_lift_prod, hs] at this
    exact this
  have hi := hs_inv_pow (ϖ := ϖ) a n
  refine ⟨(((ϖ⁻¹ : Kˣ) : K) ^ a) ^ n * (((ϖ : K) ^ a) ^ 2 * (r : K)), ?_, ?_⟩
  · have : (ϖ : K) ^ (n * a) * ((((ϖ⁻¹ : Kˣ) : K) ^ a) ^ n * (((ϖ : K) ^ a) ^ 2 * (r : K))) =
        ((ϖ : K) ^ a) ^ 2 * (r : K) := by
      rw [mul_comm n a, pow_mul]
      linear_combination (((ϖ : K) ^ a) ^ 2 * (r : K)) * hi
    unfold Bd
    rw [this]
    exact R.mul_mem (R.pow_mem (R.pow_mem hϖ a) 2) r.2
  · linear_combination ((((ϖ⁻¹ : Kˣ) : K) ^ a) ^ n) * hr' +
      (∏ i, M i i - t * sg M - M.det) * hi - ((((ϖ⁻¹ : Kˣ) : K) ^ a) ^ n * t) * hsm

/- English proof (translation)
Introduce `i j`. Prove the components needed by the constructor for the conclusion. Introduce `e`. Establish `h1 : i ≠ j` using `by intro h; rw [h] at e; omega`. Establish `h2 : ¬ i < j` using `by rw [Fin.lt_def]; omega`.

Simplify using `[HH, h1, h2, e]`. Introduce `e`. Establish `h1 : i ≠ j` using `by intro h; rw [h] at e; omega`. Establish `h2 : ¬ i < j` using `by rw [Fin.lt_def]; omega`. Establish `h3 : ¬ (j.val + 1 = i.val)` using `by omega`.

Simplify using `[HH, h1, h2, h3]`.
-/
theorem isHess_HH {n : ℕ} (t : K) (d : Fin n → K) (y : Pr n → K) : IsHess t (HH t d y) := by
  intro i j
  constructor
  · intro e
    have h1 : i ≠ j := by intro h; rw [h] at e; omega
    have h2 : ¬ i < j := by rw [Fin.lt_def]; omega
    simp [HH, h1, h2, e]
  · intro e
    have h1 : i ≠ j := by intro h; rw [h] at e; omega
    have h2 : ¬ i < j := by rw [Fin.lt_def]; omega
    have h3 : ¬ (j.val + 1 = i.val) := by omega
    simp [HH, h1, h2, h3]

/- English proof (translation)
Establish `hT : (HH 0 d y).IsUpperTriangular`. Introduce `i j hij`. Establish `hij' : j < i` using `hij`. Establish `h1 : i ≠ j` using `ne_of_gt hij'`. Establish `h2 : ¬ i < j` using `not_lt.2 hij'.le`.

Simplify using `[HH, h1, h2]`. Rewrite using `[Matrix.det_of_isUpperTriangular hT]`. Simplify using `[HH]`.
-/
theorem det_HH_zero {n : ℕ} (d : Fin n → K) (y : Pr n → K) : (HH 0 d y).det = ∏ i, d i := by
  have hT : (HH 0 d y).IsUpperTriangular := by
    intro i j hij
    have hij' : j < i := hij
    have h1 : i ≠ j := ne_of_gt hij'
    have h2 : ¬ i < j := not_lt.2 hij'.le
    simp [HH, h1, h2]
  rw [Matrix.det_of_isUpperTriangular hT]
  simp [HH]

/- English proof (translation)
Establish `h : (ZZ t d y).det = (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤ) * (HH t d y).det`. Use `Matrix.det_permute (Fin.revPerm : Equiv.Perm (Fin n)) (HH t d y)` as an intermediate fact. Conclude with `this`. Break down `Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n))) with e | e` into its components or cases. Use `left`.

Rewrite using `[h, e]`. Simplify using the standard rewrite rules. Use `right`. Rewrite using `[h, e]`. Simplify using the standard rewrite rules.
-/
theorem det_ZZ {n : ℕ} (t : K) (d : Fin n → K) (y : Pr n → K) :
    (ZZ t d y).det = (HH t d y).det ∨ (ZZ t d y).det = -(HH t d y).det := by
  have h : (ZZ t d y).det = (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤ) * (HH t d y).det := by
    have := Matrix.det_permute (Fin.revPerm : Equiv.Perm (Fin n)) (HH t d y)
    exact this
  rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n))) with e | e
  · left; rw [h, e]; simp
  · right; rw [h, e]; simp

def hs_L {m : ℕ} (ξ : Fin m → K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K :=
  fun i j => if i = j then 1 else if i = 0 then Fin.cases 0 (fun k => ξ (Fin.rev k)) j else 0

/- English proof (translation)
Establish `hT : (hs_L ξ).IsUpperTriangular`. Introduce `i j hij`. Establish `hij' : j < i` using `hij`. Establish `h1 : i ≠ j` using `ne_of_gt hij'`. Establish `h2 : i ≠ 0`.

Introduce `h0`. Rewrite `hij'` using `[h0]`. Conclude with `absurd hij' (Fin.not_lt_zero j)`. Simplify using `[hs_L, h1, h2]`. Rewrite using `[Matrix.det_of_isUpperTriangular hT]`.

Simplify using `[hs_L]`.
-/
theorem hs_L_det {m : ℕ} (ξ : Fin m → K) : (hs_L ξ).det = 1 := by
  have hT : (hs_L ξ).IsUpperTriangular := by
    intro i j hij
    have hij' : j < i := hij
    have h1 : i ≠ j := ne_of_gt hij'
    have h2 : i ≠ 0 := by
      intro h0; rw [h0] at hij'; exact absurd hij' (Fin.not_lt_zero j)
    simp [hs_L, h1, h2]
  rw [Matrix.det_of_isUpperTriangular hT]
  simp [hs_L]

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.mul_apply, Fin.sum_univ_succ]`. Use `Fin.cases ?_ (fun i' => ?_) i` and prove the remaining obligations. Establish `h1 : ∀ k : Fin m, hs_L ξ 0 k.succ = ξ (Fin.rev k)`. Introduce `k`.

Establish `: (0 : Fin (m + 1)) ≠ k.succ` using `(Fin.succ_ne_zero k).symm`. Simplify using `[hs_L, this]`. Establish `h0 : hs_L ξ 0 0 = 1` using `by simp [hs_L]`. Simplify using `only [h1, h0, Hm, Fin.cases_zero, Fin.cases_succ, Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_add, one_mul]`. Expand and normalize the polynomial expressions, which then agree.

Establish `h0 : hs_L ξ i'.succ 0 = 0` using `by simp [hs_L, Fin.succ_ne_zero]`. Establish `h1 : ∀ k : Fin m, hs_L ξ i'.succ k.succ = if i' = k then 1 else 0`. Introduce `k`. Simplify using `[hs_L, Fin.succ_ne_zero]`. Simplify using `only [h0, h1, zero_mul, zero_add, Hm, Fin.cases_succ, ite_mul, one_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]`.
-/
theorem hs_L_mul {m : ℕ} (t c : K) (ξ : Fin m → K) (u : Matrix (Fin (m + 1)) (Fin (m + 1)) K) :
    Hm t c ξ u = hs_L ξ * Hm t c 0 u := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_succ]
  refine Fin.cases ?_ (fun i' => ?_) i
  · have h1 : ∀ k : Fin m, hs_L ξ 0 k.succ = ξ (Fin.rev k) := by
      intro k
      have : (0 : Fin (m + 1)) ≠ k.succ := (Fin.succ_ne_zero k).symm
      simp [hs_L, this]
    have h0 : hs_L ξ 0 0 = 1 := by simp [hs_L]
    simp only [h1, h0, Hm, Fin.cases_zero, Fin.cases_succ, Pi.zero_apply, zero_mul,
      Finset.sum_const_zero, zero_add, one_mul]
    ring
  · have h0 : hs_L ξ i'.succ 0 = 0 := by simp [hs_L, Fin.succ_ne_zero]
    have h1 : ∀ k : Fin m, hs_L ξ i'.succ k.succ = if i' = k then 1 else 0 := by
      intro k
      simp [hs_L, Fin.succ_ne_zero]
    simp only [h0, h1, zero_mul, zero_add, Hm, Fin.cases_succ, ite_mul, one_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]

/- English proof (translation)
Rewrite using `[hs_L_mul, Matrix.det_mul, hs_L_det, one_mul, Matrix.det_succ_row_zero, Finset.sum_eq_single (Fin.last m)]`. Establish `hT : ((Hm t c 0 u).submatrix Fin.succ (Fin.last m).succAbove).IsUpperTriangular`. Introduce `i j hij`. Establish `hij' : j < i` using `hij`. Establish `: u i.castSucc j.castSucc = 0` using `hu.1 (by simpa using hij')`.

Simplify using `[Hm, this]`. Rewrite using `[Matrix.det_of_isUpperTriangular hT]`. Simplify using `[Hm, hu.2]`. Expand and normalize the polynomial expressions, which then agree. Introduce `j _ hj`.

Simplify using `[Hm, hj]`. Simplify using the standard rewrite rules.
-/
theorem det_Hm {m : ℕ} (t c : K) (ξ : Fin m → K) (u : Matrix (Fin (m + 1)) (Fin (m + 1)) K)
    (hu : IsUpUni u) : (Hm t c ξ u).det = (-1) ^ m * (c * t ^ m) := by
  rw [hs_L_mul, Matrix.det_mul, hs_L_det, one_mul, Matrix.det_succ_row_zero,
    Finset.sum_eq_single (Fin.last m)]
  · have hT : ((Hm t c 0 u).submatrix Fin.succ (Fin.last m).succAbove).IsUpperTriangular := by
      intro i j hij
      have hij' : j < i := hij
      have : u i.castSucc j.castSucc = 0 := hu.1 (by simpa using hij')
      simp [Hm, this]
    rw [Matrix.det_of_isUpperTriangular hT]
    simp [Hm, hu.2]
    ring
  · intro j _ hj
    simp [Hm, hj]
  · simp

end HS

section E2

variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ} {ϖ : Kˣ} {L₀ Λ₀ : AddSubgroup K} {Q : Set K} {a b : ℕ}

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => simpa using near_one a0`. Consider the case `insert i S hi ih`. Rewrite using `[Finset.prod_insert hi]`. Conclude with `(hf i (Finset.mem_insert_self _ _)).mul ha (ih fun k hk => hf k (Finset.mem_insert_of_mem hk))`.
-/
theorem near_product_closed {ι : Type} {a0 : K} (ha : a0 ∈ R) (S : Finset ι) (f : ι → K)
    (hf : ∀ i ∈ S, Near R a0 (f i)) : Near R a0 (∏ i ∈ S, f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using near_one a0
  | insert i S hi ih =>
    rw [Finset.prod_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).mul ha (ih fun k hk => hf k (Finset.mem_insert_of_mem hk))

/- English proof (translation)
Take `⟨r, hr, rfl⟩` from `hx`. Conclude with `R.add_mem R.one_mem (R.mul_mem ha hr)`.
-/
theorem near_element_integral {a0 x : K} (ha : a0 ∈ R) (hx : Near R a0 x) : x ∈ R := by
  obtain ⟨r, hr, rfl⟩ := hx
  exact R.add_mem R.one_mem (R.mul_mem ha hr)

/- English proof (translation)
Simplify using `[HH]`.
-/
theorem hessenberg_entry_diagonal {n : ℕ} (t : K) (d : Fin n → K) (y : Pr n → K) (i : Fin n) :
    HH t d y i i = d i := by
  simp [HH]

/- English proof (translation)
Establish `h` using `p.2`. Unfold `HH`. Rewrite using `[if_neg h.ne, dif_pos h]`.
-/
theorem hessenberg_entry_above_diagonal {n : ℕ} (t : K) (d : Fin n → K) (y : Pr n → K) (p : Pr n) :
    HH t d y p.1.1 p.1.2 = y p := by
  have h := p.2
  unfold HH
  rw [if_neg h.ne, dif_pos h]

/- English proof (translation)
Simplify using `[ZZ]`.
-/
theorem antidiagonal_hessenberg_reversed_apply {n : ℕ} (t : K) (d : Fin n → K) (y : Pr n → K) (i j : Fin n) :
    ZZ t d y (Fin.rev i) j = HH t d y i j := by
  simp [ZZ]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [HH, Matrix.add_apply, Pi.add_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem hessenberg_add {n : ℕ} (d d' : Fin n → K) (y y' : Pr n → K) :
    HH 0 (d + d') (y + y') = HH 0 d y + HH 0 d' y' := by
  ext i j
  simp only [HH, Matrix.add_apply, Pi.add_apply]
  split_ifs <;> simp

/- English proof (translation)
Unfold `ZZ`. Rewrite using `[hessenberg_add]`. Both sides reduce to the same expression.
-/
theorem antidiagonal_hessenberg_add {n : ℕ} (d d' : Fin n → K) (y y' : Pr n → K) :
    ZZ 0 (d + d') (y + y') = ZZ 0 d y + ZZ 0 d' y' := by
  unfold ZZ
  rw [hessenberg_add]
  rfl

/- English proof (translation)
Simplify using `only [ZZ, HH, Matrix.submatrix_apply, id]`. Use `split_ifs`. Conclude with `hd _`. Conclude with `hy _`. Conclude with `S.zero_mem`.

Conclude with `S.zero_mem`.
-/
theorem antidiagonal_hessenberg_mem_subgroup {n : ℕ} (S : AddSubgroup K) (d : Fin n → K) (y : Pr n → K) (hd : ∀ i, d i ∈ S)
    (hy : ∀ p, y p ∈ S) (i j : Fin n) : ZZ 0 d y i j ∈ S := by
  simp only [ZZ, HH, Matrix.submatrix_apply, id]
  split_ifs
  · exact hd _
  · exact hy _
  · exact S.zero_mem
  · exact S.zero_mem

/- English proof (translation)
Break down `hD' with h | h` into its components or cases. Conclude with `hC.Qi _ h _ (by simp)`. Use `hC.Qi _ h (-((D'⁻¹ : Kˣ) : K)) (by simp)` as an intermediate fact. Simplify using `using this.neg`.
-/
theorem inverse_determinant_bounded (hC : Cst R ϖ L₀ Λ₀ Q a b) (D' : Kˣ) (hD' : (D' : K) ∈ Q ∨ -(D' : K) ∈ Q) :
    Bd R ϖ a ((D'⁻¹ : Kˣ) : K) := by
  rcases hD' with h | h
  · exact hC.Qi _ h _ (by simp)
  · have := hC.Qi _ h (-((D'⁻¹ : Kˣ) : K)) (by simp)
    simpa using this.neg

/- English proof (translation)
Rewrite using `[Fin.prod_univ_succ]`. Simplify using `[xt]`.
-/
theorem product_of_shifted_coordinates {m : ℕ} (D' : K) (x : Fin m → K) :
    ∏ j, xt D' x j = x0 D' x * ∏ k, x k := by
  rw [Fin.prod_univ_succ]
  simp [xt]

/- English proof (translation)
Establish `hϖ` using `hC.adic.mem`. Distinguish the cases in `hU : ∀ k, IsUnit (x k)`. Use `swap`. Conclude with `absurd (by rw [GG, if_neg hU]) h`. Establish `hΦne : Φ (m + 1) (ZZ 0 (xt (D' : K) x) y) ≠ 0`.

Introduce `h0`. Apply `h` to reduce the goal to its premises. Rewrite using `[GG, if_pos hU, h0]`. Simplify using the standard rewrite rules. Establish `hent` using `hΦ.2.1 _ hΦne`.

Establish `hx : ∀ k, x k ∈ L₀`. Introduce `k`. Use `hent (Fin.rev k.succ) k.succ` as an intermediate fact. Rewrite `this` using `[antidiagonal_hessenberg_reversed_apply, hessenberg_entry_diagonal]`. Simplify `this` using `[xt]`.

Establish `hx0 : x0 (D' : K) x ∈ L₀`. Use `hent (Fin.rev 0) 0` as an intermediate fact. Rewrite `this` using `[antidiagonal_hessenberg_reversed_apply, hessenberg_entry_diagonal]`. Simplify `this` using `[xt]`. Establish `hy : ∀ p, y p ∈ L₀`.

Introduce `p`. Use `hent (Fin.rev p.1.1) p.1.2` as an intermediate fact. Rewrite `this` using `[antidiagonal_hessenberg_reversed_apply, hessenberg_entry_above_diagonal]`. Then use the resulting hypothesis. Use `⟨fun k => ⟨hx k, hU k, ?_⟩, hy, hx0⟩` and prove the remaining obligations. Establish `hxe : ∀ k, x k * Ring.inverse (x k) = 1` using `fun k => Ring.mul_inverse_cancel _ (hU k)`.

Establish `hPE : (∏ k, x k) * ∏ k, Ring.inverse (x k) = 1`. Rewrite using `[← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_eq_one fun k _ => hxe k`. Establish `hx0e : x0 (D' : K) x = (D' : K) * ∏ k, Ring.inverse (x k)`. Unfold `x0`.

Rewrite using `[ringInverse_eq hPE]`. Establish `hDD : (D' : K) * ((D'⁻¹ : Kˣ) : K) = 1` using `by simp`. Establish `hsplit : x k * ∏ j ∈ Finset.univ.erase k, x j = ∏ j, x j` using `Finset.mul_prod_erase _ _ (Finset.mem_univ k)`. Establish `hinv : x k * (x0 (D' : K) x * (∏ j ∈ Finset.univ.erase k, x j) * ((D'⁻¹ : Kˣ) : K)) = 1`. Rewrite using `[hx0e]`.

Take the linear combination `((D' : K) * (∏ k, Ring.inverse (x k)) * ((D'⁻¹ : Kˣ) : K)) * hsplit + ((D' : K) * ((D'⁻¹ : Kˣ) : K)) * hPE + hDD`. Rewrite using `[ringInverse_eq hinv]`. Establish `h1 : Bd R ϖ ((Finset.univ.erase k).card * a) (∏ j ∈ Finset.univ.erase k, x j)` using `Bd.prod _ _ fun j _ => hC.L0 _ (hx j)`. Establish `h2` using `((hC.L0 _ hx0).mul h1).mul (inverse_determinant_bounded hC D' hD')`. Use `Bd.mono hϖ ?_ h2` and prove the remaining obligations.

Rewrite using `[Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ, Fintype.card_fin]`. Establish `hm : 1 ≤ m` using `Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le _) k.2)`. Take `⟨m', rfl⟩ : ∃ m', m = m' + 1` from `⟨m - 1, by omega⟩`. Simplify using `only [Nat.add_sub_cancel]`. Put the polynomial expressions in normal form.

Use linear arithmetic over natural numbers and integers.
-/
theorem GG_supp (hC : Cst R ϖ L₀ Λ₀ Q a b) {m : ℕ} (Φ : ∀ n : ℕ, Matrix (Fin n) (Fin n) K → ℂ)
    (hΦ : PhiHyp R (m + 1) L₀ Λ₀ Q Φ) (D' : Kˣ) (hD' : (D' : K) ∈ Q ∨ -(D' : K) ∈ Q)
    (x : Fin m → K) (y : Pr (m + 1) → K) (h : GG R ψ Φ (D' : K) x y ≠ 0) :
    (∀ k, x k ∈ L₀ ∧ IsUnit (x k) ∧ Bd R ϖ ((m + 1) * a) (Ring.inverse (x k))) ∧
      (∀ p, y p ∈ L₀) ∧ x0 (D' : K) x ∈ L₀ := by
  classical
  have hϖ := hC.adic.mem
  by_cases hU : ∀ k, IsUnit (x k)
  swap
  · exact absurd (by rw [GG, if_neg hU]) h
  have hΦne : Φ (m + 1) (ZZ 0 (xt (D' : K) x) y) ≠ 0 := by
    intro h0
    apply h
    rw [GG, if_pos hU, h0]
    simp
  have hent := hΦ.2.1 _ hΦne
  have hx : ∀ k, x k ∈ L₀ := by
    intro k
    have := hent (Fin.rev k.succ) k.succ
    rw [antidiagonal_hessenberg_reversed_apply, hessenberg_entry_diagonal] at this
    simpa [xt] using this
  have hx0 : x0 (D' : K) x ∈ L₀ := by
    have := hent (Fin.rev 0) 0
    rw [antidiagonal_hessenberg_reversed_apply, hessenberg_entry_diagonal] at this
    simpa [xt] using this
  have hy : ∀ p, y p ∈ L₀ := by
    intro p
    have := hent (Fin.rev p.1.1) p.1.2
    rwa [antidiagonal_hessenberg_reversed_apply, hessenberg_entry_above_diagonal] at this
  refine ⟨fun k => ⟨hx k, hU k, ?_⟩, hy, hx0⟩
  have hxe : ∀ k, x k * Ring.inverse (x k) = 1 := fun k => Ring.mul_inverse_cancel _ (hU k)
  have hPE : (∏ k, x k) * ∏ k, Ring.inverse (x k) = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun k _ => hxe k
  have hx0e : x0 (D' : K) x = (D' : K) * ∏ k, Ring.inverse (x k) := by
    unfold x0
    rw [ringInverse_eq hPE]
  have hDD : (D' : K) * ((D'⁻¹ : Kˣ) : K) = 1 := by simp
  have hsplit : x k * ∏ j ∈ Finset.univ.erase k, x j = ∏ j, x j :=
    Finset.mul_prod_erase _ _ (Finset.mem_univ k)
  have hinv : x k * (x0 (D' : K) x * (∏ j ∈ Finset.univ.erase k, x j) * ((D'⁻¹ : Kˣ) : K)) = 1 := by
    rw [hx0e]
    linear_combination ((D' : K) * (∏ k, Ring.inverse (x k)) * ((D'⁻¹ : Kˣ) : K)) * hsplit +
      ((D' : K) * ((D'⁻¹ : Kˣ) : K)) * hPE + hDD
  rw [ringInverse_eq hinv]
  have h1 : Bd R ϖ ((Finset.univ.erase k).card * a) (∏ j ∈ Finset.univ.erase k, x j) :=
    Bd.prod _ _ fun j _ => hC.L0 _ (hx j)
  have h2 := ((hC.L0 _ hx0).mul h1).mul (inverse_determinant_bounded hC D' hD')
  refine Bd.mono hϖ ?_ h2
  rw [Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ, Fintype.card_fin]
  have hm : 1 ≤ m := Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le _) k.2)
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  ring_nf
  omega

/- English proof (translation)
Establish `hA` using `hC.adic`. Establish `hϖ` using `hA.mem`. Take `⟨hx, hy, hx0⟩` from `GG_supp hC Φ hΦ D' hD' x y hG`. Take `⟨a₁, ha₁⟩ : ∃ a₁, a₁ = (m + 1) * a` from `⟨_, rfl⟩`. Rewrite `hl`, `hl'`, `hx` using `[← ha₁]`.

Take `⟨c, hc⟩ : ∃ c, c = b + 2 * a₁ + 2 * a + 1` from `⟨_, rfl⟩`. Establish `hb₁ : b + 3 * a₁ + 2 * a + 1 = c + a₁` using `by omega`. Rewrite `hl`, `hl'` using `[hb₁]`. Take `⟨a0, ha0⟩ : ∃ a0 : K, a0 = μ * (ϖ : K) ^ c` from `⟨_, rfl⟩`. Establish `ha0R : a0 ∈ R` using `by rw [ha0]; exact R.mul_mem hμ (R.pow_mem hϖ c)`.

Establish `ha0I : a0 ∈ I R (ϖ : K)`. Use `⟨μ * (ϖ : K) ^ (b + 2 * a₁ + 2 * a), R.mul_mem hμ (R.pow_mem hϖ _), ?_⟩` and prove the remaining obligations. Rewrite using `[ha0, hc, pow_succ]`. Expand and normalize the polynomial expressions, which then agree. Establish `hsmall : ∀ s ∈ R, Sm R ϖ c (a0 * s)` using `fun s hs => ⟨μ * s, R.mul_mem hμ hs, by rw [ha0]; ring⟩`.

Establish `hlS : ∀ k, Sm R ϖ (c + a₁) (l k)` using `fun k => by`. Take `⟨r, hr, e1⟩` from `hl k`. Conclude with `⟨μ * r, R.mul_mem hμ hr, by rw [e1]; ring⟩`. Establish `hlS' : ∀ p, Sm R ϖ (c + a₁) (l' p)` using `fun p => by`. Take `⟨r, hr, e1⟩` from `hl' p`.

Conclude with `⟨μ * r, R.mul_mem hμ hr, by rw [e1]; ring⟩`. Establish `hU : ∀ k, IsUnit (x k)` using `fun k => (hx k).2.1`. Take `⟨e, he⟩ : ∃ e : Fin m → K, e = fun k => Ring.inverse (x k)` from `⟨_, rfl⟩`. Establish `hxe : ∀ k, x k * e k = 1` using `fun k => by rw [he]; exact Ring.mul_inverse_cancel _ (hU k)`. Establish `heB : ∀ k, Bd R ϖ a₁ (e k)` using `fun k => by rw [he]; exact (hx k).2.2`.

Take `⟨ν, hνd⟩ : ∃ ν : Fin m → K, ν = fun k => 1 + l k * e k` from `⟨_, rfl⟩`. Establish `hν : ∀ k, Near R a0 (ν k)`. Introduce `k`. Take `⟨r, hr, e1⟩` from `hl k`. Use `⟨r * ((ϖ : K) ^ a₁ * e k), R.mul_mem hr (heB k), ?_⟩` and prove the remaining obligations.

Rewrite using `[hνd, ha0]`. Use `show 1 + l k * e k = _`. Rewrite using `[e1, pow_add]`. Expand and normalize the polynomial expressions, which then agree. Use `choose w hw using fun k => hA.near_inv ha0I (hν k)`.

Establish `hx' : ∀ k, (x + l) k = x k * ν k`. Introduce `k`. Rewrite using `[hνd]`. Use `show x k + l k = x k * (1 + l k * e k)`. Take the linear combination `(-(l k)) * hxe k`.

Establish `hx'e : ∀ k, (x + l) k * (e k * w k) = 1`. Introduce `k`. Rewrite using `[hx' k]`. Take the linear combination `(ν k * w k) * hxe k + (hw k).1`. Establish `hU' : ∀ k, IsUnit ((x + l) k)` using `fun k => IsUnit.of_mul_eq_one _ (hx'e k)`.

Establish `hPE : (∏ k, x k) * ∏ k, e k = 1`. Rewrite using `[← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_eq_one fun k _ => hxe k`. Establish `hNW : (∏ k, ν k) * ∏ k, w k = 1`. Rewrite using `[← Finset.prod_mul_distrib]`.

Conclude with `Finset.prod_eq_one fun k _ => (hw k).1`. Establish `hP' : ∏ k, (x + l) k = (∏ k, x k) * ∏ k, ν k`. Rewrite using `[← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_congr rfl fun k _ => hx' k`. Take `⟨P, hP⟩ : ∃ P, P = ∏ k, x k` from `⟨_, rfl⟩`.

Take `⟨E, hE⟩ : ∃ E, E = ∏ k, e k` from `⟨_, rfl⟩`. Take `⟨N, hN⟩ : ∃ N, N = ∏ k, ν k` from `⟨_, rfl⟩`. Take `⟨W, hW⟩ : ∃ W, W = ∏ k, w k` from `⟨_, rfl⟩`. Rewrite `hPE` using `[← hP, ← hE]`. Rewrite `hNW` using `[← hN, ← hW]`.

Rewrite `hP'` using `[← hP, ← hN]`. Establish `hNn : Near R a0 N` using `by rw [hN]; exact near_product_closed ha0R _ _ fun k _ => hν k`. Establish `hWn : Near R a0 W` using `by rw [hW]; exact near_product_closed ha0R _ _ fun k _ => (hw k).2.1`. Establish `hNR` using `near_element_integral ha0R hNn`. Establish `hWR` using `near_element_integral ha0R hWn`.

Establish `hPNEW : P * N * (E * W) = 1` using `by linear_combination (N * W) * hPE + hNW`. Establish `hmod : modK R (P * N) = modK R P`. Rewrite using `[modK_mul_isUnit hA (IsUnit.of_mul_eq_one _ hPE) (IsUnit.of_mul_eq_one _ hNW), modK_unitR hNR hWR hNW, mul_one]`. Establish `hx0e : x0 (D' : K) x = (D' : K) * E`. Unfold `x0`.

Rewrite using `[← hP, ringInverse_eq hPE]`. Establish `hx0e' : x0 (D' : K) (x + l) = (D' : K) * E * W`. Unfold `x0`. Rewrite using `[hP', ringInverse_eq hPNEW]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hx0B : Bd R ϖ a ((D' : K) * E)` using `by rw [← hx0e]; exact hC.L0 _ hx0`. Take `⟨sW, hsW, hWs⟩` from `hWn`. Establish `hDD : (D' : K) * ((D'⁻¹ : Kˣ) : K) = 1` using `by simp`. Establish `hPB : Bd R ϖ (m * a) P`. Rewrite using `[hP]`.

Use `Bd.prod (R := R) (ϖ := ϖ) (k := a) Finset.univ x fun j _ => hC.L0 _ (hx j).1` as an intermediate fact. Simplify using `using this`. Take `⟨et, het⟩ : ∃ et : Fin (m + 1) → K, et = Fin.cons (P * ((D'⁻¹ : Kˣ) : K)) e` from `⟨_, rfl⟩`. Take `⟨wt, hwt⟩ : ∃ wt : Fin (m + 1) → K, wt = Fin.cons N w` from `⟨_, rfl⟩`. Establish `hxt : ∀ j, xt (D' : K) x j * et j = 1`.

Introduce `j`. Rewrite using `[het]`. Use `Fin.cases ?_ (fun k => ?_) j` and prove the remaining obligations. Simplify using `only [xt, Fin.cons_zero]`. Rewrite using `[hx0e]`.

Take the linear combination `((D' : K) * ((D'⁻¹ : Kˣ) : K)) * hPE + hDD`. Simplify using `only [xt, Fin.cons_succ]`. Conclude with `hxe k`. Establish `hxt' : ∀ j, xt (D' : K) (x + l) j * (et j * wt j) = 1`. Introduce `j`.

Rewrite using `[het, hwt]`. Use `Fin.cases ?_ (fun k => ?_) j` and prove the remaining obligations. Simplify using `only [xt, Fin.cons_zero]`. Rewrite using `[hx0e']`. Take the linear combination `((D' : K) * ((D'⁻¹ : Kˣ) : K) * (N * W)) * hPE + ((D' : K) * ((D'⁻¹ : Kˣ) : K)) * hNW + hDD`.

Simplify using `only [xt, Fin.cons_succ]`. Conclude with `hx'e k`. Establish `hetB : ∀ j, Bd R ϖ a₁ (et j)`. Introduce `j`. Rewrite using `[het]`.

Use `Fin.cases ?_ (fun k => ?_) j` and prove the remaining obligations. Simplify using `only [Fin.cons_zero]`. Use `hPB.mul (inverse_determinant_bounded hC D' hD')` as an intermediate fact. Establish `e1 : m * a + a = a₁` using `by rw [ha₁]; ring`. Rewrite `this` using `[e1]`. Then use the resulting hypothesis.

Simplify using `only [Fin.cons_succ]`. Conclude with `heB k`. Establish `hwtn : ∀ j, Near R a0 (wt j)`. Introduce `j`. Rewrite using `[hwt]`.

Use `Fin.cases ?_ (fun k => ?_) j` and prove the remaining obligations. Simplify `hNn` using `only [Fin.cons_zero]`. Simplify `(hw k).2.1` using `only [Fin.cons_succ]`. Establish `hg1 : g1 (D' : K) (x + l) (y + l') = g1 (D' : K) x y + ∑ i : Fin m, ((y (sd i) + l' (sd i)) * (W * wt i.castSucc * wt i.succ) - y (sd i)) * ((D' : K) * E * et i.castSucc * et i.succ)`. Unfold `g1`.

Rewrite using `[hx0e, hx0e', Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[ringInverse_eq (hxt i.castSucc), ringInverse_eq (hxt i.succ), ringInverse_eq (hxt' i.castSucc), ringInverse_eq (hxt' i.succ)]`. Simplify using `only [Pi.add_apply]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hdiff : ∑ i : Fin m, ((y (sd i) + l' (sd i)) * (W * wt i.castSucc * wt i.succ) - y (sd i)) * ((D' : K) * E * et i.castSucc * et i.succ) ∈ R`. Use `R.sum_mem fun i _ => ?_` and prove the remaining obligations. Establish `hlam : Near R a0 (W * wt i.castSucc * wt i.succ)` using `(Near.mul ha0R ⟨sW, hsW, hWs⟩ (hwtn _)).mul ha0R (hwtn _)`. Establish `hlamR` using `near_element_integral ha0R hlam`. Take `⟨s, hs, hlams⟩` from `hlam`.

Establish `hT : Bd R ϖ (a + a₁ + a₁) ((D' : K) * E * et i.castSucc * et i.succ)` using `(hx0B.mul (hetB _)).mul (hetB _)`. Establish `h1 : Sm R ϖ (0 + (a + a₁ + a₁)) (a0 * s * y (sd i))`. Establish `h2 : Sm R ϖ ((b + 2 * a₁ + a + 1) + a) (a0 * s)`. Use `hsmall s hs` as an intermediate fact. Establish `e1 : c = (b + 2 * a₁ + a + 1) + a` using `by omega`.

Rewrite `this` using `[e1]`. Then use the resulting hypothesis. Conclude with `Sm.mono hϖ (by omega) (h2.mul_bd (hC.L0 _ (hy _)))`. Establish `h3 : Sm R ϖ (0 + (a + a₁ + a₁)) (l' (sd i) * (W * wt i.castSucc * wt i.succ))` using `Sm.mono hϖ (by omega) ((hlS' _).mul_mem hlamR)`. Establish `h4` using `((h1.add h3).mul_bd hT)`. Establish `h5` using `sm_zero_iff.1 h4`.

Establish `e2 : (y (sd i) + l' (sd i)) * (W * wt i.castSucc * wt i.succ) - y (sd i) = a0 * s * y (sd i) + l' (sd i) * (W * wt i.castSucc * wt i.succ)`. Establish `: y (sd i) * (W * wt i.castSucc * wt i.succ) = y (sd i) * (1 + a0 * s)` using `by rw [hlams]`. Take the linear combination `this`. Rewrite using `[e2]`. Conclude with `h5`.

Establish `hψ : ψ (g1 (D' : K) (x + l) (y + l')) = ψ (g1 (D' : K) x y)`. Rewrite using `[hg1, AddChar.map_add_eq_mul, psi_R hD hdiff, mul_one]`. Establish `hδ0 : Sm R ϖ b ((D' : K) * E * W - (D' : K) * E)`. Establish `h2 : Sm R ϖ ((b + 2 * a₁ + a + 1) + a) (a0 * sW)`. Use `hsmall sW hsW` as an intermediate fact.

Establish `e1 : c = (b + 2 * a₁ + a + 1) + a` using `by omega`. Rewrite `this` using `[e1]`. Then use the resulting hypothesis. Establish `h3` using `Sm.mono hϖ (show b ≤ b + 2 * a₁ + a + 1 by omega) (h2.mul_bd hx0B)`. Establish `e2 : (D' : K) * E * W - (D' : K) * E = a0 * sW * ((D' : K) * E)` using `by rw [hWs]; ring`. Rewrite using `[e2]`.

Conclude with `h3`. Establish `hΦeq : Φ (m + 1) (ZZ 0 (xt (D' : K) (x + l)) (y + l')) = Φ (m + 1) (ZZ 0 (xt (D' : K) x) y)`. Establish `e1 : xt (D' : K) (x + l) = xt (D' : K) x + (xt (D' : K) (x + l) - xt (D' : K) x)`. Simplify using the standard rewrite rules. Rewrite using `[e1, antidiagonal_hessenberg_add]`.

Use `hΦ.2.2 _ _ ?_ (antidiagonal_hessenberg_mem_subgroup Λ₀ _ _ ?_ ?_)` and prove the remaining obligations. Establish `hp : ∏ j, xt (D' : K) x j = (D' : K)`. Rewrite using `[product_of_shifted_coordinates, hx0e, ← hP]`. Take the linear combination `(D' : K) * hPE`. Apply the tactic sequence `rcases det_ZZ 0 (xt (D' : K) x) y with h | h <;> rw [h, det_HH_zero, hp]`.

Conclude with `hD'`. Rewrite using `[neg_neg]`. Conclude with `hD'.symm`. Introduce `j`. Use `Fin.cases ?_ (fun k => ?_) j` and prove the remaining obligations.

Simplify using `only [Pi.sub_apply, xt, Fin.cons_zero]`. Rewrite using `[hx0e, hx0e']`. Conclude with `hC.abelian₂ _ hδ0`. Simplify using `only [Pi.sub_apply, xt, Fin.cons_succ, Pi.add_apply]`. Rewrite using `[add_sub_cancel_left]`.

Conclude with `hC.abelian₂ _ (Sm.mono hϖ (by omega) (hlS k))`. Introduce `p`. Conclude with `hC.abelian₂ _ (Sm.mono hϖ (by omega) (hlS' p))`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[GG, if_pos hU', GG, if_pos hU, hΦeq, hψ, hP', hmod, hP]`.

Use `choose r hr hlr using hl`. Use `⟨∑ k, (ϖ : K) ^ (c + a₁) * r k + ((ϖ : K) ^ c * ((D' : K) * E)) * sW, ?_, ?_⟩` and prove the remaining obligations. Use `R.add_mem (R.sum_mem fun k _ => R.mul_mem (R.pow_mem hϖ _) (hr k)) (R.mul_mem ?_ hsW)` and prove the remaining obligations. Conclude with `Bd.mono hϖ (by omega) hx0B`. Unfold `g0`.

Rewrite using `[hP', ← hP, ringInverse_eq hPE, ringInverse_eq hPNEW, mul_add, Finset.mul_sum]`. Establish `e3 : ∑ k, (x + l) k = ∑ k, x k + ∑ k, μ * ((ϖ : K) ^ (c + a₁) * r k)`. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Use `show x k + l k = _`.

Rewrite using `[hlr k]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e3, hWs, ha0]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem orbital_integral_change_estimate (hD : LocalDatum K R ψ) (hC : Cst R ϖ L₀ Λ₀ Q a b) (m : ℕ)
    (Φ : ∀ n : ℕ, Matrix (Fin n) (Fin n) K → ℂ) (hΦ : PhiHyp R (m + 1) L₀ Λ₀ Q Φ)
    (D' : Kˣ) (hD' : (D' : K) ∈ Q ∨ -(D' : K) ∈ Q) (μ : K) (hμ : μ ∈ R)
    (x l : Fin m → K) (y l' : Pr (m + 1) → K)
    (hl : ∀ k, ∃ r ∈ R, l k = μ * (ϖ : K) ^ (b + 3 * ((m + 1) * a) + 2 * a + 1) * r)
    (hl' : ∀ p, ∃ r ∈ R, l' p = μ * (ϖ : K) ^ (b + 3 * ((m + 1) * a) + 2 * a + 1) * r)
    (hG : GG R ψ Φ (D' : K) x y ≠ 0) :
    GG R ψ Φ (D' : K) (x + l) (y + l') = GG R ψ Φ (D' : K) x y ∧
      ∃ r ∈ R, g0 (D' : K) (x + l) - g0 (D' : K) x = μ * r := by
  classical
  have hA := hC.adic
  have hϖ := hA.mem
  obtain ⟨hx, hy, hx0⟩ := GG_supp hC Φ hΦ D' hD' x y hG
  obtain ⟨a₁, ha₁⟩ : ∃ a₁, a₁ = (m + 1) * a := ⟨_, rfl⟩
  rw [← ha₁] at hl hl' hx
  obtain ⟨c, hc⟩ : ∃ c, c = b + 2 * a₁ + 2 * a + 1 := ⟨_, rfl⟩
  have hb₁ : b + 3 * a₁ + 2 * a + 1 = c + a₁ := by omega
  rw [hb₁] at hl hl'
  obtain ⟨a0, ha0⟩ : ∃ a0 : K, a0 = μ * (ϖ : K) ^ c := ⟨_, rfl⟩
  have ha0R : a0 ∈ R := by rw [ha0]; exact R.mul_mem hμ (R.pow_mem hϖ c)
  have ha0I : a0 ∈ I R (ϖ : K) := by
    refine ⟨μ * (ϖ : K) ^ (b + 2 * a₁ + 2 * a), R.mul_mem hμ (R.pow_mem hϖ _), ?_⟩
    rw [ha0, hc, pow_succ]; ring
  have hsmall : ∀ s ∈ R, Sm R ϖ c (a0 * s) := fun s hs =>
    ⟨μ * s, R.mul_mem hμ hs, by rw [ha0]; ring⟩
  have hlS : ∀ k, Sm R ϖ (c + a₁) (l k) := fun k => by
    obtain ⟨r, hr, e1⟩ := hl k
    exact ⟨μ * r, R.mul_mem hμ hr, by rw [e1]; ring⟩
  have hlS' : ∀ p, Sm R ϖ (c + a₁) (l' p) := fun p => by
    obtain ⟨r, hr, e1⟩ := hl' p
    exact ⟨μ * r, R.mul_mem hμ hr, by rw [e1]; ring⟩
  have hU : ∀ k, IsUnit (x k) := fun k => (hx k).2.1
  obtain ⟨e, he⟩ : ∃ e : Fin m → K, e = fun k => Ring.inverse (x k) := ⟨_, rfl⟩
  have hxe : ∀ k, x k * e k = 1 := fun k => by rw [he]; exact Ring.mul_inverse_cancel _ (hU k)
  have heB : ∀ k, Bd R ϖ a₁ (e k) := fun k => by rw [he]; exact (hx k).2.2
  obtain ⟨ν, hνd⟩ : ∃ ν : Fin m → K, ν = fun k => 1 + l k * e k := ⟨_, rfl⟩
  have hν : ∀ k, Near R a0 (ν k) := by
    intro k
    obtain ⟨r, hr, e1⟩ := hl k
    refine ⟨r * ((ϖ : K) ^ a₁ * e k), R.mul_mem hr (heB k), ?_⟩
    rw [hνd, ha0]
    show 1 + l k * e k = _
    rw [e1, pow_add]; ring
  choose w hw using fun k => hA.near_inv ha0I (hν k)
  have hx' : ∀ k, (x + l) k = x k * ν k := by
    intro k
    rw [hνd]
    show x k + l k = x k * (1 + l k * e k)
    linear_combination (-(l k)) * hxe k
  have hx'e : ∀ k, (x + l) k * (e k * w k) = 1 := by
    intro k
    rw [hx' k]
    linear_combination (ν k * w k) * hxe k + (hw k).1
  have hU' : ∀ k, IsUnit ((x + l) k) := fun k => IsUnit.of_mul_eq_one _ (hx'e k)

  have hPE : (∏ k, x k) * ∏ k, e k = 1 := by
    rw [← Finset.prod_mul_distrib]; exact Finset.prod_eq_one fun k _ => hxe k
  have hNW : (∏ k, ν k) * ∏ k, w k = 1 := by
    rw [← Finset.prod_mul_distrib]; exact Finset.prod_eq_one fun k _ => (hw k).1
  have hP' : ∏ k, (x + l) k = (∏ k, x k) * ∏ k, ν k := by
    rw [← Finset.prod_mul_distrib]; exact Finset.prod_congr rfl fun k _ => hx' k
  obtain ⟨P, hP⟩ : ∃ P, P = ∏ k, x k := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E, E = ∏ k, e k := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N, N = ∏ k, ν k := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W, W = ∏ k, w k := ⟨_, rfl⟩
  rw [← hP, ← hE] at hPE
  rw [← hN, ← hW] at hNW
  rw [← hP, ← hN] at hP'
  have hNn : Near R a0 N := by rw [hN]; exact near_product_closed ha0R _ _ fun k _ => hν k
  have hWn : Near R a0 W := by rw [hW]; exact near_product_closed ha0R _ _ fun k _ => (hw k).2.1
  have hNR := near_element_integral ha0R hNn
  have hWR := near_element_integral ha0R hWn
  have hPNEW : P * N * (E * W) = 1 := by linear_combination (N * W) * hPE + hNW
  have hmod : modK R (P * N) = modK R P := by
    rw [modK_mul_isUnit hA (IsUnit.of_mul_eq_one _ hPE) (IsUnit.of_mul_eq_one _ hNW),
      modK_unitR hNR hWR hNW, mul_one]
  have hx0e : x0 (D' : K) x = (D' : K) * E := by
    unfold x0; rw [← hP, ringInverse_eq hPE]
  have hx0e' : x0 (D' : K) (x + l) = (D' : K) * E * W := by
    unfold x0; rw [hP', ringInverse_eq hPNEW]; ring
  have hx0B : Bd R ϖ a ((D' : K) * E) := by rw [← hx0e]; exact hC.L0 _ hx0
  obtain ⟨sW, hsW, hWs⟩ := hWn
  have hDD : (D' : K) * ((D'⁻¹ : Kˣ) : K) = 1 := by simp
  have hPB : Bd R ϖ (m * a) P := by
    rw [hP]
    have := Bd.prod (R := R) (ϖ := ϖ) (k := a) Finset.univ x fun j _ => hC.L0 _ (hx j).1
    simpa using this

  obtain ⟨et, het⟩ : ∃ et : Fin (m + 1) → K, et = Fin.cons (P * ((D'⁻¹ : Kˣ) : K)) e := ⟨_, rfl⟩
  obtain ⟨wt, hwt⟩ : ∃ wt : Fin (m + 1) → K, wt = Fin.cons N w := ⟨_, rfl⟩
  have hxt : ∀ j, xt (D' : K) x j * et j = 1 := by
    intro j
    rw [het]
    refine Fin.cases ?_ (fun k => ?_) j
    · simp only [xt, Fin.cons_zero]
      rw [hx0e]
      linear_combination ((D' : K) * ((D'⁻¹ : Kˣ) : K)) * hPE + hDD
    · simp only [xt, Fin.cons_succ]
      exact hxe k
  have hxt' : ∀ j, xt (D' : K) (x + l) j * (et j * wt j) = 1 := by
    intro j
    rw [het, hwt]
    refine Fin.cases ?_ (fun k => ?_) j
    · simp only [xt, Fin.cons_zero]
      rw [hx0e']
      linear_combination ((D' : K) * ((D'⁻¹ : Kˣ) : K) * (N * W)) * hPE +
        ((D' : K) * ((D'⁻¹ : Kˣ) : K)) * hNW + hDD
    · simp only [xt, Fin.cons_succ]
      exact hx'e k
  have hetB : ∀ j, Bd R ϖ a₁ (et j) := by
    intro j
    rw [het]
    refine Fin.cases ?_ (fun k => ?_) j
    · simp only [Fin.cons_zero]
      have := hPB.mul (inverse_determinant_bounded hC D' hD')
      have e1 : m * a + a = a₁ := by rw [ha₁]; ring
      rwa [e1] at this
    · simp only [Fin.cons_succ]
      exact heB k
  have hwtn : ∀ j, Near R a0 (wt j) := by
    intro j
    rw [hwt]
    refine Fin.cases ?_ (fun k => ?_) j
    · simpa only [Fin.cons_zero] using hNn
    · simpa only [Fin.cons_succ] using (hw k).2.1

  have hg1 : g1 (D' : K) (x + l) (y + l') = g1 (D' : K) x y +
      ∑ i : Fin m, ((y (sd i) + l' (sd i)) * (W * wt i.castSucc * wt i.succ) - y (sd i)) *
        ((D' : K) * E * et i.castSucc * et i.succ) := by
    unfold g1
    rw [hx0e, hx0e', Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ringInverse_eq (hxt i.castSucc), ringInverse_eq (hxt i.succ),
      ringInverse_eq (hxt' i.castSucc), ringInverse_eq (hxt' i.succ)]
    simp only [Pi.add_apply]
    ring
  have hdiff : ∑ i : Fin m, ((y (sd i) + l' (sd i)) * (W * wt i.castSucc * wt i.succ) - y (sd i)) *
        ((D' : K) * E * et i.castSucc * et i.succ) ∈ R := by
    refine R.sum_mem fun i _ => ?_
    have hlam : Near R a0 (W * wt i.castSucc * wt i.succ) :=
      (Near.mul ha0R ⟨sW, hsW, hWs⟩ (hwtn _)).mul ha0R (hwtn _)
    have hlamR := near_element_integral ha0R hlam
    obtain ⟨s, hs, hlams⟩ := hlam
    have hT : Bd R ϖ (a + a₁ + a₁) ((D' : K) * E * et i.castSucc * et i.succ) :=
      (hx0B.mul (hetB _)).mul (hetB _)
    have h1 : Sm R ϖ (0 + (a + a₁ + a₁)) (a0 * s * y (sd i)) := by
      have h2 : Sm R ϖ ((b + 2 * a₁ + a + 1) + a) (a0 * s) := by
        have := hsmall s hs
        have e1 : c = (b + 2 * a₁ + a + 1) + a := by omega
        rwa [e1] at this
      exact Sm.mono hϖ (by omega) (h2.mul_bd (hC.L0 _ (hy _)))
    have h3 : Sm R ϖ (0 + (a + a₁ + a₁)) (l' (sd i) * (W * wt i.castSucc * wt i.succ)) :=
      Sm.mono hϖ (by omega) ((hlS' _).mul_mem hlamR)
    have h4 := ((h1.add h3).mul_bd hT)
    have h5 := sm_zero_iff.1 h4
    have e2 : (y (sd i) + l' (sd i)) * (W * wt i.castSucc * wt i.succ) - y (sd i) =
        a0 * s * y (sd i) + l' (sd i) * (W * wt i.castSucc * wt i.succ) := by
      have : y (sd i) * (W * wt i.castSucc * wt i.succ) = y (sd i) * (1 + a0 * s) := by rw [hlams]
      linear_combination this
    rw [e2]
    exact h5
  have hψ : ψ (g1 (D' : K) (x + l) (y + l')) = ψ (g1 (D' : K) x y) := by
    rw [hg1, AddChar.map_add_eq_mul, psi_R hD hdiff, mul_one]

  have hδ0 : Sm R ϖ b ((D' : K) * E * W - (D' : K) * E) := by
    have h2 : Sm R ϖ ((b + 2 * a₁ + a + 1) + a) (a0 * sW) := by
      have := hsmall sW hsW
      have e1 : c = (b + 2 * a₁ + a + 1) + a := by omega
      rwa [e1] at this
    have h3 := Sm.mono hϖ (show b ≤ b + 2 * a₁ + a + 1 by omega) (h2.mul_bd hx0B)
    have e2 : (D' : K) * E * W - (D' : K) * E = a0 * sW * ((D' : K) * E) := by rw [hWs]; ring
    rw [e2]; exact h3
  have hΦeq : Φ (m + 1) (ZZ 0 (xt (D' : K) (x + l)) (y + l')) =
      Φ (m + 1) (ZZ 0 (xt (D' : K) x) y) := by
    have e1 : xt (D' : K) (x + l) = xt (D' : K) x + (xt (D' : K) (x + l) - xt (D' : K) x) := by
      simp
    rw [e1, antidiagonal_hessenberg_add]
    refine hΦ.2.2 _ _ ?_ (antidiagonal_hessenberg_mem_subgroup Λ₀ _ _ ?_ ?_)
    · have hp : ∏ j, xt (D' : K) x j = (D' : K) := by
        rw [product_of_shifted_coordinates, hx0e, ← hP]
        linear_combination (D' : K) * hPE
      rcases det_ZZ 0 (xt (D' : K) x) y with h | h <;> rw [h, det_HH_zero, hp]
      · exact hD'
      · rw [neg_neg]; exact hD'.symm
    · intro j
      refine Fin.cases ?_ (fun k => ?_) j
      · simp only [Pi.sub_apply, xt, Fin.cons_zero]
        rw [hx0e, hx0e']
        exact hC.abelian₂ _ hδ0
      · simp only [Pi.sub_apply, xt, Fin.cons_succ, Pi.add_apply]
        rw [add_sub_cancel_left]
        exact hC.abelian₂ _ (Sm.mono hϖ (by omega) (hlS k))
    · intro p
      exact hC.abelian₂ _ (Sm.mono hϖ (by omega) (hlS' p))
  refine ⟨?_, ?_⟩
  · rw [GG, if_pos hU', GG, if_pos hU, hΦeq, hψ, hP', hmod, hP]
  · choose r hr hlr using hl
    refine ⟨∑ k, (ϖ : K) ^ (c + a₁) * r k + ((ϖ : K) ^ c * ((D' : K) * E)) * sW, ?_, ?_⟩
    · refine R.add_mem (R.sum_mem fun k _ => R.mul_mem (R.pow_mem hϖ _) (hr k)) (R.mul_mem ?_ hsW)
      exact Bd.mono hϖ (by omega) hx0B
    · unfold g0
      rw [hP', ← hP, ringInverse_eq hPE, ringInverse_eq hPNEW, mul_add, Finset.mul_sum]
      have e3 : ∑ k, (x + l) k = ∑ k, x k + ∑ k, μ * ((ϖ : K) ^ (c + a₁) * r k) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        show x k + l k = _
        rw [hlr k]; ring
      rw [e3, hWs, ha0]
      ring

/- English proof (translation)
Use `⟨b + 3 * ((m + 1) * a) + 2 * a + 1, fun Φ hΦ D' hD' μ hμ x l y l' hl hl' => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hG : GG R ψ Φ (D' : K) x y = 0`. Use `⟨?_, fun h => absurd hG h⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Establish `hG' : GG R ψ Φ (D' : K) (x + l) (y + l') ≠ 0` using `by rwa [hG] at hne`.

Establish `key` using `(orbital_integral_change_estimate hD hC m Φ hΦ D' hD' μ hμ (x + l) (-l) (y + l') (-l') (fun k => by`. Take `⟨r, hr, e⟩` from `hl k`. Conclude with `⟨-r, R.neg_mem hr, by show -(l k) = _; rw [e]; ring⟩)`. Use the proof step `(fun p => by`. Take `⟨r, hr, e⟩` from `hl' p`.

Conclude with `⟨-r, R.neg_mem hr, by show -(l' p) = _; rw [e]; ring⟩) hG').1`. Rewrite `key` using `[add_neg_cancel_right, add_neg_cancel_right]`. Conclude with `hne key.symm`. Take `⟨h1, h2⟩` from `orbital_integral_change_estimate hD hC m Φ hΦ D' hD' μ hμ x l y l' hl hl' hG`. Conclude with `⟨h1, fun _ => h2⟩`.
-/
theorem GG_inv (hD : LocalDatum K R ψ) (hC : Cst R ϖ L₀ Λ₀ Q a b) (m : ℕ) :
    ∃ b₁ : ℕ, ∀ Φ : ∀ n : ℕ, Matrix (Fin n) (Fin n) K → ℂ, PhiHyp R (m + 1) L₀ Λ₀ Q Φ →
    ∀ D' : Kˣ, ((D' : K) ∈ Q ∨ -(D' : K) ∈ Q) → ∀ μ ∈ R,
    ∀ (x l : Fin m → K) (y l' : Pr (m + 1) → K),
      (∀ k, ∃ r ∈ R, l k = μ * (ϖ : K) ^ b₁ * r) → (∀ p, ∃ r ∈ R, l' p = μ * (ϖ : K) ^ b₁ * r) →
      GG R ψ Φ (D' : K) (x + l) (y + l') = GG R ψ Φ (D' : K) x y ∧
      (GG R ψ Φ (D' : K) x y ≠ 0 → ∃ r ∈ R, g0 (D' : K) (x + l) - g0 (D' : K) x = μ * r) := by
  refine ⟨b + 3 * ((m + 1) * a) + 2 * a + 1, fun Φ hΦ D' hD' μ hμ x l y l' hl hl' => ?_⟩
  by_cases hG : GG R ψ Φ (D' : K) x y = 0
  · refine ⟨?_, fun h => absurd hG h⟩
    by_contra hne
    have hG' : GG R ψ Φ (D' : K) (x + l) (y + l') ≠ 0 := by rwa [hG] at hne
    have key := (orbital_integral_change_estimate hD hC m Φ hΦ D' hD' μ hμ (x + l) (-l) (y + l') (-l')
      (fun k => by
        obtain ⟨r, hr, e⟩ := hl k
        exact ⟨-r, R.neg_mem hr, by show -(l k) = _; rw [e]; ring⟩)
      (fun p => by
        obtain ⟨r, hr, e⟩ := hl' p
        exact ⟨-r, R.neg_mem hr, by show -(l' p) = _; rw [e]; ring⟩) hG').1
    rw [add_neg_cancel_right, add_neg_cancel_right] at key
    exact hne key.symm
  · obtain ⟨h1, h2⟩ := orbital_integral_change_estimate hD hC m Φ hΦ D' hD' μ hμ x l y l' hl hl' hG
    exact ⟨h1, fun _ => h2⟩

end E2

section P2

variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ} {ϖ : Kˣ} {L₀ Λ₀ : AddSubgroup K} {Q : Set K} {a b : ℕ}

/- English proof (translation)
Simplify using `[HH]`.
-/
theorem hessenberg_diagonal_entry {n : ℕ} (t : K) (d : Fin n → K) (y : Pr n → K) (i : Fin n) :
    HH t d y i i = d i := by simp [HH]

/- English proof (translation)
Simplify using `[HH, h, ne_of_lt h]`.
-/
theorem hessenberg_entry_upper {n : ℕ} (t : K) (d : Fin n → K) (y : Pr n → K) {i j : Fin n} (h : i < j) :
    HH t d y i j = y ⟨(i, j), h⟩ := by
  simp [HH, h, ne_of_lt h]

/- English proof (translation)
Introduce `i j`. Conclude with `⟨fun e => (h i.succ j.succ).1 (by simp only [Fin.val_succ]; omega), fun e => (h i.succ j.succ).2 (by simp only [Fin.val_succ]; omega)⟩`.
-/
theorem hessenberg_submatrix_tail {A : Type} [CommRing A] {n : ℕ} {t : A}
    {M : Matrix (Fin (n + 1)) (Fin (n + 1)) A} (h : IsHess t M) :
    IsHess t (M.submatrix Fin.succ Fin.succ) := by
  intro i j
  exact ⟨fun e => (h i.succ j.succ).1 (by simp only [Fin.val_succ]; omega),
    fun e => (h i.succ j.succ).2 (by simp only [Fin.val_succ]; omega)⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem succ_above_one_zero {n : ℕ} : Fin.succAbove (1 : Fin (n + 2)) (0 : Fin (n + 1)) = 0 := by
  rfl

/- English proof (translation)
Rewrite using `[← Fin.succ_zero_eq_one, Fin.succ_succAbove_succ, Fin.zero_succAbove]`.
-/
theorem succ_above_one_succ {n : ℕ} (i : Fin n) :
    Fin.succAbove (1 : Fin (n + 2)) i.succ = i.succ.succ := by
  rw [← Fin.succ_zero_eq_one, Fin.succ_succAbove_succ, Fin.zero_succAbove]

/- English proof (translation)
Introduce `i j`. Use `Fin.cases ?_ (fun i' => ?_) i` and prove the remaining obligations. Conclude with `⟨fun e => by simp at e, fun e => by simp at e⟩`. Simplify using `only [Matrix.submatrix_apply, succ_above_one_succ]`. Conclude with `⟨fun e => (h i'.succ.succ j.succ).1 (by simp only [Fin.val_succ] at e ⊢; omega), fun e => (h i'.succ.succ j.succ).2 (by simp only [Fin.val_succ] at e ⊢; omega)⟩`.
-/
theorem hessenberg_submatrix_above_one {A : Type} [CommRing A] {n : ℕ} {t : A}
    {M : Matrix (Fin (n + 2)) (Fin (n + 2)) A} (h : IsHess t M) :
    IsHess t (M.submatrix (Fin.succAbove 1) Fin.succ) := by
  intro i j
  refine Fin.cases ?_ (fun i' => ?_) i
  · exact ⟨fun e => by simp at e, fun e => by simp at e⟩
  · simp only [Matrix.submatrix_apply, succ_above_one_succ]
    exact ⟨fun e => (h i'.succ.succ j.succ).1 (by simp only [Fin.val_succ] at e ⊢; omega),
      fun e => (h i'.succ.succ j.succ).2 (by simp only [Fin.val_succ] at e ⊢; omega)⟩

/- English proof (translation)
Break down `h with h | h` into its components or cases. Conclude with `⟨hC.Qb _ h, hC.Qi _ h _ (by simp)⟩`. Use `⟨by simpa using (hC.Qb _ h).neg, ?_⟩` and prove the remaining obligations. Use `hC.Qi _ h (-((D'⁻¹ : Kˣ) : K)) (by simp)` as an intermediate fact. Simplify using `using this.neg`.
-/
theorem determinant_and_inverse_bounded (hC : Cst R ϖ L₀ Λ₀ Q a b) (D' : Kˣ) (h : (D' : K) ∈ Q ∨ -(D' : K) ∈ Q) :
    Bd R ϖ a (D' : K) ∧ Bd R ϖ a ((D'⁻¹ : Kˣ) : K) := by
  rcases h with h | h
  · exact ⟨hC.Qb _ h, hC.Qi _ h _ (by simp)⟩
  · refine ⟨by simpa using (hC.Qb _ h).neg, ?_⟩
    have := hC.Qi _ h (-((D'⁻¹ : Kˣ) : K)) (by simp)
    simpa using this.neg

/- English proof (translation)
Unfold `HH`. Use `split_ifs with h1 h2 h3`. Rewrite using `[h1, Fin.cons_succ]`. Conclude with `hx j`. Conclude with `hy h2`.

Conclude with `ht`. Conclude with `Bd.of_mem hϖ R.zero_mem a`.
-/
theorem hessenberg_entry_bounded (hϖ : (ϖ : K) ∈ R) {m : ℕ} {t ρ : K} {x : Fin m → K} {y : Pr (m + 1) → K}
    (ht : Bd R ϖ a t) (hx : ∀ k, Bd R ϖ a (x k)) (i : Fin (m + 1)) (j : Fin m)
    (hy : ∀ h : i < j.succ, Bd R ϖ a (y ⟨(i, j.succ), h⟩)) :
    Bd R ϖ a (HH t (Fin.cons ρ x : Fin (m + 1) → K) y i j.succ) := by
  unfold HH
  split_ifs with h1 h2 h3
  · rw [h1, Fin.cons_succ]; exact hx j
  · exact hy h2
  · exact ht
  · exact Bd.of_mem hϖ R.zero_mem a

/- English proof (translation)
Use `⟨(1 + a) + (m + 1) * a, ?_⟩` and prove the remaining obligations. Introduce `t ht D' hD' ρ x y hρ hx hy hdet k`. Establish `hϖ` using `hC.adic.mem`. Take `⟨hDb, hDi⟩` from `determinant_and_inverse_bounded hC D' hD'`. Establish `htb : Bd R ϖ a t` using `ht.bd hϖ a`.

Establish `hd : ∀ i, Bd R ϖ a ((Fin.cons ρ x : Fin (m + 1) → K) i)`. Introduce `i`. Use `Fin.cases ?_ (fun i' => ?_) i` and prove the remaining obligations. Simplify using `using hC.L0 _ hρ`. Simplify using `using hC.L0 _ (hx i')`.

Establish `hent : ∀ i j, Bd R ϖ a (HH t (Fin.cons ρ x : Fin (m + 1) → K) y i j)`. Introduce `i j`. Unfold `HH`. Use `split_ifs with h1 h2 h3`. Conclude with `hd i`.

Conclude with `hC.L0 _ (hy _)`. Conclude with `htb`. Conclude with `Bd.of_mem hϖ R.zero_mem a`. Take `⟨r, hr, e⟩` from `hess_one_bd hϖ _ (isHess_HH t (Fin.cons ρ x : Fin (m + 1) → K) y) htb hent`. Establish `hprod : ∏ i, HH t (Fin.cons ρ x : Fin (m + 1) → K) y i i = ρ * ∏ k, x k`.

Simplify using `only [hessenberg_diagonal_entry, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]`. Rewrite `e` using `[hdet, hprod]`. Establish `hε : Sm R ϖ 1 (-(t * r * ((D'⁻¹ : Kˣ) : K)))` using `((ht.mul_bd hr).mul_bd hDi).neg`. Take `⟨v, hv, ev, -⟩` from `Sm.one_add_inv hC.adic le_rfl hε`. Establish `hDD : (D' : K) * ((D'⁻¹ : Kˣ) : K) = 1` using `by simp`.

Establish `key : ρ * (∏ k, x k) * ((D'⁻¹ : Kˣ) : K) * v = 1`. Take the linear combination `ev - ((D'⁻¹ : Kˣ) : K) * v * e + v * hDD`. Establish `hP : x k * ∏ j ∈ Finset.univ.erase k, x j = ∏ j, x j` using `Finset.mul_prod_erase _ _ (Finset.mem_univ k)`. Establish `hinv : x k * (ρ * (∏ j ∈ Finset.univ.erase k, x j) * ((D'⁻¹ : Kˣ) : K) * v) = 1`. Rewrite `key` using `[← hP]`.

Take the linear combination `key`. Use `⟨IsUnit.of_mul_eq_one _ hinv, ?_⟩` and prove the remaining obligations. Rewrite using `[ringInverse_eq hinv]`. Establish `hb` using `(((hC.L0 _ hρ).mul (Bd.prod (Finset.univ.erase k) x (fun j _ => hC.L0 _ (hx j)))).mul hDi).mul_mem hv`. Rewrite `hb` using `[Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ, Fintype.card_fin]`.

Use `Bd.mono hϖ (le_of_eq ?_) hb` and prove the remaining obligations. Establish `h1 : (m - 1) + 1 = m` using `by have := k.2; omega`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem pw_units (hC : Cst R ϖ L₀ Λ₀ Q a b) (m : ℕ) :
    ∃ M₁ : ℕ, ∀ t : K, Sm R ϖ M₁ t → ∀ D' : Kˣ, ((D' : K) ∈ Q ∨ -(D' : K) ∈ Q) →
    ∀ (ρ : K) (x : Fin m → K) (y : Pr (m + 1) → K), ρ ∈ L₀ → (∀ k, x k ∈ L₀) → (∀ p, y p ∈ L₀) →
      (HH t (Fin.cons ρ x : Fin (m + 1) → K) y).det = (D' : K) →
      ∀ k, IsUnit (x k) ∧ Bd R ϖ ((m + 1) * a) (Ring.inverse (x k)) := by
  refine ⟨(1 + a) + (m + 1) * a, ?_⟩
  intro t ht D' hD' ρ x y hρ hx hy hdet k
  have hϖ := hC.adic.mem
  obtain ⟨hDb, hDi⟩ := determinant_and_inverse_bounded hC D' hD'
  have htb : Bd R ϖ a t := ht.bd hϖ a
  have hd : ∀ i, Bd R ϖ a ((Fin.cons ρ x : Fin (m + 1) → K) i) := by
    intro i
    refine Fin.cases ?_ (fun i' => ?_) i
    · simpa using hC.L0 _ hρ
    · simpa using hC.L0 _ (hx i')
  have hent : ∀ i j, Bd R ϖ a (HH t (Fin.cons ρ x : Fin (m + 1) → K) y i j) := by
    intro i j
    unfold HH
    split_ifs with h1 h2 h3
    · exact hd i
    · exact hC.L0 _ (hy _)
    · exact htb
    · exact Bd.of_mem hϖ R.zero_mem a
  obtain ⟨r, hr, e⟩ := hess_one_bd hϖ _ (isHess_HH t (Fin.cons ρ x : Fin (m + 1) → K) y) htb hent
  have hprod : ∏ i, HH t (Fin.cons ρ x : Fin (m + 1) → K) y i i = ρ * ∏ k, x k := by
    simp only [hessenberg_diagonal_entry, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  rw [hdet, hprod] at e
  have hε : Sm R ϖ 1 (-(t * r * ((D'⁻¹ : Kˣ) : K))) := ((ht.mul_bd hr).mul_bd hDi).neg
  obtain ⟨v, hv, ev, -⟩ := Sm.one_add_inv hC.adic le_rfl hε
  have hDD : (D' : K) * ((D'⁻¹ : Kˣ) : K) = 1 := by simp
  have key : ρ * (∏ k, x k) * ((D'⁻¹ : Kˣ) : K) * v = 1 := by
    linear_combination ev - ((D'⁻¹ : Kˣ) : K) * v * e + v * hDD
  have hP : x k * ∏ j ∈ Finset.univ.erase k, x j = ∏ j, x j :=
    Finset.mul_prod_erase _ _ (Finset.mem_univ k)
  have hinv : x k * (ρ * (∏ j ∈ Finset.univ.erase k, x j) * ((D'⁻¹ : Kˣ) : K) * v) = 1 := by
    rw [← hP] at key; linear_combination key
  refine ⟨IsUnit.of_mul_eq_one _ hinv, ?_⟩
  rw [ringInverse_eq hinv]
  have hb := (((hC.L0 _ hρ).mul (Bd.prod (Finset.univ.erase k) x
    (fun j _ => hC.L0 _ (hx j)))).mul hDi).mul_mem hv
  rw [Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ, Fintype.card_fin] at hb
  refine Bd.mono hϖ (le_of_eq ?_) hb
  have h1 : (m - 1) + 1 = m := by have := k.2; omega
  calc a + (m - 1) * a + a = ((m - 1) + 1 + 1) * a := by ring
    _ = (m + 1) * a := by rw [h1]

/- English proof (translation)
Establish `hP : IsUnit (∏ k, x k)`. Establish `hPP : (∏ k, x k) * ∏ k, Ring.inverse (x k) = 1`. Rewrite using `[← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_eq_one fun k _ => Ring.mul_inverse_cancel _ (hx k)`. Conclude with `IsUnit.of_mul_eq_one _ hPP`.

Establish `hX : IsUnit (x0 (D' : K) x)`. Unfold `x0`. Conclude with `D'.isUnit.mul (by`. Take `⟨u, hu⟩` from `hP`. Rewrite using `[← hu, Ring.inverse_unit]`.

Conclude with `(u⁻¹).isUnit)`. Establish `h1` using `Ring.mul_inverse_cancel _ hX`. Unfold `g1`. Rewrite using `[Fin.sum_univ_succ]`. Simplify using `only [xt, Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ, ← Fin.succ_castSucc]`.

Take the linear combination `(y (sd 0) * Ring.inverse (x 0)) * h1`.
-/
theorem first_coordinate_formula {n : ℕ} (D' : Kˣ) (x : Fin (n + 1) → K) (y : Pr (n + 1 + 1) → K)
    (hx : ∀ k, IsUnit (x k)) :
    g1 (D' : K) x y = y (sd 0) * Ring.inverse (x 0) +
      x0 (D' : K) x * ∑ i : Fin n, y (sd i.succ) * Ring.inverse (x i.castSucc) *
        Ring.inverse (x i.succ) := by
  have hP : IsUnit (∏ k, x k) := by
    have hPP : (∏ k, x k) * ∏ k, Ring.inverse (x k) = 1 := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one fun k _ => Ring.mul_inverse_cancel _ (hx k)
    exact IsUnit.of_mul_eq_one _ hPP
  have hX : IsUnit (x0 (D' : K) x) := by
    unfold x0
    exact D'.isUnit.mul (by
      obtain ⟨u, hu⟩ := hP
      rw [← hu, Ring.inverse_unit]; exact (u⁻¹).isUnit)
  have h1 := Ring.mul_inverse_cancel _ hX
  unfold g1
  rw [Fin.sum_univ_succ]
  simp only [xt, Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ, ← Fin.succ_castSucc]
  linear_combination (y (sd 0) * Ring.inverse (x 0)) * h1

/- English proof (translation)
Take `⟨n, rfl⟩ : ∃ n, m = n + 1` from `⟨m - 1, by omega⟩`. Take `⟨a₁, ha₁⟩ : ∃ a₁, a₁ = (n + 1 + 1) * a` from `⟨_, rfl⟩`. Take `⟨B, hB⟩ : ∃ B, B = a + (n + 1) * a + (n + 1) * a₁ + 2 * a₁` from `⟨_, rfl⟩`. Use `⟨b + 3 * B + 1, ?_⟩` and prove the remaining obligations. Introduce `t ht D' hD' ρ x y hx hy hdet`.

Rewrite `hx` using `[← ha₁]`. Establish `hϖ` using `hC.adic.mem`. Take `⟨hDb, hDi⟩` from `determinant_and_inverse_bounded hC D' hD'`. Establish `htb : Bd R ϖ a (t : K)` using `ht.bd hϖ a`. Establish `htR : (t : K) ∈ R` using `ht.mem hϖ`.

Establish `hxb : ∀ k, Bd R ϖ a (x k)` using `fun k => hC.L0 _ (hx k).1`. Establish `hyb : ∀ p, Bd R ϖ a (y p)` using `fun p => hC.L0 _ (hy p)`. Establish `hHess` using `isHess_HH (t : K) (Fin.cons ρ x : Fin (n + 1 + 1) → K) y`. Establish `lap` using `hess_laplace _ hHess`. Rewrite `lap` using `[hdet, hessenberg_diagonal_entry, Fin.cons_zero]`.

Take `⟨r₂, hr₂, e₂⟩` from `hess_two_bd hϖ _ (hessenberg_submatrix_tail hHess) htb (fun i j => hessenberg_entry_bounded hϖ htb hxb i.succ j (fun h => hyb _))`. Establish `hdiag : ∏ i, ((HH (t : K) (Fin.cons ρ x : Fin (n + 1 + 1) → K) y).submatrix Fin.succ Fin.succ) i i = ∏ k, x k`. Simplify using `only [Matrix.submatrix_apply, hessenberg_diagonal_entry, Fin.cons_succ]`. Establish `hsg` using `sg_units ((HH (t : K) (Fin.cons ρ x : Fin (n + 1 + 1) → K) y).submatrix Fin.succ Fin.succ) (fun i => Ring.inverse (x i)) (fun i => by`. Simplify using `only [Matrix.submatrix_apply, hessenberg_diagonal_entry, Fin.cons_succ]`.

Conclude with `Ring.mul_inverse_cancel _ (hx i).2.1)`. Establish `hsup : ∀ i : Fin n, ((HH (t : K) (Fin.cons ρ x : Fin (n + 1 + 1) → K) y).submatrix Fin.succ Fin.succ) i.castSucc i.succ = y (sd i.succ)`. Introduce `i`. Rewrite using `[Matrix.submatrix_apply, hessenberg_entry_upper _ _ _ (Fin.succ_lt_succ_iff.2 Fin.castSucc_lt_succ)]`. Use `congr 1`.

Simplify using `only [hsup] at hsg`. Rewrite `hsg`, `e₂` using `[hdiag]`. Rewrite `e₂` using `[hsg]`. Take `⟨r₁, hr₁, e₁⟩` from `hess_one_bd hϖ _ (hessenberg_submatrix_above_one hHess) htb (fun i j => hessenberg_entry_bounded hϖ htb hxb (Fin.succAbove 1 i) j (fun h => hyb _))`. Establish `hdiag' : ∏ i, ((HH (t : K) (Fin.cons ρ x : Fin (n + 1 + 1) → K) y).submatrix (Fin.succAbove 1) Fin.succ) i i = y (sd 0) * ∏ i : Fin n, x i.succ`.

Establish `f0 : ((HH (t : K) (Fin.cons ρ x : Fin (n + 1 + 1) → K) y).submatrix (Fin.succAbove 1) Fin.succ) 0 0 = y (sd 0)`. Rewrite using `[Matrix.submatrix_apply, succ_above_one_zero, hessenberg_entry_upper _ _ _ (Fin.succ_pos 0)]`. Use `congr 1`. Establish `f1 : ∀ i : Fin n, ((HH (t : K) (Fin.cons ρ x : Fin (n + 1 + 1) → K) y).submatrix (Fin.succAbove 1) Fin.succ) i.succ i.succ = x i.succ`. Introduce `i`.

Rewrite using `[Matrix.submatrix_apply, succ_above_one_succ, hessenberg_diagonal_entry, Fin.cons_succ]`. Rewrite using `[Fin.prod_univ_succ, f0]`. Simplify using `only [f1]`. Rewrite `e₁` using `[hdiag']`. Rewrite `lap` using `[e₂, e₁]`.

Take `⟨S, hS⟩ : ∃ S, S = ∑ i : Fin n, y (sd i.succ) * Ring.inverse (x i.castSucc) * Ring.inverse (x i.succ)` from `⟨_, rfl⟩`. Take `⟨P, hPdef⟩ : ∃ P, P = ∏ k, x k` from `⟨_, rfl⟩`. Take `⟨P'', hP''def⟩ : ∃ P'', P'' = ∏ i : Fin n, x i.succ` from `⟨_, rfl⟩`. Take `⟨Pi, hPidef⟩ : ∃ Pi, Pi = ∏ k, Ring.inverse (x k)` from `⟨_, rfl⟩`. Establish `hPP : P * Pi = 1`.

Rewrite using `[hPdef, hPidef, ← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_eq_one fun k _ => Ring.mul_inverse_cancel _ (hx k).2.1`. Establish `hPsplit : P = x 0 * P''` using `by rw [hPdef, hP''def, Fin.prod_univ_succ]`. Establish `he0 : x 0 * Ring.inverse (x 0) = 1` using `Ring.mul_inverse_cancel _ (hx 0).2.1`. Establish `hP''Pi : P'' * Pi = Ring.inverse (x 0)`.

Rewrite `hPP` using `[hPsplit]`. Take the linear combination `(Ring.inverse (x 0)) * hPP - (P'' * Pi) * he0`. Establish `hX0 : x0 (D' : K) x = (D' : K) * Pi`. Unfold `x0`. Rewrite using `[← hPdef, ringInverse_eq hPP]`.

Establish `hg1` using `first_coordinate_formula D' x y (fun k => (hx k).2.1)`. Rewrite `hg1` using `[← hS, hX0]`. Rewrite `lap` using `[← hS, ← hPdef, ← hP''def]`. Rewrite using `[hX0, hg1]`. Establish `hPi : Bd R ϖ ((n + 1) * a₁) Pi`.

Use `Bd.prod Finset.univ (fun k => Ring.inverse (x k)) (fun k _ => (hx k).2.2)` as an intermediate fact. Rewrite `this` using `[Finset.card_univ, Fintype.card_fin]`. Rewrite using `[hPidef]`. Conclude with `this`. Establish `hSb : Bd R ϖ B S`.

Rewrite using `[hS]`. Use `Bd.sum _ _ fun i _ => ?_` and prove the remaining obligations. Conclude with `Bd.mono hϖ (by omega) (((hyb (sd i.succ)).mul (hx i.castSucc).2.2).mul (hx i.succ).2.2)`. Establish `hXb : Bd R ϖ B ((D' : K) * Pi)` using `Bd.mono hϖ (by omega) (hDb.mul hPi)`. Establish `hq₂ : Bd R ϖ B (r₂ * Pi)` using `Bd.mono hϖ (by omega) (hr₂.mul hPi)`.

Establish `hq₁ : Bd R ϖ B (r₁ * Pi)` using `Bd.mono hϖ (by omega) (hr₁.mul hPi)`. Establish `hye : Bd R ϖ B (y (sd 0) * Ring.inverse (x 0))` using `Bd.mono hϖ (by omega) ((hyb (sd 0)).mul (hx 0).2.2)`. Take `⟨δ, hδ⟩ : ∃ δ, δ = S - r₂ * Pi * (t : K)` from `⟨_, rfl⟩`. Establish `hδb : Bd R ϖ B δ` using `by rw [hδ]; exact hSb.sub (hq₂.mul_mem htR)`. Establish `hε : Sm R ϖ 1 (-((t : K) * δ))` using `(Sm.mul_bd (Sm.mono hϖ (by omega) ht : Sm R ϖ (1 + B) (t : K)) hδb).neg`.

Take `⟨v, hv, ev, -⟩` from `Sm.one_add_inv hC.adic le_rfl hε`. Take `⟨G, hG⟩ : ∃ G, G = -((D' : K) * Pi * (r₂ * Pi)) + (D' : K) * Pi * δ * δ * v + y (sd 0) * Ring.inverse (x 0) * δ * v + r₁ * Pi * v` from `⟨_, rfl⟩`. Establish `hGb : Bd R ϖ (3 * B) G`. Rewrite using `[hG]`. Use `((Bd.add ?_ ?_).add ?_).add ?_` and prove the remaining obligations.

Conclude with `Bd.mono hϖ (by omega) (hXb.mul hq₂).neg`. Conclude with `Bd.mono hϖ (by omega) (((hXb.mul hδb).mul hδb).mul_mem hv)`. Conclude with `Bd.mono hϖ (by omega) ((hye.mul hδb).mul_mem hv)`. Conclude with `Bd.mono hϖ (by omega) (hq₁.mul_mem hv)`. Establish `htG : (t : K) * G ∈ R` using `sm_zero_iff.1 (Sm.mul_bd (Sm.mono hϖ (by omega) ht : Sm R ϖ (0 + 3 * B) (t : K)) hGb)`.

Establish `hW : ρ * (1 - (t : K) * δ) = (D' : K) * Pi + (t : K) * (y (sd 0) * Ring.inverse (x 0)) + (t : K) ^ 2 * (r₁ * Pi)`. Rewrite using `[hδ]`. Take the linear combination `(-Pi) * lap - ρ * (1 - (t : K) * S) * hPP + (t : K) * y (sd 0) * hP''Pi`. Establish `hρ : ρ = ((D' : K) * Pi + (t : K) * (y (sd 0) * Ring.inverse (x 0)) + (t : K) ^ 2 * (r₁ * Pi)) * v`. Take the linear combination `v * hW - ρ * ev`.

Establish `hfin : ρ = (D' : K) * Pi + (t : K) * (y (sd 0) * Ring.inverse (x 0) + (D' : K) * Pi * S) + (t : K) ^ 2 * G`. Rewrite using `[hG]`. Establish `hδ' : S = δ + r₂ * Pi * (t : K)` using `by rw [hδ]; ring`. Rewrite using `[hδ']`. Take the linear combination `hρ + ((D' : K) * Pi * (1 + (t : K) * δ) + (t : K) * (y (sd 0) * Ring.inverse (x 0))) * ev`.

Establish `hgb : Bd R ϖ (2 * B) (y (sd 0) * Ring.inverse (x 0) + (D' : K) * Pi * S + (t : K) * G)` using `((Bd.mono hϖ (by omega) hye).add (Bd.mono hϖ (by omega) (hXb.mul hSb))).add (Bd.of_mem hϖ htG _)`. Prove the components needed by the constructor for the conclusion. Establish `: ρ - (D' : K) * Pi = (t : K) * (y (sd 0) * Ring.inverse (x 0) + (D' : K) * Pi * S + (t : K) * G)`. Take the linear combination `hfin`. Rewrite using `[this]`.

Conclude with `Sm.mul_bd (Sm.mono hϖ (by omega) ht : Sm R ϖ (b + 2 * B) (t : K)) hgb`. Use `⟨(t : K) * G, htG, ?_⟩` and prove the remaining obligations. Establish `hti : (t : K) * ((t⁻¹ : Kˣ) : K) = 1` using `by simp`. Take the linear combination `((t⁻¹ : Kˣ) : K) * hfin + (y (sd 0) * Ring.inverse (x 0) + (D' : K) * Pi * S + (t : K) * G) * hti`.
-/
theorem pw_main (hC : Cst R ϖ L₀ Λ₀ Q a b) (m : ℕ) (hm : 1 ≤ m) :
    ∃ M₂ : ℕ, ∀ t : Kˣ, Sm R ϖ M₂ (t : K) → ∀ D' : Kˣ, ((D' : K) ∈ Q ∨ -(D' : K) ∈ Q) →
    ∀ (ρ : K) (x : Fin m → K) (y : Pr (m + 1) → K),
      (∀ k, x k ∈ L₀ ∧ IsUnit (x k) ∧ Bd R ϖ ((m + 1) * a) (Ring.inverse (x k))) →
      (∀ p, y p ∈ L₀) → (HH (t : K) (Fin.cons ρ x : Fin (m + 1) → K) y).det = (D' : K) →
      Sm R ϖ b (ρ - x0 (D' : K) x) ∧
      ∃ r ∈ R, ρ * ((t⁻¹ : Kˣ) : K) = x0 (D' : K) x * ((t⁻¹ : Kˣ) : K) + g1 (D' : K) x y + r := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  obtain ⟨a₁, ha₁⟩ : ∃ a₁, a₁ = (n + 1 + 1) * a := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = a + (n + 1) * a + (n + 1) * a₁ + 2 * a₁ := ⟨_, rfl⟩
  refine ⟨b + 3 * B + 1, ?_⟩
  intro t ht D' hD' ρ x y hx hy hdet
  rw [← ha₁] at hx
  have hϖ := hC.adic.mem
  obtain ⟨hDb, hDi⟩ := determinant_and_inverse_bounded hC D' hD'
  have htb : Bd R ϖ a (t : K) := ht.bd hϖ a
  have htR : (t : K) ∈ R := ht.mem hϖ
  have hxb : ∀ k, Bd R ϖ a (x k) := fun k => hC.L0 _ (hx k).1
  have hyb : ∀ p, Bd R ϖ a (y p) := fun p => hC.L0 _ (hy p)
  have hHess := isHess_HH (t : K) (Fin.cons ρ x : Fin (n + 1 + 1) → K) y

  have lap := hess_laplace _ hHess
  rw [hdet, hessenberg_diagonal_entry, Fin.cons_zero] at lap

  obtain ⟨r₂, hr₂, e₂⟩ := hess_two_bd hϖ _ (hessenberg_submatrix_tail hHess) htb
    (fun i j => hessenberg_entry_bounded hϖ htb hxb i.succ j (fun h => hyb _))
  have hdiag : ∏ i, ((HH (t : K) (Fin.cons ρ x : Fin (n + 1 + 1) → K) y).submatrix
      Fin.succ Fin.succ) i i = ∏ k, x k := by
    simp only [Matrix.submatrix_apply, hessenberg_diagonal_entry, Fin.cons_succ]
  have hsg := sg_units ((HH (t : K) (Fin.cons ρ x : Fin (n + 1 + 1) → K) y).submatrix
      Fin.succ Fin.succ) (fun i => Ring.inverse (x i)) (fun i => by
        simp only [Matrix.submatrix_apply, hessenberg_diagonal_entry, Fin.cons_succ]
        exact Ring.mul_inverse_cancel _ (hx i).2.1)
  have hsup : ∀ i : Fin n, ((HH (t : K) (Fin.cons ρ x : Fin (n + 1 + 1) → K) y).submatrix
      Fin.succ Fin.succ) i.castSucc i.succ = y (sd i.succ) := by
    intro i
    rw [Matrix.submatrix_apply, hessenberg_entry_upper _ _ _ (Fin.succ_lt_succ_iff.2 Fin.castSucc_lt_succ)]
    congr 1
  simp only [hsup] at hsg
  rw [hdiag] at hsg e₂
  rw [hsg] at e₂

  obtain ⟨r₁, hr₁, e₁⟩ := hess_one_bd hϖ _ (hessenberg_submatrix_above_one hHess) htb
    (fun i j => hessenberg_entry_bounded hϖ htb hxb (Fin.succAbove 1 i) j (fun h => hyb _))
  have hdiag' : ∏ i, ((HH (t : K) (Fin.cons ρ x : Fin (n + 1 + 1) → K) y).submatrix
      (Fin.succAbove 1) Fin.succ) i i = y (sd 0) * ∏ i : Fin n, x i.succ := by
    have f0 : ((HH (t : K) (Fin.cons ρ x : Fin (n + 1 + 1) → K) y).submatrix
        (Fin.succAbove 1) Fin.succ) 0 0 = y (sd 0) := by
      rw [Matrix.submatrix_apply, succ_above_one_zero, hessenberg_entry_upper _ _ _ (Fin.succ_pos 0)]
      congr 1
    have f1 : ∀ i : Fin n, ((HH (t : K) (Fin.cons ρ x : Fin (n + 1 + 1) → K) y).submatrix
        (Fin.succAbove 1) Fin.succ) i.succ i.succ = x i.succ := by
      intro i
      rw [Matrix.submatrix_apply, succ_above_one_succ, hessenberg_diagonal_entry, Fin.cons_succ]
    rw [Fin.prod_univ_succ, f0]
    simp only [f1]
  rw [hdiag'] at e₁
  rw [e₂, e₁] at lap

  obtain ⟨S, hS⟩ : ∃ S, S = ∑ i : Fin n, y (sd i.succ) * Ring.inverse (x i.castSucc) *
      Ring.inverse (x i.succ) := ⟨_, rfl⟩
  obtain ⟨P, hPdef⟩ : ∃ P, P = ∏ k, x k := ⟨_, rfl⟩
  obtain ⟨P'', hP''def⟩ : ∃ P'', P'' = ∏ i : Fin n, x i.succ := ⟨_, rfl⟩
  obtain ⟨Pi, hPidef⟩ : ∃ Pi, Pi = ∏ k, Ring.inverse (x k) := ⟨_, rfl⟩
  have hPP : P * Pi = 1 := by
    rw [hPdef, hPidef, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun k _ => Ring.mul_inverse_cancel _ (hx k).2.1
  have hPsplit : P = x 0 * P'' := by rw [hPdef, hP''def, Fin.prod_univ_succ]
  have he0 : x 0 * Ring.inverse (x 0) = 1 := Ring.mul_inverse_cancel _ (hx 0).2.1
  have hP''Pi : P'' * Pi = Ring.inverse (x 0) := by
    rw [hPsplit] at hPP
    linear_combination (Ring.inverse (x 0)) * hPP - (P'' * Pi) * he0
  have hX0 : x0 (D' : K) x = (D' : K) * Pi := by
    unfold x0
    rw [← hPdef, ringInverse_eq hPP]
  have hg1 := first_coordinate_formula D' x y (fun k => (hx k).2.1)
  rw [← hS, hX0] at hg1
  rw [← hS, ← hPdef, ← hP''def] at lap
  rw [hX0, hg1]

  have hPi : Bd R ϖ ((n + 1) * a₁) Pi := by
    have := Bd.prod Finset.univ (fun k => Ring.inverse (x k)) (fun k _ => (hx k).2.2)
    rw [Finset.card_univ, Fintype.card_fin] at this
    rw [hPidef]; exact this
  have hSb : Bd R ϖ B S := by
    rw [hS]
    refine Bd.sum _ _ fun i _ => ?_
    exact Bd.mono hϖ (by omega) (((hyb (sd i.succ)).mul (hx i.castSucc).2.2).mul (hx i.succ).2.2)
  have hXb : Bd R ϖ B ((D' : K) * Pi) := Bd.mono hϖ (by omega) (hDb.mul hPi)
  have hq₂ : Bd R ϖ B (r₂ * Pi) := Bd.mono hϖ (by omega) (hr₂.mul hPi)
  have hq₁ : Bd R ϖ B (r₁ * Pi) := Bd.mono hϖ (by omega) (hr₁.mul hPi)
  have hye : Bd R ϖ B (y (sd 0) * Ring.inverse (x 0)) :=
    Bd.mono hϖ (by omega) ((hyb (sd 0)).mul (hx 0).2.2)
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = S - r₂ * Pi * (t : K) := ⟨_, rfl⟩
  have hδb : Bd R ϖ B δ := by rw [hδ]; exact hSb.sub (hq₂.mul_mem htR)
  have hε : Sm R ϖ 1 (-((t : K) * δ)) :=
    (Sm.mul_bd (Sm.mono hϖ (by omega) ht : Sm R ϖ (1 + B) (t : K)) hδb).neg
  obtain ⟨v, hv, ev, -⟩ := Sm.one_add_inv hC.adic le_rfl hε
  obtain ⟨G, hG⟩ : ∃ G, G = -((D' : K) * Pi * (r₂ * Pi)) + (D' : K) * Pi * δ * δ * v +
      y (sd 0) * Ring.inverse (x 0) * δ * v + r₁ * Pi * v := ⟨_, rfl⟩
  have hGb : Bd R ϖ (3 * B) G := by
    rw [hG]
    refine ((Bd.add ?_ ?_).add ?_).add ?_
    · exact Bd.mono hϖ (by omega) (hXb.mul hq₂).neg
    · exact Bd.mono hϖ (by omega) (((hXb.mul hδb).mul hδb).mul_mem hv)
    · exact Bd.mono hϖ (by omega) ((hye.mul hδb).mul_mem hv)
    · exact Bd.mono hϖ (by omega) (hq₁.mul_mem hv)
  have htG : (t : K) * G ∈ R :=
    sm_zero_iff.1 (Sm.mul_bd (Sm.mono hϖ (by omega) ht : Sm R ϖ (0 + 3 * B) (t : K)) hGb)

  have hW : ρ * (1 - (t : K) * δ) = (D' : K) * Pi + (t : K) * (y (sd 0) * Ring.inverse (x 0)) +
      (t : K) ^ 2 * (r₁ * Pi) := by
    rw [hδ]
    linear_combination (-Pi) * lap - ρ * (1 - (t : K) * S) * hPP + (t : K) * y (sd 0) * hP''Pi
  have hρ : ρ = ((D' : K) * Pi + (t : K) * (y (sd 0) * Ring.inverse (x 0)) +
      (t : K) ^ 2 * (r₁ * Pi)) * v := by
    linear_combination v * hW - ρ * ev
  have hfin : ρ = (D' : K) * Pi + (t : K) * (y (sd 0) * Ring.inverse (x 0) + (D' : K) * Pi * S) +
      (t : K) ^ 2 * G := by
    rw [hG]
    have hδ' : S = δ + r₂ * Pi * (t : K) := by rw [hδ]; ring
    rw [hδ']
    linear_combination hρ + ((D' : K) * Pi * (1 + (t : K) * δ) +
      (t : K) * (y (sd 0) * Ring.inverse (x 0))) * ev
  have hgb : Bd R ϖ (2 * B) (y (sd 0) * Ring.inverse (x 0) + (D' : K) * Pi * S + (t : K) * G) :=
    ((Bd.mono hϖ (by omega) hye).add (Bd.mono hϖ (by omega) (hXb.mul hSb))).add
      (Bd.of_mem hϖ htG _)
  constructor
  · have : ρ - (D' : K) * Pi =
        (t : K) * (y (sd 0) * Ring.inverse (x 0) + (D' : K) * Pi * S + (t : K) * G) := by
      linear_combination hfin
    rw [this]
    exact Sm.mul_bd (Sm.mono hϖ (by omega) ht : Sm R ϖ (b + 2 * B) (t : K)) hgb
  · refine ⟨(t : K) * G, htG, ?_⟩
    have hti : (t : K) * ((t⁻¹ : Kˣ) : K) = 1 := by simp
    linear_combination ((t⁻¹ : Kˣ) : K) * hfin +
      (y (sd 0) * Ring.inverse (x 0) + (D' : K) * Pi * S + (t : K) * G) * hti

/- English proof (translation)
Use `⟨(1 + m * ((m + 1) * a)) + m * a, ?_⟩` and prove the remaining obligations. Introduce `t ht ρ x y hx hy`. Establish `hϖ` using `hC.adic.mem`. Establish `htb : Bd R ϖ a t` using `ht.bd hϖ a`. Establish `hent : ∀ i j, Bd R ϖ a (((HH t (Fin.cons ρ x : Fin (m + 1) → K) y).submatrix Fin.succ Fin.succ) i j)`.

Introduce `i j`. Conclude with `hessenberg_entry_bounded hϖ htb (fun k => hC.L0 _ (hx k).1) i.succ j (fun h => hC.L0 _ (hy _ (Fin.succ_ne_zero i)))`. Take `⟨r, hr, e⟩` from `hess_one_bd hϖ _ (hessenberg_submatrix_tail (isHess_HH t (Fin.cons ρ x : Fin (m + 1) → K) y)) htb hent`. Establish `hdiag : ∏ i, ((HH t (Fin.cons ρ x : Fin (m + 1) → K) y).submatrix Fin.succ Fin.succ) i i = ∏ k, x k`. Simplify using `only [Matrix.submatrix_apply, hessenberg_diagonal_entry, Fin.cons_succ]`.

Rewrite `e` using `[hdiag]`. Establish `hPP : (∏ k, x k) * ∏ k, Ring.inverse (x k) = 1`. Rewrite using `[← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_eq_one fun k _ => Ring.mul_inverse_cancel _ (hx k).2.1`. Establish `hPi : Bd R ϖ (m * ((m + 1) * a)) (∏ k, Ring.inverse (x k))`.

Use `Bd.prod Finset.univ (fun k => Ring.inverse (x k)) (fun k _ => (hx k).2.2)` as an intermediate fact. Rewrite `this` using `[Finset.card_univ, Fintype.card_fin]`. Then use the resulting hypothesis. Establish `hε : Sm R ϖ 1 (t * r * ∏ k, Ring.inverse (x k))` using `(ht.mul_bd hr).mul_bd hPi`. Take `⟨v, hv, ev, -⟩` from `Sm.one_add_inv hC.adic le_rfl hε`. Establish `e2 : ((HH t (Fin.cons ρ x : Fin (m + 1) → K) y).submatrix Fin.succ Fin.succ).det = (∏ k, x k) * (1 + t * r * ∏ k, Ring.inverse (x k))`.

Rewrite using `[e]`. Take the linear combination `(-(t * r)) * hPP`. Establish `hu1 : IsUnit (∏ k, x k)` using `IsUnit.of_mul_eq_one _ hPP`. Establish `hu2 : IsUnit (1 + t * r * ∏ k, Ring.inverse (x k))` using `IsUnit.of_mul_eq_one _ ev`. Rewrite using `[e2]`.

Use `⟨hu1.mul hu2, ?_⟩` and prove the remaining obligations. Rewrite using `[modK_mul_isUnit hC.adic hu1 hu2, modK_unitR (R.add_mem R.one_mem (hε.mem hϖ)) hv ev, mul_one]`.
-/
theorem pw_det (hC : Cst R ϖ L₀ Λ₀ Q a b) (m : ℕ) :
    ∃ M₃ : ℕ, ∀ t : K, Sm R ϖ M₃ t → ∀ (ρ : K) (x : Fin m → K) (y : Pr (m + 1) → K),
      (∀ k, x k ∈ L₀ ∧ IsUnit (x k) ∧ Bd R ϖ ((m + 1) * a) (Ring.inverse (x k))) →
      (∀ p : Pr (m + 1), p.1.1 ≠ 0 → y p ∈ L₀) →
      IsUnit ((HH t (Fin.cons ρ x : Fin (m + 1) → K) y).submatrix Fin.succ Fin.succ).det ∧
      modK R ((HH t (Fin.cons ρ x : Fin (m + 1) → K) y).submatrix Fin.succ Fin.succ).det =
        modK R (∏ k, x k) := by
  refine ⟨(1 + m * ((m + 1) * a)) + m * a, ?_⟩
  intro t ht ρ x y hx hy
  have hϖ := hC.adic.mem
  have htb : Bd R ϖ a t := ht.bd hϖ a
  have hent : ∀ i j, Bd R ϖ a
      (((HH t (Fin.cons ρ x : Fin (m + 1) → K) y).submatrix Fin.succ Fin.succ) i j) := by
    intro i j
    exact hessenberg_entry_bounded hϖ htb (fun k => hC.L0 _ (hx k).1) i.succ j
      (fun h => hC.L0 _ (hy _ (Fin.succ_ne_zero i)))
  obtain ⟨r, hr, e⟩ := hess_one_bd hϖ _
    (hessenberg_submatrix_tail (isHess_HH t (Fin.cons ρ x : Fin (m + 1) → K) y)) htb hent
  have hdiag : ∏ i, ((HH t (Fin.cons ρ x : Fin (m + 1) → K) y).submatrix Fin.succ Fin.succ) i i =
      ∏ k, x k := by
    simp only [Matrix.submatrix_apply, hessenberg_diagonal_entry, Fin.cons_succ]
  rw [hdiag] at e
  have hPP : (∏ k, x k) * ∏ k, Ring.inverse (x k) = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun k _ => Ring.mul_inverse_cancel _ (hx k).2.1
  have hPi : Bd R ϖ (m * ((m + 1) * a)) (∏ k, Ring.inverse (x k)) := by
    have := Bd.prod Finset.univ (fun k => Ring.inverse (x k)) (fun k _ => (hx k).2.2)
    rwa [Finset.card_univ, Fintype.card_fin] at this
  have hε : Sm R ϖ 1 (t * r * ∏ k, Ring.inverse (x k)) := (ht.mul_bd hr).mul_bd hPi
  obtain ⟨v, hv, ev, -⟩ := Sm.one_add_inv hC.adic le_rfl hε
  have e2 : ((HH t (Fin.cons ρ x : Fin (m + 1) → K) y).submatrix Fin.succ Fin.succ).det =
      (∏ k, x k) * (1 + t * r * ∏ k, Ring.inverse (x k)) := by
    rw [e]; linear_combination (-(t * r)) * hPP
  have hu1 : IsUnit (∏ k, x k) := IsUnit.of_mul_eq_one _ hPP
  have hu2 : IsUnit (1 + t * r * ∏ k, Ring.inverse (x k)) := IsUnit.of_mul_eq_one _ ev
  rw [e2]
  refine ⟨hu1.mul hu2, ?_⟩
  rw [modK_mul_isUnit hC.adic hu1 hu2,
    modK_unitR (R.add_mem R.one_mem (hε.mem hϖ)) hv ev, mul_one]

end P2

section PWa

variable {K : Type} [CommRing K]

/- English proof (translation)
Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using `[EE]`. Simplify using `[EE, h]`.
-/
theorem pw_one_add_EE {n : ℕ} (N : Pr n → K) (i j : Fin n) :
    (1 + EE N) i j = if i = j then 1 else if h : i < j then N ⟨(i, j), h⟩ else 0 := by
  by_cases h : i = j
  · subst h; simp [EE]
  · simp [EE, h]

/- English proof (translation)
Use `⟨fun i j hij => ?_, fun i => ?_⟩` and prove the remaining obligations. Establish `hij' : j < i` using `hij`. Rewrite using `[pw_one_add_EE, if_neg (ne_of_gt hij'), dif_neg (not_lt.2 hij'.le)]`. Rewrite using `[pw_one_add_EE, if_pos rfl]`.
-/
theorem pw_isUpUni {n : ℕ} (N : Pr n → K) : IsUpUni (1 + EE N) := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · have hij' : j < i := hij
    rw [pw_one_add_EE, if_neg (ne_of_gt hij'), dif_neg (not_lt.2 hij'.le)]
  · rw [pw_one_add_EE, if_pos rfl]

/- English proof (translation)
Simplify using `[ys, ee]`.
-/
theorem pw_ys_zero {m : ℕ} (n : Pr (m + 1) → K) (τ : Fin m → K) (j : Fin m) (h : (0 : Fin (m + 1)) < j.succ) :
    ys n τ ⟨(0, j.succ), h⟩ = τ j := by
  simp [ys, ee]

/- English proof (translation)
Simplify using `[ys, ee, Fin.succ_ne_zero]`.
-/
theorem pw_ys_succ {m : ℕ} (n : Pr (m + 1) → K) (τ : Fin m → K) (i : Fin m) (j : Fin (m + 1))
    (h : i.succ < j) (h' : i.castSucc < j) :
    ys n τ ⟨(i.succ, j), h⟩ = n ⟨(i.castSucc, j), h'⟩ := by
  simp [ys, ee, Fin.succ_ne_zero]

/- English proof (translation)
Simplify using `[ys, ee, hp]`.
-/
theorem pw_ys_indep {m : ℕ} (n : Pr (m + 1) → K) (τ τ' : Fin m → K) (p : Pr (m + 1))
    (hp : p.1.1 ≠ 0) : ys n τ p = ys n τ' p := by
  simp [ys, ee, hp]

/- English proof (translation)
Use function extensionality and compare the values at `p`. Distinguish the cases in `hp : p.1.1 = 0`. Simplify using `[ys, ee, hp]`. Simplify using `[ys, ee, hp]`.
-/
theorem pw_ys_add {m : ℕ} (n : Pr (m + 1) → K) (τ l : Fin m → K) :
    ys n (τ + l) = ys n τ + ys 0 l := by
  funext p
  by_cases hp : p.1.1 = 0
  · simp [ys, ee, hp]
  · simp [ys, ee, hp]

/- English proof (translation)
Distinguish the cases in `hp : p.1.1 = 0`. Simplify using `[ys, ee, hp, hl]`. Simplify using `[ys, ee, hp, Λ.zero_mem]`.
-/
theorem pw_ys_mem {m : ℕ} (Λ : AddSubgroup K) (l : Fin m → K) (hl : ∀ i, l i ∈ Λ) (p : Pr (m + 1)) :
    ys (0 : Pr (m + 1) → K) l p ∈ Λ := by
  by_cases hp : p.1.1 = 0
  · simp [ys, ee, hp, hl]
  · simp [ys, ee, hp, Λ.zero_mem]

/- English proof (translation)
Unfold `sUp`. Rewrite using `[Fin.sum_univ_castSucc]`. Simplify using `only [Fin.val_last, lt_self_iff_false, dite_false, add_zero, Fin.val_castSucc]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[dif_pos (by omega), pw_one_add_EE]`.

Establish `h1 : i.castSucc ≠ (⟨i.val + 1, by omega⟩ : Fin (m + 1))`. Introduce `h`. Use `congrArg Fin.val h` as an intermediate fact. Simplify using `at this`. Establish `h2 : i.castSucc < (⟨i.val + 1, by omega⟩ : Fin (m + 1))`.

Rewrite using `[Fin.lt_def]`. Simplify using the standard rewrite rules. Rewrite using `[if_neg h1, dif_pos h2]`. Both sides reduce to the same expression.
-/
theorem pw_sUp {m : ℕ} (N : Pr (m + 1) → K) : sUp (1 + EE N) = ∑ i : Fin m, N (sd i) := by
  unfold sUp
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_last, lt_self_iff_false, dite_false, add_zero, Fin.val_castSucc]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dif_pos (by omega), pw_one_add_EE]
  have h1 : i.castSucc ≠ (⟨i.val + 1, by omega⟩ : Fin (m + 1)) := by
    intro h; have := congrArg Fin.val h; simp at this
  have h2 : i.castSucc < (⟨i.val + 1, by omega⟩ : Fin (m + 1)) := by
    rw [Fin.lt_def]; simp
  rw [if_neg h1, dif_pos h2]
  rfl

end PWa

section PWb

variable {K : Type} [CommRing K]

def pw_Mx {m : ℕ} (t : K) (u : Matrix (Fin (m + 1)) (Fin (m + 1)) K) : Matrix (Fin m) (Fin m) K :=
  fun j k => t * u (Fin.rev k).castSucc j.succ

def pw_bv {m : ℕ} (c : K) : Fin m → K := fun j => if j.succ = Fin.last m then c else 0

/- English proof (translation)
Unfold `lastE`. Rewrite using `[← Equiv.sum_comp Fin.revPerm]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Establish `hk` using `k.2`. Establish `: ((Fin.rev k : Fin m).val + 1 = m) ↔ k.val = 0`.

Simplify using `only [Fin.val_rev]`. Use linear arithmetic over natural numbers and integers. Simplify using `only [Fin.revPerm_apply, this]`.
-/
theorem pw_lastE_rev {m : ℕ} (ξ : Fin m → K) :
    lastE ξ = ∑ k : Fin m, if k.val = 0 then ξ (Fin.rev k) else 0 := by
  unfold lastE
  rw [← Equiv.sum_comp Fin.revPerm]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk := k.2
  have : ((Fin.rev k : Fin m).val + 1 = m) ↔ k.val = 0 := by
    simp only [Fin.val_rev]; omega
  simp only [Fin.revPerm_apply, this]

/- English proof (translation)
Use extensionality with `i j`. Use `Fin.cases ?_ (fun i' => ?_) i` and prove the remaining obligations. Use `Fin.cases ?_ (fun j' => ?_) j` and prove the remaining obligations. Establish `h0 : (0 : Fin (m + 1)) ≠ Fin.last m`. Introduce `h`.

Use `congrArg Fin.val h` as an intermediate fact. Simplify using `at this`. Use linear arithmetic over natural numbers and integers. Simplify using `only [Hm, HH, Fin.cases_zero, if_true, Fin.cons_zero, if_neg h0, add_zero]`. Rewrite using `[pw_lastE_rev, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[pw_one_add_EE]`. Distinguish the cases in `hk : k.val = 0`. Establish `: k.castSucc = 0` using `by ext; simpa using hk`. Rewrite using `[if_pos this, if_pos hk]`.

Expand and normalize the polynomial expressions, which then agree. Establish `: k.castSucc ≠ 0`. Introduce `h`. Apply `hk` to reduce the goal to its premises. Use `congrArg Fin.val h` as an intermediate fact.

Simplify using `using this`. Rewrite using `[if_neg this, if_neg hk, dif_neg (by simp)]; ring`. Establish `h0 : (0 : Fin (m + 1)) ≠ j'.succ` using `(Fin.succ_ne_zero j').symm`. Establish `h1 : (0 : Fin (m + 1)) < j'.succ` using `Fin.succ_pos j'`. Simplify using `only [Hm, HH, Fin.cases_zero, if_neg h0, dif_pos h1]`.

Rewrite using `[pw_ys_zero]`. Simplify using `only [Pi.add_apply, Matrix.mulVec, dotProduct, pw_Mx, pw_bv]`. Use `congr 1`. Rewrite using `[← Equiv.sum_comp Fin.revPerm]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Simplify using `only [Fin.revPerm_apply, Fin.rev_rev]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [Hm, HH, Fin.cases_succ]`. Rewrite using `[pw_one_add_EE]`. Distinguish the cases in `h1 : i'.succ = j`.

Substitute `h1` using the available equality. Establish `h2 : i'.castSucc ≠ i'.succ` using `(Fin.castSucc_lt_succ).ne`. Rewrite using `[if_pos rfl, if_neg h2, dif_pos Fin.castSucc_lt_succ, Fin.cons_succ]`. Both sides reduce to the same expression. Rewrite using `[if_neg h1]`.

Distinguish the cases in `h2 : i'.succ < j`. Establish `h3 : i'.castSucc < j` using `lt_trans Fin.castSucc_lt_succ h2`. Rewrite using `[dif_pos h2, if_neg h3.ne, dif_pos h3, pw_ys_succ _ _ _ _ h2 h3]`. Both sides reduce to the same expression. Rewrite using `[dif_neg h2]`.

Distinguish the cases in `h3 : j.val + 1 = i'.succ.val`. Establish `h4 : i'.castSucc = j` using `by ext; simp at h3 ⊢; omega`. Rewrite using `[if_pos h3, if_pos h4, mul_one]`. Establish `h4 : i'.castSucc ≠ j`. Introduce `h`.

Apply `h3` to reduce the goal to its premises. Rewrite using `[← h]`. Simplify using the standard rewrite rules. Establish `h5 : ¬ i'.castSucc < j`. Introduce `h`.

Rewrite `h`, `h2` using `[Fin.lt_def]`. Establish `h6 : i'.succ.val ≠ j.val` using `fun e => h1 (Fin.ext e)`. Simplify using `at h h2 h6`. Use linear arithmetic over natural numbers and integers. Rewrite using `[if_neg h3, if_neg h4, dif_neg h5, mul_zero]`.
-/
theorem pw_shape {m : ℕ} (hm : 1 ≤ m) (t c : K) (ξ : Fin m → K) (N : Pr (m + 1) → K) :
    Hm t c ξ (1 + EE N) = HH t (Fin.cons (t * lastE ξ) (xs (t • N)) : Fin (m + 1) → K)
      (ys (t • N) (pw_Mx t (1 + EE N) *ᵥ ξ + pw_bv c)) := by
  ext i j
  refine Fin.cases ?_ (fun i' => ?_) i
  · refine Fin.cases ?_ (fun j' => ?_) j
    · have h0 : (0 : Fin (m + 1)) ≠ Fin.last m := by
        intro h; have := congrArg Fin.val h; simp at this; omega
      simp only [Hm, HH, Fin.cases_zero, if_true, Fin.cons_zero, if_neg h0, add_zero]
      rw [pw_lastE_rev, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [pw_one_add_EE]
      by_cases hk : k.val = 0
      · have : k.castSucc = 0 := by ext; simpa using hk
        rw [if_pos this, if_pos hk]; ring
      · have : k.castSucc ≠ 0 := by
          intro h; apply hk; have := congrArg Fin.val h; simpa using this
        rw [if_neg this, if_neg hk, dif_neg (by simp)]; ring
    · have h0 : (0 : Fin (m + 1)) ≠ j'.succ := (Fin.succ_ne_zero j').symm
      have h1 : (0 : Fin (m + 1)) < j'.succ := Fin.succ_pos j'
      simp only [Hm, HH, Fin.cases_zero, if_neg h0, dif_pos h1]
      rw [pw_ys_zero]
      simp only [Pi.add_apply, Matrix.mulVec, dotProduct, pw_Mx, pw_bv]
      congr 1
      rw [← Equiv.sum_comp Fin.revPerm]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Fin.revPerm_apply, Fin.rev_rev]
      ring
  · simp only [Hm, HH, Fin.cases_succ]
    rw [pw_one_add_EE]
    by_cases h1 : i'.succ = j
    · subst h1
      have h2 : i'.castSucc ≠ i'.succ := (Fin.castSucc_lt_succ).ne
      rw [if_pos rfl, if_neg h2, dif_pos Fin.castSucc_lt_succ, Fin.cons_succ]
      rfl
    · rw [if_neg h1]
      by_cases h2 : i'.succ < j
      · have h3 : i'.castSucc < j := lt_trans Fin.castSucc_lt_succ h2
        rw [dif_pos h2, if_neg h3.ne, dif_pos h3, pw_ys_succ _ _ _ _ h2 h3]
        rfl
      · rw [dif_neg h2]
        by_cases h3 : j.val + 1 = i'.succ.val
        · have h4 : i'.castSucc = j := by ext; simp at h3 ⊢; omega
          rw [if_pos h3, if_pos h4, mul_one]
        · have h4 : i'.castSucc ≠ j := by
            intro h; apply h3; rw [← h]; simp
          have h5 : ¬ i'.castSucc < j := by
            intro h
            rw [Fin.lt_def] at h h2
            have h6 : i'.succ.val ≠ j.val := fun e => h1 (Fin.ext e)
            simp at h h2 h6; omega
          rw [if_neg h3, if_neg h4, dif_neg h5, mul_zero]

/- English proof (translation)
Unfold `lastE`. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Apply the tactic sequence `by_cases h : j.val + 1 = m <;> simp [h]`.
-/
theorem pw_lastE_add {m : ℕ} (ξ r : Fin m → K) : lastE (ξ + r) = lastE ξ + lastE r := by
  unfold lastE
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : j.val + 1 = m <;> simp [h]

/- English proof (translation)
Unfold `lastE`. Use `R.sum_mem fun j _ => ?_` and prove the remaining obligations. Distinguish the cases in `h : j.val + 1 = m`. Rewrite using `[if_pos h]`. Conclude with `hr j`.

Rewrite using `[if_neg h]`. Conclude with `R.zero_mem`.
-/
theorem pw_lastE_mem {m : ℕ} (R : Subring K) (r : Fin m → K) (hr : ∀ i, r i ∈ R) : lastE r ∈ R := by
  unfold lastE
  refine R.sum_mem fun j _ => ?_
  by_cases h : j.val + 1 = m
  · rw [if_pos h]; exact hr j
  · rw [if_neg h]; exact R.zero_mem

def pw_ro {m : ℕ} (r : Fin m → K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K :=
  fun i j => if i = j then 1 else
    Fin.cases (Fin.cases 0 (fun k => r (Fin.rev k)) j) (fun _ => 0) i

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.mul_apply, Fin.sum_univ_succ]`. Use `Fin.cases ?_ (fun i' => ?_) i` and prove the remaining obligations. Simplify using `only [pw_ro, if_true, Fin.cases_zero, one_mul, (Fin.succ_ne_zero _).symm, if_false, Fin.cases_succ, Hm, Pi.add_apply, add_mul, Finset.sum_add_distrib]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [pw_ro, Fin.succ_ne_zero, if_false, Fin.cases_succ, zero_mul, zero_add, Hm]`. Rewrite using `[Finset.sum_eq_single i']`. Simplify using the standard rewrite rules. Introduce `k _ hk`. Establish `: i'.succ ≠ k.succ` using `fun h => hk (Fin.succ_injective _ h).symm`.

Simplify using `[this]`. Simplify using the standard rewrite rules.
-/
theorem pw_ro_mul {m : ℕ} (t c : K) (ξ r : Fin m → K) (u : Matrix (Fin (m + 1)) (Fin (m + 1)) K) :
    Hm t c (ξ + r) u = pw_ro r * Hm t c ξ u := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_succ]
  refine Fin.cases ?_ (fun i' => ?_) i
  · simp only [pw_ro, if_true, Fin.cases_zero, one_mul, (Fin.succ_ne_zero _).symm, if_false,
      Fin.cases_succ, Hm, Pi.add_apply, add_mul, Finset.sum_add_distrib]
    ring
  · simp only [pw_ro, Fin.succ_ne_zero, if_false, Fin.cases_succ, zero_mul, zero_add, Hm]
    rw [Finset.sum_eq_single i']
    · simp
    · intro k _ hk
      have : i'.succ ≠ k.succ := fun h => hk (Fin.succ_injective _ h).symm
      simp [this]
    · simp

/- English proof (translation)
Use `⟨fun i j hij => ?_, fun i => ?_⟩` and prove the remaining obligations. Establish `hij' : i < j` using `hij`. Establish `h1 : Fin.rev j < Fin.rev i` using `Fin.rev_lt_rev.2 hij'`. Establish `h2 : Fin.rev i ≠ Fin.rev j` using `h1.ne'`. Establish `h3 : Fin.rev i ≠ 0`.

Introduce `h; rw [h] at h1; exact absurd h1 (by simp)`. Take `⟨i', hi'⟩` from `Fin.exists_succ_eq.2 h3`. Simplify using `only [Matrix.submatrix_apply, pw_ro, if_neg h2]`. Rewrite using `[← hi']`. Simplify using the standard rewrite rules.

Simplify using `[pw_ro]`.
-/
theorem pw_ro_low {m : ℕ} (r : Fin m → K) : IsLowUni ((pw_ro r).submatrix Fin.rev Fin.rev) := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · have hij' : i < j := hij
    have h1 : Fin.rev j < Fin.rev i := Fin.rev_lt_rev.2 hij'
    have h2 : Fin.rev i ≠ Fin.rev j := h1.ne'
    have h3 : Fin.rev i ≠ 0 := by
      intro h; rw [h] at h1; exact absurd h1 (by simp)
    obtain ⟨i', hi'⟩ := Fin.exists_succ_eq.2 h3
    simp only [Matrix.submatrix_apply, pw_ro, if_neg h2]
    rw [← hi']
    simp
  · simp [pw_ro]

/- English proof (translation)
Introduce `i j`. Simplify using `only [Matrix.submatrix_apply, pw_ro]`. Distinguish the cases in `h : Fin.rev i = Fin.rev j`. Rewrite using `[if_pos h]`. Conclude with `R.one_mem`.

Rewrite using `[if_neg h]`. Generalize the expression as in `Fin.rev i = i1`. Generalize the expression as in `Fin.rev j = j1`. Use `Fin.cases ?_ (fun i' => ?_) i1` and prove the remaining obligations. Use `Fin.cases ?_ (fun j' => ?_) j1` and prove the remaining obligations.

Simplify using the standard rewrite rules. Simplify using `using hr _`. Simplify using the standard rewrite rules.
-/
theorem pw_ro_int {m : ℕ} (R : Subring K) (r : Fin m → K) (hr : ∀ i, r i ∈ R) :
    IsInt R ((pw_ro r).submatrix Fin.rev Fin.rev) := by
  intro i j
  simp only [Matrix.submatrix_apply, pw_ro]
  by_cases h : Fin.rev i = Fin.rev j
  · rw [if_pos h]; exact R.one_mem
  · rw [if_neg h]
    generalize Fin.rev i = i1
    generalize Fin.rev j = j1
    refine Fin.cases ?_ (fun i' => ?_) i1
    · refine Fin.cases ?_ (fun j' => ?_) j1
      · simp
      · simpa using hr _
    · simp

/- English proof (translation)
Establish `h` using `Matrix.det_permute Fin.revPerm A`. Establish `e : (A.submatrix (Fin.revPerm : Fin n → Fin n) id) = A.submatrix Fin.rev id` using `rfl`. Rewrite `h` using `[e]`. Break down `Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n))) with hs | hs` into its components or cases. Use `left`.

Rewrite using `[h, hs]`. Simplify using the standard rewrite rules. Use `right`. Rewrite using `[h, hs]`. Simplify using the standard rewrite rules.
-/
theorem pw_det_rev {n : ℕ} (A : Matrix (Fin n) (Fin n) K) :
    (A.submatrix Fin.rev id).det = A.det ∨ (A.submatrix Fin.rev id).det = -A.det := by
  have h := Matrix.det_permute Fin.revPerm A
  have e : (A.submatrix (Fin.revPerm : Fin n → Fin n) id) = A.submatrix Fin.rev id := rfl
  rw [e] at h
  rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n))) with hs | hs
  · left; rw [h, hs]; simp
  · right; rw [h, hs]; simp

end PWb

section PWc

variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ} {ϖ : Kˣ} {L₀ Λ₀ : AddSubgroup K} {Q : Set K} {a b : ℕ}

/- English proof (translation)
Introduce `h`. Establish `h1 : ψ x * ψ (-x) = 1` using `by rw [← AddChar.map_add_eq_mul]; simp`. Rewrite `h1` using `[h, zero_mul]`. Conclude with `zero_ne_one h1`.
-/
theorem pw_psi_ne (ψ : AddChar K ℂ) (x : K) : ψ x ≠ 0 := by
  intro h
  have h1 : ψ x * ψ (-x) = 1 := by rw [← AddChar.map_add_eq_mul]; simp
  rw [h, zero_mul] at h1
  exact zero_ne_one h1

/- English proof (translation)
Simplify `(smul_finsum c f).symm` using `[smul_eq_mul]`.
-/
theorem pw_mul_finsum {α : Type} (c : ℂ) (f : α → ℂ) : ∑ᶠ i, c * f i = c * ∑ᶠ i, f i := by
  simpa [smul_eq_mul] using (smul_finsum c f).symm

/- English proof (translation)
Use `choose u hu using h`. Establish `: ∏ k, x k = ((∏ k, u k : Kˣ) : K)`. Rewrite using `[Units.coe_prod]`. Conclude with `Finset.prod_congr rfl fun k _ => (hu k).symm`. Rewrite using `[this]`.

Conclude with `Units.isUnit _`.
-/
theorem pw_isUnit_prod {m : ℕ} (x : Fin m → K) (h : ∀ k, IsUnit (x k)) : IsUnit (∏ k, x k) := by
  choose u hu using h
  have : ∏ k, x k = ((∏ k, u k : Kˣ) : K) := by
    rw [Units.coe_prod]; exact Finset.prod_congr rfl fun k _ => (hu k).symm
  rw [this]; exact Units.isUnit _

/- English proof (translation)
Establish `e1 : (Hm t c (ξ + r) u).submatrix Fin.rev id = (pw_ro r).submatrix Fin.rev Fin.rev * (Hm t c ξ u).submatrix Fin.rev id * 1`. Rewrite using `[pw_ro_mul, Matrix.mul_one]`. Conclude with `(Matrix.submatrix_mul_equiv (pw_ro r) (Hm t c ξ u) Fin.rev Fin.revPerm id).symm`. Establish `hone : IsInt R (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K)`. Introduce `i j`.

Distinguish the cases in `h : i = j`. Rewrite using `[h, Matrix.one_apply_eq]`. Conclude with `R.one_mem`. Rewrite using `[Matrix.one_apply_ne h]`. Conclude with `R.zero_mem`.

Rewrite using `[e1, hΦ.1 _ _ _ (pw_ro_low r) (pw_ro_int R r hr) (isUpUni_one K) hone, pw_lastE_add, show lastE ξ + lastE r + s = (lastE ξ + s) + lastE r by ring, AddChar.map_add_eq_mul, psi_R hD (pw_lastE_mem R r hr), mul_one]`.
-/
theorem pw_term_inv (hD : LocalDatum K R ψ) {m : ℕ} (Φ : ∀ n : ℕ, Matrix (Fin n) (Fin n) K → ℂ)
    (hΦ : PhiHyp R (m + 1) L₀ Λ₀ Q Φ) (t c : K) (u : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (s : K)
    (ξ r : Fin m → K) (hr : ∀ i, r i ∈ R) :
    Φ (m + 1) ((Hm t c (ξ + r) u).submatrix Fin.rev id) * ψ (lastE (ξ + r) + s) =
      Φ (m + 1) ((Hm t c ξ u).submatrix Fin.rev id) * ψ (lastE ξ + s) := by
  have e1 : (Hm t c (ξ + r) u).submatrix Fin.rev id =
      (pw_ro r).submatrix Fin.rev Fin.rev * (Hm t c ξ u).submatrix Fin.rev id * 1 := by
    rw [pw_ro_mul, Matrix.mul_one]
    exact (Matrix.submatrix_mul_equiv (pw_ro r) (Hm t c ξ u) Fin.rev Fin.revPerm id).symm
  have hone : IsInt R (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K) := by
    intro i j
    by_cases h : i = j
    · rw [h, Matrix.one_apply_eq]; exact R.one_mem
    · rw [Matrix.one_apply_ne h]; exact R.zero_mem
  rw [e1, hΦ.1 _ _ _ (pw_ro_low r) (pw_ro_int R r hr) (isUpUni_one K) hone, pw_lastE_add,
    show lastE ξ + lastE r + s = (lastE ξ + s) + lastE r by ring, AddChar.map_add_eq_mul,
    psi_R hD (pw_lastE_mem R r hr), mul_one]

/- English proof (translation)
Establish `h1` using `hΦ.2.1 _ h`. Prove the components needed by the constructor for the conclusion. Introduce `i`. Use `h1 (Fin.rev i) i` as an intermediate fact. Simplify `this` using `[ZZ, HH]`.

Introduce `p`. Use `h1 (Fin.rev p.1.1) p.1.2` as an intermediate fact. Simplify `this` using `[ZZ, HH, p.2.ne, p.2]`.
-/
theorem pw_supp_Z {m : ℕ} (Φ : ∀ n : ℕ, Matrix (Fin n) (Fin n) K → ℂ)
    (hΦ : PhiHyp R (m + 1) L₀ Λ₀ Q Φ) (t : K) (d : Fin (m + 1) → K) (y : Pr (m + 1) → K)
    (h : Φ (m + 1) (ZZ t d y) ≠ 0) : (∀ i, d i ∈ L₀) ∧ ∀ p, y p ∈ L₀ := by
  have h1 := hΦ.2.1 _ h
  constructor
  · intro i
    have := h1 (Fin.rev i) i
    simpa [ZZ, HH] using this
  · intro p
    have := h1 (Fin.rev p.1.1) p.1.2
    simpa [ZZ, HH, p.2.ne, p.2] using this

/- English proof (translation)
Rewrite using `[Fin.prod_univ_succ]`. Simplify using `only [xt, Fin.cons_zero, Fin.cons_succ, x0]`. Rewrite using `[mul_assoc, Ring.inverse_mul_cancel _ (pw_isUnit_prod x hx), mul_one]`.
-/
theorem pw_prod_xt {m : ℕ} (D' : K) (x : Fin m → K) (hx : ∀ k, IsUnit (x k)) :
    ∏ i, xt D' x i = D' := by
  rw [Fin.prod_univ_succ]
  simp only [xt, Fin.cons_zero, Fin.cons_succ, x0]
  rw [mul_assoc, Ring.inverse_mul_cancel _ (pw_isUnit_prod x hx), mul_one]

/- English proof (translation)
Establish `hdet : (ZZ 0 (xt D' x) y).det ∈ Q ∨ -(ZZ 0 (xt D' x) y).det ∈ Q`. Apply the tactic sequence `rcases det_ZZ 0 (xt D' x) y with e | e <;> rw [e, det_HH_zero, pw_prod_xt D' x hx]`. Conclude with `hD'`. Rewrite using `[neg_neg]`. Conclude with `hD'.symm`.

Establish `hY : ∀ i j, (ZZ t (Fin.cons ρ x : Fin (m + 1) → K) y - ZZ 0 (xt D' x) y) i j ∈ Λ₀`. Introduce `i j`. Simplify using `only [Matrix.sub_apply, ZZ, Matrix.submatrix_apply, id, HH]`. Generalize the expression as in `Fin.rev i = i1`. Distinguish the cases in `h1 : i1 = j`.

Substitute `h1` using the available equality. Rewrite using `[if_pos rfl, if_pos rfl]`. Use `Fin.cases ?_ (fun k => ?_) i1` and prove the remaining obligations. Simplify `hC.abelian₂ _ hρ` using `[xt]`. Simplify using `[xt]`.

Rewrite using `[if_neg h1, if_neg h1]`. Distinguish the cases in `h2 : i1 < j`. Rewrite using `[dif_pos h2, dif_pos h2, sub_self]`. Conclude with `Λ₀.zero_mem`. Rewrite using `[dif_neg h2, dif_neg h2]`.

Distinguish the cases in `h3 : j.val + 1 = i1.val`. Rewrite using `[if_pos h3, if_pos h3, sub_zero]`. Conclude with `hC.abelian₂ _ ht`. Rewrite using `[if_neg h3, if_neg h3, sub_self]`. Conclude with `Λ₀.zero_mem`.

Use `hΦ.2.2 _ _ hdet hY` as an intermediate fact. Rewrite `this` using `[add_sub_cancel]`. Then use the resulting hypothesis.
-/
theorem pw_Phi_eq (hC : Cst R ϖ L₀ Λ₀ Q a b) {m : ℕ} (Φ : ∀ n : ℕ, Matrix (Fin n) (Fin n) K → ℂ)
    (hΦ : PhiHyp R (m + 1) L₀ Λ₀ Q Φ) (t D' ρ : K) (hD' : D' ∈ Q ∨ -D' ∈ Q) (x : Fin m → K)
    (y : Pr (m + 1) → K) (hx : ∀ k, IsUnit (x k)) (ht : Sm R ϖ b t) (hρ : Sm R ϖ b (ρ - x0 D' x)) :
    Φ (m + 1) (ZZ t (Fin.cons ρ x : Fin (m + 1) → K) y) = Φ (m + 1) (ZZ 0 (xt D' x) y) := by
  have hdet : (ZZ 0 (xt D' x) y).det ∈ Q ∨ -(ZZ 0 (xt D' x) y).det ∈ Q := by
    rcases det_ZZ 0 (xt D' x) y with e | e <;> rw [e, det_HH_zero, pw_prod_xt D' x hx]
    · exact hD'
    · rw [neg_neg]; exact hD'.symm
  have hY : ∀ i j, (ZZ t (Fin.cons ρ x : Fin (m + 1) → K) y - ZZ 0 (xt D' x) y) i j ∈ Λ₀ := by
    intro i j
    simp only [Matrix.sub_apply, ZZ, Matrix.submatrix_apply, id, HH]
    generalize Fin.rev i = i1
    by_cases h1 : i1 = j
    · subst h1
      rw [if_pos rfl, if_pos rfl]
      refine Fin.cases ?_ (fun k => ?_) i1
      · simpa [xt] using hC.abelian₂ _ hρ
      · simp [xt]
    · rw [if_neg h1, if_neg h1]
      by_cases h2 : i1 < j
      · rw [dif_pos h2, dif_pos h2, sub_self]; exact Λ₀.zero_mem
      · rw [dif_neg h2, dif_neg h2]
        by_cases h3 : j.val + 1 = i1.val
        · rw [if_pos h3, if_pos h3, sub_zero]; exact hC.abelian₂ _ ht
        · rw [if_neg h3, if_neg h3, sub_self]; exact Λ₀.zero_mem
  have := hΦ.2.2 _ _ hdet hY
  rwa [add_sub_cancel] at this

def pw_Good (R : Subring K) (ϖ : Kˣ) (L₀ : AddSubgroup K) (a : ℕ) {m : ℕ} (n : Pr (m + 1) → K) : Prop :=
  (∀ k, xs n k ∈ L₀ ∧ IsUnit (xs n k) ∧ Bd R ϖ ((m + 1) * a) (Ring.inverse (xs n k))) ∧
    ∀ p : Pr (m + 1), p.1.1 ≠ 0 → ys n 0 p ∈ L₀

/- English proof (translation)
Distinguish the cases in `hp : p.1.1 = 0`. Take `⟨⟨i, j⟩, h⟩` from `p`. Simplify using `only at hp`. Substitute `hp` using the available equality. Take `⟨j', rfl⟩` from `Fin.exists_succ_eq.2 (ne_of_gt h)`.

Rewrite using `[pw_ys_zero]`. Conclude with `h2 j'`. Rewrite using `[pw_ys_indep n τ 0 p hp]`. Conclude with `h1 p hp`.
-/
theorem pw_ys_all {m : ℕ} (n : Pr (m + 1) → K) (τ : Fin m → K) (L : AddSubgroup K)
    (h1 : ∀ p : Pr (m + 1), p.1.1 ≠ 0 → ys n 0 p ∈ L) (h2 : ∀ j, τ j ∈ L) (p : Pr (m + 1)) :
    ys n τ p ∈ L := by
  by_cases hp : p.1.1 = 0
  · obtain ⟨⟨i, j⟩, h⟩ := p
    simp only at hp
    subst hp
    obtain ⟨j', rfl⟩ := Fin.exists_succ_eq.2 (ne_of_gt h)
    rw [pw_ys_zero]; exact h2 j'
  · rw [pw_ys_indep n τ 0 p hp]; exact h1 p hp

/- English proof (translation)
Establish `hsh` using `pw_shape hm (t : K) (c : K) ξ N`. Use `set n := (t : K) • N with hn`. Use `set x := xs n with hx`. Use `set τ := pw_Mx (t : K) (1 + EE N) *ᵥ ξ + pw_bv (c : K) with hτ`. Use `set y := ys n τ with hy`.

Establish `hZ : (Hm (t : K) (c : K) ξ (1 + EE N)).submatrix Fin.rev id = ZZ (t : K) (Fin.cons ((t : K) * lastE ξ) x : Fin (m + 1) → K) y` using `by rw [hsh]; rfl`. Establish `hdet : (HH (t : K) (Fin.cons ((t : K) * lastE ξ) x : Fin (m + 1) → K) y).det = (D' : K)`. Rewrite using `[← hsh, det_Hm _ _ _ _ (pw_isUpUni N), hDt]`. Establish `hxu : ∀ k, IsUnit (x k)` using `fun k => (hG.1 k).2.1`. Rewrite using `[hZ]`.

Distinguish the cases in `hτL : ∀ j, τ j ∈ L₀`. Establish `hyL : ∀ p, y p ∈ L₀` using `pw_ys_all n τ L₀ hG.2 hτL`. Take `⟨h1, r, hr, h2⟩` from `hmain _ x y hG.1 hyL hdet`. Rewrite using `[pw_Phi_eq hC Φ hΦ (t : K) (D' : K) _ hQ x y hxu htb h1]`. Establish `ht1 : (t : K) * ((t⁻¹ : Kˣ) : K) = 1` using `by simp`.

Establish `hs : ∑ k, x k = (t : K) * ∑ k, N (sd k)`. Rewrite using `[Finset.mul_sum]`. Both sides reduce to the same expression. Establish `e : lastE ξ + sUp (1 + EE N) = g0 (D' : K) x * ((t⁻¹ : Kˣ) : K) + g1 (D' : K) x y + r`. Rewrite using `[pw_sUp]`.

Unfold `g0`. Rewrite using `[hs]`. Unfold `x0 at h2`. Take the linear combination `h2 - (lastE ξ + ∑ k, N (sd k)) * ht1`. Rewrite using `[e, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, psi_R hD hr, mul_one, GG, if_pos hxu]`.

Take `⟨P, hP⟩` from `pw_isUnit_prod x hxu`. Establish `hpos : (modK R (∏ k, x k) : ℝ) ≠ 0`. Rewrite using `[← hP]`. Conclude with `(modK_pos hC.adic.isOpen hC.adic.isCompact P).ne'`. Establish `hpos' : ((modK R (∏ k, x k) : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast hpos`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Rewrite `hτL` using `[not_forall]`. Take `⟨j, hj⟩` from `hτL`. Establish `z1 : Φ (m + 1) (ZZ (t : K) (Fin.cons ((t : K) * lastE ξ) x : Fin (m + 1) → K) y) = 0`.

Assume the negation of the conclusion as `h`. Use `(pw_supp_Z Φ hΦ _ _ _ h).2 ⟨(0, j.succ), Fin.succ_pos j⟩` as an intermediate fact. Rewrite `this` using `[hy, pw_ys_zero]`. Conclude with `hj this`. Establish `z2 : GG R ψ Φ (D' : K) x y = 0`.

Assume the negation of the conclusion as `h`. Use `(GG_supp hC Φ hΦ D' hQ x y h).2.1 ⟨(0, j.succ), Fin.succ_pos j⟩` as an intermediate fact. Rewrite `this` using `[hy, pw_ys_zero]`. Conclude with `hj this`. Rewrite using `[z1, z2, zero_mul, mul_zero]`.
-/
theorem pw_point (hD : LocalDatum K R ψ) (hC : Cst R ϖ L₀ Λ₀ Q a b) {m : ℕ} (hm : 1 ≤ m)
    (Φ : ∀ n : ℕ, Matrix (Fin n) (Fin n) K → ℂ) (hΦ : PhiHyp R (m + 1) L₀ Λ₀ Q Φ) (t c D' : Kˣ)
    (htb : Sm R ϖ b (t : K)) (hDt : (D' : K) = (-1) ^ m * ((c : K) * (t : K) ^ m))
    (hQ : (D' : K) ∈ Q ∨ -(D' : K) ∈ Q)
    (hmain : ∀ (ρ : K) (x : Fin m → K) (y : Pr (m + 1) → K),
      (∀ k, x k ∈ L₀ ∧ IsUnit (x k) ∧ Bd R ϖ ((m + 1) * a) (Ring.inverse (x k))) →
      (∀ p, y p ∈ L₀) → (HH (t : K) (Fin.cons ρ x : Fin (m + 1) → K) y).det = (D' : K) →
      Sm R ϖ b (ρ - x0 (D' : K) x) ∧
      ∃ r ∈ R, ρ * ((t⁻¹ : Kˣ) : K) = x0 (D' : K) x * ((t⁻¹ : Kˣ) : K) + g1 (D' : K) x y + r)
    (N : Pr (m + 1) → K) (hG : pw_Good R ϖ L₀ a ((t : K) • N)) (ξ : Fin m → K) :
    Φ (m + 1) ((Hm (t : K) (c : K) ξ (1 + EE N)).submatrix Fin.rev id) *
        ψ (lastE ξ + sUp (1 + EE N)) =
      ψ (g0 (D' : K) (xs ((t : K) • N)) * ((t⁻¹ : Kˣ) : K)) *
        ((modK R (∏ k, xs ((t : K) • N) k) : ℝ) : ℂ) *
        GG R ψ Φ (D' : K) (xs ((t : K) • N))
          (ys ((t : K) • N) (pw_Mx (t : K) (1 + EE N) *ᵥ ξ + pw_bv (c : K))) := by
  have hsh := pw_shape hm (t : K) (c : K) ξ N
  set n := (t : K) • N with hn
  set x := xs n with hx
  set τ := pw_Mx (t : K) (1 + EE N) *ᵥ ξ + pw_bv (c : K) with hτ
  set y := ys n τ with hy
  have hZ : (Hm (t : K) (c : K) ξ (1 + EE N)).submatrix Fin.rev id =
      ZZ (t : K) (Fin.cons ((t : K) * lastE ξ) x : Fin (m + 1) → K) y := by rw [hsh]; rfl
  have hdet : (HH (t : K) (Fin.cons ((t : K) * lastE ξ) x : Fin (m + 1) → K) y).det = (D' : K) := by
    rw [← hsh, det_Hm _ _ _ _ (pw_isUpUni N), hDt]
  have hxu : ∀ k, IsUnit (x k) := fun k => (hG.1 k).2.1
  rw [hZ]
  by_cases hτL : ∀ j, τ j ∈ L₀
  · have hyL : ∀ p, y p ∈ L₀ := pw_ys_all n τ L₀ hG.2 hτL
    obtain ⟨h1, r, hr, h2⟩ := hmain _ x y hG.1 hyL hdet
    rw [pw_Phi_eq hC Φ hΦ (t : K) (D' : K) _ hQ x y hxu htb h1]
    have ht1 : (t : K) * ((t⁻¹ : Kˣ) : K) = 1 := by simp
    have hs : ∑ k, x k = (t : K) * ∑ k, N (sd k) := by
      rw [Finset.mul_sum]; rfl
    have e : lastE ξ + sUp (1 + EE N) =
        g0 (D' : K) x * ((t⁻¹ : Kˣ) : K) + g1 (D' : K) x y + r := by
      rw [pw_sUp]
      unfold g0
      rw [hs]
      unfold x0 at h2
      linear_combination h2 - (lastE ξ + ∑ k, N (sd k)) * ht1
    rw [e, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, psi_R hD hr, mul_one, GG, if_pos hxu]
    obtain ⟨P, hP⟩ := pw_isUnit_prod x hxu
    have hpos : (modK R (∏ k, x k) : ℝ) ≠ 0 := by
      rw [← hP]; exact (modK_pos hC.adic.isOpen hC.adic.isCompact P).ne'
    have hpos' : ((modK R (∏ k, x k) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos
    push_cast
    field_simp
  · rw [not_forall] at hτL
    obtain ⟨j, hj⟩ := hτL
    have z1 : Φ (m + 1) (ZZ (t : K) (Fin.cons ((t : K) * lastE ξ) x : Fin (m + 1) → K) y) = 0 := by
      by_contra h
      have := (pw_supp_Z Φ hΦ _ _ _ h).2 ⟨(0, j.succ), Fin.succ_pos j⟩
      rw [hy, pw_ys_zero] at this
      exact hj this
    have z2 : GG R ψ Φ (D' : K) x y = 0 := by
      by_contra h
      have := (GG_supp hC Φ hΦ D' hQ x y h).2.1 ⟨(0, j.succ), Fin.succ_pos j⟩
      rw [hy, pw_ys_zero] at this
      exact hj this
    rw [z1, z2, zero_mul, mul_zero]

end PWc

section PW

variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ} {ϖ : Kˣ} {L₀ Λ₀ : AddSubgroup K} {Q : Set K} {a b : ℕ}

/- English proof (translation)
Take `⟨M₁, h₁⟩` from `pw_units hC m`. Take `⟨M₂, h₂⟩` from `pw_main hC m hm`. Take `⟨M₃, h₃⟩` from `pw_det hC m`. Use `⟨M₁ + M₂ + M₃ + b, ?_⟩` and prove the remaining obligations. Introduce `Φ hΦ t c D' ht hDt hQ Λ₁ hΛ₁ hGinv N`.

Establish `hϖ` using `hC.adic.mem`. Establish `ht1 : Sm R ϖ M₁ (t : K)` using `ht.mono hϖ (by omega)`. Establish `ht2 : Sm R ϖ M₂ (t : K)` using `ht.mono hϖ (by omega)`. Establish `ht3 : Sm R ϖ M₃ (t : K)` using `ht.mono hϖ (by omega)`. Establish `htb : Sm R ϖ b (t : K)` using `ht.mono hϖ (by omega)`.

Distinguish the cases in `hG : pw_Good R ϖ L₀ a ((t : K) • N)`. Establish `hpt` using `pw_point hD hC hm Φ hΦ t c D' htb hDt hQ (h₂ t ht2 D' hQ) N hG`. Establish `hsh` using `pw_shape hm (t : K) (c : K) 0 N`. Take `⟨hu, hmod⟩` from `h₃ (t : K) ht3 ((t : K) * lastE (0 : Fin m → K)) (xs ((t : K) • N)) (ys ((t : K) • N) (pw_Mx (t : K) (1 + EE N) *ᵥ 0 + pw_bv (c : K))) hG.1 (fun p hp => by rw [pw_ys_indep _ _ 0 p hp]; exact hG.2 p hp)`. Rewrite `hu`, `hmod` using `[← hsh]`.

Establish `hMx : pw_Mx (t : K) (1 + EE N) = (((Hm (t : K) (c : K) 0 (1 + EE N)).submatrix Fin.succ Fin.succ).submatrix Fin.rev id)ᵀ`. Use extensionality with `j k`. Simplify using `[pw_Mx, Hm]`. Establish `hMu : IsUnit (pw_Mx (t : K) (1 + EE N)).det`. Rewrite using `[hMx, Matrix.det_transpose]`.

Break down `pw_det_rev ((Hm (t : K) (c : K) 0 (1 + EE N)).submatrix Fin.succ Fin.succ) with e | e` into its components or cases. Rewrite using `[e]`. Conclude with `hu`. Rewrite using `[e]`. Conclude with `hu.neg`.

Establish `hMm : modK R (pw_Mx (t : K) (1 + EE N)).det = modK R (∏ k, xs ((t : K) • N) k)`. Rewrite using `[hMx, Matrix.det_transpose]`. Break down `pw_det_rev ((Hm (t : K) (c : K) 0 (1 + EE N)).submatrix Fin.succ Fin.succ) with e | e` into its components or cases. Rewrite using `[e]`. Conclude with `hmod`.

Rewrite using `[e, modK_neg]`. Conclude with `hmod`. Take `⟨P, hP⟩` from `pw_isUnit_prod (xs ((t : K) • N)) (fun k => (hG.1 k).2.1)`. Establish `hpos : ((modK R (∏ k, xs ((t : K) • N) k) : ℝ) : ℂ) ≠ 0`. Establish `: (modK R (∏ k, xs ((t : K) • N) k) : ℝ) ≠ 0`.

Rewrite using `[← hP]`. Conclude with `(modK_pos hC.adic.isOpen hC.adic.isCompact P).ne'`. Conclude with `this` after adjusting the coercions. Establish `hinv : BInv Λ₁ (fun τ => GG R ψ Φ (D' : K) (xs ((t : K) • N)) (ys ((t : K) • N) τ))`. Introduce `τ l hl`.

Use `show GG R ψ Φ (D' : K) _ (ys ((t : K) • N) (τ + l)) = _`. Rewrite using `[pw_ys_add]`. Conclude with `hGinv _ _ _ (pw_ys_mem Λ₁ l hl)`. Establish `hs : BSupp L₀ (fun τ => GG R ψ Φ (D' : K) (xs ((t : K) • N)) (ys ((t : K) • N) τ))`. Introduce `τ h j`.

Use `(GG_supp hC Φ hΦ D' hQ _ _ h).2.1 ⟨(0, j.succ), Fin.succ_pos j⟩` as an intermediate fact. Rewrite `this` using `[pw_ys_zero]`. Then use the resulting hypothesis. Establish `hR : ∀ ξ r : Fin m → K, (∀ i, r i ∈ R) → GG R ψ Φ (D' : K) (xs ((t : K) • N)) (ys ((t : K) • N) (pw_Mx (t : K) (1 + EE N) *ᵥ (ξ + r) + pw_bv (c : K))) = GG R ψ Φ (D' : K) (xs ((t : K) • N)) (ys ((t : K) • N) (pw_Mx (t : K) (1 + EE N) *ᵥ ξ + pw_bv (c : K)))`. Introduce `ξ r hr`. Establish `e1` using `hpt (ξ + r)`.

Rewrite `e1` using `[pw_term_inv hD Φ hΦ _ _ _ _ ξ r hr, hpt ξ]`. Conclude with `(mul_left_cancel₀ (mul_ne_zero (pw_psi_ne ψ _) hpos) e1).symm`. Rewrite using `[bx_lin hD (pw_Mx (t : K) (1 + EE N)) hMu (pw_bv (c : K)) hΛ₁ hL₀ _ hinv hs hR, hMm, ← mul_assoc, ← pw_mul_finsum]`. Conclude with `finsum_congr fun q => hpt (outV R q)`. Establish `hL : ∀ ξ : Fin m → K, Φ (m + 1) ((Hm (t : K) (c : K) ξ (1 + EE N)).submatrix Fin.rev id) = 0`.

Introduce `ξ`. Assume the negation of the conclusion as `h`. Apply `hG` to reduce the goal to its premises. Establish `hsh` using `pw_shape hm (t : K) (c : K) ξ N`. Establish `hdet` using `det_Hm (t : K) (c : K) ξ (1 + EE N) (pw_isUpUni N)`.

Rewrite `hdet` using `[← hDt]`. Rewrite `h`, `hdet` using `[hsh]`. Take `⟨hd, hy⟩` from `pw_supp_Z Φ hΦ _ _ _ h`. Establish `hρ` using `hd 0`. Establish `hx : ∀ k, xs ((t : K) • N) k ∈ L₀` using `fun k => by simpa using hd k.succ`.

Rewrite `hρ` using `[Fin.cons_zero]`. Use `h₁ (t : K) ht1 D' hQ _ _ _ hρ hx hy hdet` as an intermediate fact. Conclude with `⟨fun k => ⟨hx k, this k⟩, fun p hp => by rw [pw_ys_indep _ 0 _ p hp]; exact hy p⟩`. Establish `hRz : ∀ τ : Fin m → K, GG R ψ Φ (D' : K) (xs ((t : K) • N)) (ys ((t : K) • N) τ) = 0`. Introduce `τ`.

Assume the negation of the conclusion as `h`. Apply `hG` to reduce the goal to its premises. Take `⟨g1, g2, -⟩` from `GG_supp hC Φ hΦ D' hQ _ _ h`. Conclude with `⟨g1, fun p hp => by rw [pw_ys_indep _ 0 τ p hp]; exact g2 p⟩`. Simplify using `only [hL, hRz, zero_mul, finsum_zero, bx_zero, mul_zero]`.
-/
theorem levelA (hD : LocalDatum K R ψ) (hC : Cst R ϖ L₀ Λ₀ Q a b) (hL₀ : IsLat L₀) (m : ℕ)
    (hm : 1 ≤ m) :
    ∃ M : ℕ, ∀ Φ : ∀ n : ℕ, Matrix (Fin n) (Fin n) K → ℂ, PhiHyp R (m + 1) L₀ Λ₀ Q Φ →
    ∀ t c D' : Kˣ, Sm R ϖ M (t : K) → (D' : K) = (-1) ^ m * ((c : K) * (t : K) ^ m) →
    ((D' : K) ∈ Q ∨ -(D' : K) ∈ Q) →
    ∀ Λ₁ : AddSubgroup K, IsLat Λ₁ → (∀ x : Fin m → K, BInv Λ₁ (GG R ψ Φ (D' : K) x)) →
    ∀ N : Pr (m + 1) → K,
      ∑ᶠ ξ : Fin m → KR R,
        Φ (m + 1) ((Hm (t : K) (c : K) (outV R ξ) (1 + EE N)).submatrix Fin.rev id) *
          ψ (lastE (outV R ξ) + sUp (1 + EE N)) =
      ψ (g0 (D' : K) (xs ((t : K) • N)) * ((t⁻¹ : Kˣ) : K)) *
        bx R Λ₁ (Fin m) (fun τ => GG R ψ Φ (D' : K) (xs ((t : K) • N)) (ys ((t : K) • N) τ)) := by
  obtain ⟨M₁, h₁⟩ := pw_units hC m
  obtain ⟨M₂, h₂⟩ := pw_main hC m hm
  obtain ⟨M₃, h₃⟩ := pw_det hC m
  refine ⟨M₁ + M₂ + M₃ + b, ?_⟩
  intro Φ hΦ t c D' ht hDt hQ Λ₁ hΛ₁ hGinv N
  have hϖ := hC.adic.mem
  have ht1 : Sm R ϖ M₁ (t : K) := ht.mono hϖ (by omega)
  have ht2 : Sm R ϖ M₂ (t : K) := ht.mono hϖ (by omega)
  have ht3 : Sm R ϖ M₃ (t : K) := ht.mono hϖ (by omega)
  have htb : Sm R ϖ b (t : K) := ht.mono hϖ (by omega)
  by_cases hG : pw_Good R ϖ L₀ a ((t : K) • N)
  · have hpt := pw_point hD hC hm Φ hΦ t c D' htb hDt hQ (h₂ t ht2 D' hQ) N hG
    have hsh := pw_shape hm (t : K) (c : K) 0 N
    obtain ⟨hu, hmod⟩ := h₃ (t : K) ht3 ((t : K) * lastE (0 : Fin m → K)) (xs ((t : K) • N))
      (ys ((t : K) • N) (pw_Mx (t : K) (1 + EE N) *ᵥ 0 + pw_bv (c : K))) hG.1
      (fun p hp => by rw [pw_ys_indep _ _ 0 p hp]; exact hG.2 p hp)
    rw [← hsh] at hu hmod
    have hMx : pw_Mx (t : K) (1 + EE N) =
        (((Hm (t : K) (c : K) 0 (1 + EE N)).submatrix Fin.succ Fin.succ).submatrix Fin.rev id)ᵀ := by
      ext j k
      simp [pw_Mx, Hm]
    have hMu : IsUnit (pw_Mx (t : K) (1 + EE N)).det := by
      rw [hMx, Matrix.det_transpose]
      rcases pw_det_rev ((Hm (t : K) (c : K) 0 (1 + EE N)).submatrix Fin.succ Fin.succ) with e | e
      · rw [e]; exact hu
      · rw [e]; exact hu.neg
    have hMm : modK R (pw_Mx (t : K) (1 + EE N)).det = modK R (∏ k, xs ((t : K) • N) k) := by
      rw [hMx, Matrix.det_transpose]
      rcases pw_det_rev ((Hm (t : K) (c : K) 0 (1 + EE N)).submatrix Fin.succ Fin.succ) with e | e
      · rw [e]; exact hmod
      · rw [e, modK_neg]; exact hmod
    obtain ⟨P, hP⟩ := pw_isUnit_prod (xs ((t : K) • N)) (fun k => (hG.1 k).2.1)
    have hpos : ((modK R (∏ k, xs ((t : K) • N) k) : ℝ) : ℂ) ≠ 0 := by
      have : (modK R (∏ k, xs ((t : K) • N) k) : ℝ) ≠ 0 := by
        rw [← hP]; exact (modK_pos hC.adic.isOpen hC.adic.isCompact P).ne'
      exact_mod_cast this
    have hinv : BInv Λ₁ (fun τ => GG R ψ Φ (D' : K) (xs ((t : K) • N)) (ys ((t : K) • N) τ)) := by
      intro τ l hl
      show GG R ψ Φ (D' : K) _ (ys ((t : K) • N) (τ + l)) = _
      rw [pw_ys_add]
      exact hGinv _ _ _ (pw_ys_mem Λ₁ l hl)
    have hs : BSupp L₀ (fun τ => GG R ψ Φ (D' : K) (xs ((t : K) • N)) (ys ((t : K) • N) τ)) := by
      intro τ h j
      have := (GG_supp hC Φ hΦ D' hQ _ _ h).2.1 ⟨(0, j.succ), Fin.succ_pos j⟩
      rwa [pw_ys_zero] at this
    have hR : ∀ ξ r : Fin m → K, (∀ i, r i ∈ R) →
        GG R ψ Φ (D' : K) (xs ((t : K) • N))
          (ys ((t : K) • N) (pw_Mx (t : K) (1 + EE N) *ᵥ (ξ + r) + pw_bv (c : K))) =
        GG R ψ Φ (D' : K) (xs ((t : K) • N))
          (ys ((t : K) • N) (pw_Mx (t : K) (1 + EE N) *ᵥ ξ + pw_bv (c : K))) := by
      intro ξ r hr
      have e1 := hpt (ξ + r)
      rw [pw_term_inv hD Φ hΦ _ _ _ _ ξ r hr, hpt ξ] at e1
      exact (mul_left_cancel₀ (mul_ne_zero (pw_psi_ne ψ _) hpos) e1).symm
    rw [bx_lin hD (pw_Mx (t : K) (1 + EE N)) hMu (pw_bv (c : K)) hΛ₁ hL₀ _ hinv hs hR, hMm,
      ← mul_assoc, ← pw_mul_finsum]
    exact finsum_congr fun q => hpt (outV R q)
  · have hL : ∀ ξ : Fin m → K,
        Φ (m + 1) ((Hm (t : K) (c : K) ξ (1 + EE N)).submatrix Fin.rev id) = 0 := by
      intro ξ
      by_contra h
      apply hG
      have hsh := pw_shape hm (t : K) (c : K) ξ N
      have hdet := det_Hm (t : K) (c : K) ξ (1 + EE N) (pw_isUpUni N)
      rw [← hDt] at hdet
      rw [hsh] at h hdet
      obtain ⟨hd, hy⟩ := pw_supp_Z Φ hΦ _ _ _ h
      have hρ := hd 0
      have hx : ∀ k, xs ((t : K) • N) k ∈ L₀ := fun k => by simpa using hd k.succ
      rw [Fin.cons_zero] at hρ
      have := h₁ (t : K) ht1 D' hQ _ _ _ hρ hx hy hdet
      exact ⟨fun k => ⟨hx k, this k⟩, fun p hp => by rw [pw_ys_indep _ 0 _ p hp]; exact hy p⟩
    have hRz : ∀ τ : Fin m → K,
        GG R ψ Φ (D' : K) (xs ((t : K) • N)) (ys ((t : K) • N) τ) = 0 := by
      intro τ
      by_contra h
      apply hG
      obtain ⟨g1, g2, -⟩ := GG_supp hC Φ hΦ D' hQ _ _ h
      exact ⟨g1, fun p hp => by rw [pw_ys_indep _ 0 τ p hp]; exact g2 p⟩
    simp only [hL, hRz, zero_mul, finsum_zero, bx_zero, mul_zero]

end PW

section FA0

variable {K : Type} [CommRing K]

/- English proof (translation)
Set `e : Pr n ≃ Σ j : Fin n, {i : Fin n // i < j}` to `{ toFun := fun p => ⟨p.1.2, ⟨p.1.1, p.2⟩⟩ invFun := fun q => ⟨(q.2.1, q.1), q.2.2⟩ left_inv := fun _ => rfl right_inv := fun _ => rfl }`. Establish `h : ∀ j : Fin n, Fintype.card {i : Fin n // i < j} = (j : ℕ)`. Introduce `j`. Rewrite using `[Fintype.card_subtype, Finset.filter_gt_eq_Iio]`. Conclude with `Fin.card_Iio j`.

Rewrite using `[Fintype.card_congr e, Fintype.card_sigma]`. Simplify using `only [h]`. Rewrite using `[Fin.sum_univ_eq_sum_range (fun i => i) n, Finset.sum_range_id]`.
-/
theorem fa_card_Pr (n : ℕ) : Fintype.card (Pr n) = n * (n - 1) / 2 := by

  let e : Pr n ≃ Σ j : Fin n, {i : Fin n // i < j} :=
    { toFun := fun p => ⟨p.1.2, ⟨p.1.1, p.2⟩⟩
      invFun := fun q => ⟨(q.2.1, q.1), q.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h : ∀ j : Fin n, Fintype.card {i : Fin n // i < j} = (j : ℕ) := by
    intro j
    rw [Fintype.card_subtype, Finset.filter_gt_eq_Iio]
    exact Fin.card_Iio j
  rw [Fintype.card_congr e, Fintype.card_sigma]
  simp only [h]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) n, Finset.sum_range_id]

/- English proof (translation)
Introduce and unpack `(i | p) (j | q) h`. Simplify using `only [ee, sd, Sum.inl.injEq, Subtype.mk.injEq, Prod.mk.injEq] at h`. Rewrite using `[Fin.succ_inj.1 h.2]`. It suffices to derive a contradiction. Simplify using `only [ee] at h`.

Use `split_ifs at h with h0`. Simplify using `only [sd, Sum.inl.injEq, Subtype.mk.injEq, Prod.mk.injEq] at h`. Establish `h1` using `congrArg Fin.val h.1`. Establish `h2` using `congrArg Fin.val h.2`. Establish `h3` using `q.2`.

Rewrite `h3` using `[Fin.lt_def]`. Simplify using `only [Fin.val_castSucc, Fin.val_pred, Fin.val_succ] at h1 h2`. Establish `h4 : q.1.1.val ≠ 0` using `fun h5 => h0 (Fin.ext h5)`. Use linear arithmetic over natural numbers and integers. It suffices to derive a contradiction.

Simplify using `only [ee] at h`. Use `split_ifs at h with h0`. Simplify using `only [sd, Sum.inl.injEq, Subtype.mk.injEq, Prod.mk.injEq] at h`. Establish `h1` using `congrArg Fin.val h.1`. Establish `h2` using `congrArg Fin.val h.2`.

Establish `h3` using `p.2`. Rewrite `h3` using `[Fin.lt_def]`. Simplify using `only [Fin.val_castSucc, Fin.val_pred, Fin.val_succ] at h1 h2`. Establish `h4 : p.1.1.val ≠ 0` using `fun h5 => h0 (Fin.ext h5)`. Use linear arithmetic over natural numbers and integers.

Simplify using `only [ee] at h`. Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Prod.ext` to reduce the goal to its premises. Use `split_ifs at h with h0 h1 h1`.

Rewrite using `[h0, h1]`. Simplify using `only [Sum.inl.injEq, Subtype.mk.injEq, Prod.mk.injEq] at h`. Use `Fin.castSucc_inj.1 h.1` as an intermediate fact. Conclude with `Fin.pred_inj.1 this`. Use `split_ifs at h with h0 h1 h1`.

Simplify using `only [Sum.inr.injEq] at h`. Conclude with `Fin.pred_inj.1 h`. Simplify using `only [Sum.inl.injEq, Subtype.mk.injEq, Prod.mk.injEq] at h`. Conclude with `h.2`.
-/
theorem fa_ee_inj {m : ℕ} : Function.Injective (ee : Fin m ⊕ Pr (m + 1) → Pr (m + 1) ⊕ Fin m) := by
  rintro (i | p) (j | q) h
  · simp only [ee, sd, Sum.inl.injEq, Subtype.mk.injEq, Prod.mk.injEq] at h
    rw [Fin.succ_inj.1 h.2]
  · exfalso
    simp only [ee] at h
    split_ifs at h with h0
    simp only [sd, Sum.inl.injEq, Subtype.mk.injEq, Prod.mk.injEq] at h
    have h1 := congrArg Fin.val h.1
    have h2 := congrArg Fin.val h.2
    have h3 := q.2
    rw [Fin.lt_def] at h3
    simp only [Fin.val_castSucc, Fin.val_pred, Fin.val_succ] at h1 h2
    have h4 : q.1.1.val ≠ 0 := fun h5 => h0 (Fin.ext h5)
    omega
  · exfalso
    simp only [ee] at h
    split_ifs at h with h0
    simp only [sd, Sum.inl.injEq, Subtype.mk.injEq, Prod.mk.injEq] at h
    have h1 := congrArg Fin.val h.1
    have h2 := congrArg Fin.val h.2
    have h3 := p.2
    rw [Fin.lt_def] at h3
    simp only [Fin.val_castSucc, Fin.val_pred, Fin.val_succ] at h1 h2
    have h4 : p.1.1.val ≠ 0 := fun h5 => h0 (Fin.ext h5)
    omega
  · simp only [ee] at h
    congr 1
    apply Subtype.ext
    apply Prod.ext
    · split_ifs at h with h0 h1 h1
      · rw [h0, h1]
      · simp only [Sum.inl.injEq, Subtype.mk.injEq, Prod.mk.injEq] at h
        have := Fin.castSucc_inj.1 h.1
        exact Fin.pred_inj.1 this
    · split_ifs at h with h0 h1 h1
      · simp only [Sum.inr.injEq] at h
        exact Fin.pred_inj.1 h
      · simp only [Sum.inl.injEq, Subtype.mk.injEq, Prod.mk.injEq] at h
        exact h.2

/- English proof (translation)
Rewrite using `[Fintype.bijective_iff_injective_and_card]`. Conclude with `⟨fa_ee_inj, by simp [add_comm]⟩`.
-/
theorem fa_ee_bij {m : ℕ} : Function.Bijective (ee : Fin m ⊕ Pr (m + 1) → Pr (m + 1) ⊕ Fin m) := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨fa_ee_inj, by simp [add_comm]⟩

/- English proof (translation)
Establish `hlast : ∀ j, r (Fin.last m) j = if j = Fin.last m then 1 else 0`. Introduce `j`. Use `split_ifs with h`. Rewrite using `[h]`. Conclude with `hr.2 _`.

Conclude with `hr.1 (lt_of_le_of_ne (Fin.le_last j) h)`. Use extensionality with `i j`. Use `Fin.cases ?_ (fun i' => ?_) i` and prove the remaining obligations. Simplify using `only [Hm, Fin.cases_zero, Matrix.mul_apply, add_mul, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]`. Use `congr 1`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring` and prove the remaining obligations. Simplify using `[hlast]`. Simplify using `only [Hm, Fin.cases_succ, Matrix.mul_apply, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun l _ => by ring` and prove the remaining obligations.
-/
theorem fa_Hm_mul {m : ℕ} (t c : K) (ξ : Fin m → K) (u r : Matrix (Fin (m + 1)) (Fin (m + 1)) K)
    (hr : IsUpUni r) : Hm t c ξ (u * r) = Hm t c ξ u * r := by
  have hlast : ∀ j, r (Fin.last m) j = if j = Fin.last m then 1 else 0 := by
    intro j
    split_ifs with h
    · rw [h]; exact hr.2 _
    · exact hr.1 (lt_of_le_of_ne (Fin.le_last j) h)
  ext i j
  refine Fin.cases ?_ (fun i' => ?_) i
  · simp only [Hm, Fin.cases_zero, Matrix.mul_apply, add_mul, Finset.sum_add_distrib,
      Finset.sum_mul, Finset.mul_sum]
    congr 1
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
    · simp [hlast]
  · simp only [Hm, Fin.cases_succ, Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => by ring

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Matrix.mul_apply]`.
-/
theorem fa_sub_mul {n : ℕ} (A r : Matrix (Fin n) (Fin n) K) :
    (A * r).submatrix Fin.rev id = 1 * A.submatrix Fin.rev id * r := by
  ext i j
  simp [Matrix.mul_apply]

/- English proof (translation)
Unfold `sUp`. Rewrite using `[Fin.sum_univ_castSucc]`. Simplify using `only [Fin.val_last, lt_self_iff_false, dite_false, add_zero, Fin.val_castSucc, add_lt_add_iff_right, Fin.is_lt, dite_true]`. Both sides reduce to the same expression.
-/
theorem fa_sUp {m : ℕ} (u : Matrix (Fin (m + 1)) (Fin (m + 1)) K) :
    sUp u = ∑ i : Fin m, u i.castSucc i.succ := by
  unfold sUp
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_last, lt_self_iff_false, dite_false, add_zero, Fin.val_castSucc,
    add_lt_add_iff_right, Fin.is_lt, dite_true]
  rfl

/- English proof (translation)
Rewrite using `[fa_sUp]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `h : i.castSucc < i.succ` using `Fin.castSucc_lt_succ`. Simplify using `[EE, h, h.ne, sd]`.
-/
theorem fa_sUp_EE {m : ℕ} (N : Pr (m + 1) → K) : sUp (1 + EE N) = ∑ i : Fin m, N (sd i) := by
  rw [fa_sUp]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : i.castSucc < i.succ := Fin.castSucc_lt_succ
  simp [EE, h, h.ne, sd]

/- English proof (translation)
Use extensionality with `i j`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using `[HH, EE]`. Distinguish the cases in `h2 : i < j`.

Simplify using `[HH, EE, h, h2]`. Simplify using `[HH, EE, h, h2]`.
-/
theorem fa_smul_EE {n : ℕ} (z : K) (N : Pr n → K) :
    z • (1 + EE N) = HH 0 (fun _ => z) (z • N) := by
  ext i j
  by_cases h : i = j
  · subst h; simp [HH, EE]
  · by_cases h2 : i < j
    · simp [HH, EE, h, h2]
    · simp [HH, EE, h, h2]

end FA0

section FA1

variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ} {ϖ : Kˣ} {L₀ Λ₀ : AddSubgroup K} {Q : Set K} {a b : ℕ}

/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.A6x3.lat_iff.2 (lat_mulR hA.isOpen hA.isCompact u)`.
-/
theorem fa_lat (hA : Adic R ϖ) (u : Kˣ) : IsLat (mulR R (u : K)) :=
  Formalism.FourierDecayAlt.P.A6x3.lat_iff.2 (lat_mulR hA.isOpen hA.isCompact u)

/- English proof (translation)
Simplify using `only [mulR, AddSubgroup.mem_map, Subring.mem_toAddSubgroup, AddMonoidHom.coe_mulLeft]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨r, hr, rfl⟩`. Conclude with `⟨r, hr, rfl⟩`. Introduce and unpack `⟨r, hr, rfl⟩`.

Conclude with `⟨r, hr, rfl⟩`.
-/
theorem fa_mem_mulR {c x : K} : x ∈ mulR R c ↔ ∃ r ∈ R, x = c * r := by
  simp only [mulR, AddSubgroup.mem_map, Subring.mem_toAddSubgroup, AddMonoidHom.coe_mulLeft]
  constructor
  · rintro ⟨r, hr, rfl⟩; exact ⟨r, hr, rfl⟩
  · rintro ⟨r, hr, rfl⟩; exact ⟨r, hr, rfl⟩

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp [modK_one]`. Consider the case `succ n ih`. Rewrite using `[pow_succ, pow_succ, ← ih]`. Conclude with `modK_mul_isUnit hA (z.isUnit.pow n) z.isUnit`.
-/
theorem fa_modK_pow (hA : Adic R ϖ) (z : Kˣ) (n : ℕ) : modK R ((z : K) ^ n) = modK R (z : K) ^ n := by
  induction n with
  | zero => simp [modK_one]
  | succ n ih =>
    rw [pow_succ, pow_succ, ← ih]
    exact modK_mul_isUnit hA (z.isUnit.pow n) z.isUnit

def InvP (R : Subring K) (ψ : AddChar K ℂ) (ϖ : Kˣ) (Φ : ∀ n : ℕ, Matrix (Fin n) (Fin n) K → ℂ)
    (m : ℕ) (D' : K) (b₁ : ℕ) : Prop :=
  ∀ μ ∈ R, ∀ (x l : Fin m → K) (y l' : Pr (m + 1) → K),
    (∀ k, ∃ r ∈ R, l k = μ * (ϖ : K) ^ b₁ * r) → (∀ p, ∃ r ∈ R, l' p = μ * (ϖ : K) ^ b₁ * r) →
    GG R ψ Φ D' (x + l) (y + l') = GG R ψ Φ D' x y ∧
    (GG R ψ Φ D' x y ≠ 0 → ∃ r ∈ R, g0 D' (x + l) - g0 D' x = μ * r)

/- English proof (translation)
Introduce `y l' hl'`. Use `(hI 1 R.one_mem x 0 y l' (fun k => ⟨0, R.zero_mem, by simp⟩) (fun p => by` as an intermediate fact. Take `⟨r, hr, e⟩` from `fa_mem_mulR.1 (hl' p)`. Conclude with `⟨r, hr, by rw [e]; simp⟩)).1`. Simplify using `using this`.
-/
theorem fa_inv_y {Φ : ∀ n : ℕ, Matrix (Fin n) (Fin n) K → ℂ} {m : ℕ} {D' : K} {b₁ : ℕ}
    (hI : InvP R ψ ϖ Φ m D' b₁) (x : Fin m → K) :
    BInv (mulR R (((ϖ ^ b₁ : Kˣ) : Kˣ) : K)) (GG R ψ Φ D' x) := by
  intro y l' hl'
  have := (hI 1 R.one_mem x 0 y l' (fun k => ⟨0, R.zero_mem, by simp⟩) (fun p => by
    obtain ⟨r, hr, e⟩ := fa_mem_mulR.1 (hl' p)
    exact ⟨r, hr, by rw [e]; simp⟩)).1
  simpa using this

/- English proof (translation)
Establish `hϖ` using `hC.adic.mem`. Establish `hmem : ∀ x : K, Bd R ϖ ((m + 1) * a) x → x ∈ mulR R ((ϖ⁻¹ ^ ((m + 1) * a) : Kˣ) : K)`. Introduce `x hx`. Take `⟨r, hr, e⟩` from `bd_iff_sm_mul.1 hx`. Conclude with `fa_mem_mulR.2 ⟨r, hr, by rw [e]; simp⟩`.

Prove the components needed by the constructor for the conclusion. Introduce `x hx k`. Establish `: ∃ y, GG R ψ Φ (D' : K) x y ≠ 0`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`.

Apply `hx` to reduce the goal to its premises. Use `show bx R _ (Pr (m + 1)) (GG R ψ Φ (D' : K) x) = 0`. Rewrite using `[bx_congr _ hcon, bx_zero]`. Take `⟨y, hy⟩` from `this`. Take `⟨h1, -, -⟩` from `GG_supp hC Φ hΦ D' hD' x y hy`.

Take `⟨h2, h3, h4⟩` from `h1 k`. Use `⟨hmem _ (Bd.mono hϖ ?_ (hC.L0 _ h2)), h3, hmem _ h4⟩` and prove the remaining obligations. Use the polynomial consequences of the given equalities and inequalities. Introduce `x l hl`. Use `bx_congr _ fun y => ?_` and prove the remaining obligations.

Use `(hI 1 R.one_mem x l y 0 (fun k => by` as an intermediate fact. Take `⟨r, hr, e⟩` from `fa_mem_mulR.1 (hl k)`. Conclude with `⟨r, hr, by rw [e]; simp⟩) (fun p => ⟨0, R.zero_mem, by simp⟩)).1`. Simplify using `using this`.
-/
theorem fa_amp (hC : Cst R ϖ L₀ Λ₀ Q a b) {m : ℕ} (Φ : ∀ n : ℕ, Matrix (Fin n) (Fin n) K → ℂ)
    (hΦ : PhiHyp R (m + 1) L₀ Λ₀ Q Φ) (D' : Kˣ) (hD' : (D' : K) ∈ Q ∨ -(D' : K) ∈ Q) {b₁ : ℕ}
    (hI : InvP R ψ ϖ Φ m (D' : K) b₁) :
    AmpHyp (mulR R ((ϖ⁻¹ ^ ((m + 1) * a) : Kˣ) : K)) (mulR R ((ϖ ^ b₁ : Kˣ) : K))
      (fun x : Fin m → K => bx R (mulR R ((ϖ ^ b₁ : Kˣ) : K)) (Pr (m + 1)) (GG R ψ Φ (D' : K) x)) := by
  have hϖ := hC.adic.mem
  have hmem : ∀ x : K, Bd R ϖ ((m + 1) * a) x → x ∈ mulR R ((ϖ⁻¹ ^ ((m + 1) * a) : Kˣ) : K) := by
    intro x hx
    obtain ⟨r, hr, e⟩ := bd_iff_sm_mul.1 hx
    exact fa_mem_mulR.2 ⟨r, hr, by rw [e]; simp⟩
  constructor
  · intro x hx k
    have : ∃ y, GG R ψ Φ (D' : K) x y ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hx
      show bx R _ (Pr (m + 1)) (GG R ψ Φ (D' : K) x) = 0
      rw [bx_congr _ hcon, bx_zero]
    obtain ⟨y, hy⟩ := this
    obtain ⟨h1, -, -⟩ := GG_supp hC Φ hΦ D' hD' x y hy
    obtain ⟨h2, h3, h4⟩ := h1 k
    refine ⟨hmem _ (Bd.mono hϖ ?_ (hC.L0 _ h2)), h3, hmem _ h4⟩
    nlinarith
  · intro x l hl
    refine bx_congr _ fun y => ?_
    have := (hI 1 R.one_mem x l y 0 (fun k => by
      obtain ⟨r, hr, e⟩ := fa_mem_mulR.1 (hl k)
      exact ⟨r, hr, by rw [e]; simp⟩) (fun p => ⟨0, R.zero_mem, by simp⟩)).1
    simpa using this

/- English proof (translation)
Establish `hA` using `hC.adic`. Establish `hzz : (z : K) * ((z⁻¹ : Kˣ) : K) = 1` using `by simp`. Establish `hprod : ∏ _k : Fin m, (z : K) = (z : K) ^ m` using `by simp`. Establish `hinvz : Ring.inverse (z : K) = ((z⁻¹ : Kˣ) : K)` using `ringInverse_eq hzz`. Establish `hx0 : x0 (D' : K) (fun _ : Fin m => (z : K)) = (z : K)`.

Unfold `x0`. Rewrite using `[hprod, ringInverse_eq (y := ((z⁻¹ : Kˣ) : K) ^ m) (by rw [← mul_pow, hzz, one_pow]), ← hz]`. Use `push_cast`. Establish `h : (z : K) ^ m * ((z⁻¹ : Kˣ) : K) ^ m = 1` using `by rw [← mul_pow, hzz, one_pow]`. Take the linear combination `(z : K) * h`.

Establish `hxt : xt (D' : K) (fun _ : Fin m => (z : K)) = fun _ => (z : K)`. Use function extensionality and compare the values at `i`. Use `Fin.cases ?_ (fun i' => ?_) i` and prove the remaining obligations. Simplify using `[xt, hx0]`. Simplify using `[xt]`.

Establish `hg1 : ∀ N : Pr (m + 1) → K, g1 (D' : K) (fun _ : Fin m => (z : K)) ((z : K) • N) = ∑ i : Fin m, N (sd i)`. Introduce `N`. Unfold `g1`. Rewrite using `[hx0, hxt, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Simplify using `only [hinvz, Pi.smul_apply, smul_eq_mul]`. Take the linear combination `((z : K) * ((z⁻¹ : Kˣ) : K) * N (sd i) + N (sd i)) * hzz`. Use `set f : Matrix (Fin (m + 1)) (Fin (m + 1)) K → ℂ := fun u => Φ (m + 1) (((z : K) • u).submatrix Fin.rev id) * ψ (sUp u) with hf`. Establish `hP : 0 < modK R (z : K)` using `modK_pos hA.isOpen hA.isCompact z`. Establish `key : ∀ N : Pr (m + 1) → K, f (1 + EE N) = ((modK R (z : K) ^ m : ℝ) : ℂ) * GG R ψ Φ (D' : K) (fun _ => (z : K)) ((z : K) • N)`.

Introduce `N`. Establish `hu : ∀ _k : Fin m, IsUnit (z : K)` using `fun _ => z.isUnit`. Simplify using `only [hf, GG, if_pos hu, hprod, fa_modK_pow hA, hxt, hg1, fa_sUp_EE, fa_smul_EE, ZZ]`. Establish `: ((modK R (z : K) ^ m : ℝ) : ℂ) ≠ 0`. Conclude with `(pow_pos hP m).ne'` after adjusting the coercions.

Use `push_cast`. Move the coercions through the operations in `at this`. Clear the denominators using the available nonvanishing facts. Use `set Λ' : AddSubgroup K := mulR R ((z⁻¹ * ϖ ^ b₁ : Kˣ) : K) with hΛ'`. Establish `hinv' : BInv Λ' (fun N : Pr (m + 1) → K => GG R ψ Φ (D' : K) (fun _ => (z : K)) ((z : K) • N))`.

Introduce `N l hl`. Use `show GG R ψ Φ (D' : K) (fun _ => (z : K)) ((z : K) • (N + l)) = _`. Rewrite using `[smul_add]`. Use `fa_inv_y hI _ _ _ fun p => ?_` and prove the remaining obligations. Take `⟨r, hr, e⟩` from `fa_mem_mulR.1 (hl p)`.

Use `fa_mem_mulR.2 ⟨r, hr, ?_⟩` and prove the remaining obligations. Simplify using `only [Pi.smul_apply, smul_eq_mul, e]`. Use `push_cast`. Take the linear combination `((ϖ : K) ^ b₁ * r) * hzz`. Establish `hsc` using `bx_scale hD z (fa_lat hA (ϖ ^ b₁)) (fa_lat hA (z⁻¹ * ϖ ^ b₁)) (GG R ψ Φ (D' : K) (fun _ => (z : K))) (fa_inv_y hI _) hinv'`.

Establish `hU` using `sumU hD (m + 1) f (by`. Introduce `u r hu hr hrI`. Simplify using `only [hf]`. Rewrite using `[← Matrix.smul_mul, fa_sub_mul, hΦ.1 _ 1 r (isLowUni_one K) (by`. Introduce `i j`.

Rewrite using `[Matrix.one_apply]`. Use `split_ifs`. Use `exacts [R.one_mem, R.zero_mem]) hr hrI,`. Use the proof step `(Formalism.DoubleCosetMeasures.P.simpleAdd K (m + 1) u r).2 hu hr, AddChar.map_add_eq_mul,`. Use `psi_R hD (Formalism.DoubleCosetMeasures.P.sUp_mem R _ hrI), mul_one]) (by`.

Use `(fin_single hD (m + 1) (ϖ ^ a * z)).subset ?_` and prove the remaining obligations. Introduce `q hq`. Establish `h1 : Φ (m + 1) (((z : K) • sec_m (Quotient.out q)).submatrix Fin.rev id) ≠ 0` using `left_ne_zero_of_mul hq`. Introduce `i j`. Establish `h2` using `hC.L0 _ (hΦ.2.1 _ h1 (Fin.rev i) j)`.

Simplify using `only [Matrix.submatrix_apply, Fin.rev_rev, id, Matrix.smul_apply, smul_eq_mul] at h2`. Use `show ((ϖ ^ a * z : Kˣ) : K) • sec_m (Quotient.out q) i j ∈ R`. Establish `h3 : ((ϖ ^ a * z : Kˣ) : K) • sec_m (Quotient.out q) i j = (ϖ : K) ^ a * ((z : K) * sec_m (Quotient.out q) i j)` using `by push_cast; rw [smul_eq_mul, mul_assoc]`. Rewrite using `[h3]; exact h2) (fa_lat hA (z⁻¹ * ϖ ^ b₁)) (by`. Introduce `N l hl`.

Use `show f (1 + EE (N + l)) = f (1 + EE N)`. Rewrite using `[key, key]`. Conclude with `congrArg _ (hinv' N l hl))`. Rewrite using `[omPhi_single, hU, bx_congr _ key, bx_mul_left, ← hsc, fa_card_Pr]`. Establish `hcard : (m + 1) * (m + 1 - 1) / 2 = m * (m - 1) / 2 + m`.

Take `⟨k, rfl⟩ : ∃ k, m = k + 1` from `⟨m - 1, by omega⟩`. Establish `e : (k + 1 + 1) * (k + 1 + 1 - 1) = (k + 1) * (k + 1 - 1) + 2 * (k + 1)`. Simplify using `only [Nat.add_sub_cancel]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, Nat.add_mul_div_left _ _ (by norm_num)]`.

Rewrite using `[hcard, pow_add]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fa_crit (hD : LocalDatum K R ψ) (hC : Cst R ϖ L₀ Λ₀ Q a b) {m : ℕ} (hm : 1 ≤ m)
    (Φ : ∀ n : ℕ, Matrix (Fin n) (Fin n) K → ℂ)
    (hΦ : PhiHyp R (m + 1) L₀ Λ₀ Q Φ) (D' z : Kˣ) (hz : z ^ (m + 1) = D') {b₁ : ℕ}
    (hI : InvP R ψ ϖ Φ m (D' : K) b₁) :
    bx R (mulR R ((ϖ ^ b₁ : Kˣ) : K)) (Pr (m + 1)) (GG R ψ Φ (D' : K) (fun _ => (z : K))) =
      ((modK R (z : K) ^ (m * (m - 1) / 2) : ℝ) : ℂ) * omPhi R ψ (addBlock h0 (m + 1) z) Φ := by
  have hA := hC.adic
  have hzz : (z : K) * ((z⁻¹ : Kˣ) : K) = 1 := by simp
  have hprod : ∏ _k : Fin m, (z : K) = (z : K) ^ m := by simp
  have hinvz : Ring.inverse (z : K) = ((z⁻¹ : Kˣ) : K) := ringInverse_eq hzz
  have hx0 : x0 (D' : K) (fun _ : Fin m => (z : K)) = (z : K) := by
    unfold x0
    rw [hprod, ringInverse_eq (y := ((z⁻¹ : Kˣ) : K) ^ m) (by rw [← mul_pow, hzz, one_pow]), ← hz]
    push_cast
    have h : (z : K) ^ m * ((z⁻¹ : Kˣ) : K) ^ m = 1 := by rw [← mul_pow, hzz, one_pow]
    linear_combination (z : K) * h
  have hxt : xt (D' : K) (fun _ : Fin m => (z : K)) = fun _ => (z : K) := by
    funext i
    refine Fin.cases ?_ (fun i' => ?_) i
    · simp [xt, hx0]
    · simp [xt]
  have hg1 : ∀ N : Pr (m + 1) → K, g1 (D' : K) (fun _ : Fin m => (z : K)) ((z : K) • N) =
      ∑ i : Fin m, N (sd i) := by
    intro N
    unfold g1
    rw [hx0, hxt, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hinvz, Pi.smul_apply, smul_eq_mul]
    linear_combination ((z : K) * ((z⁻¹ : Kˣ) : K) * N (sd i) + N (sd i)) * hzz
  set f : Matrix (Fin (m + 1)) (Fin (m + 1)) K → ℂ := fun u =>
    Φ (m + 1) (((z : K) • u).submatrix Fin.rev id) * ψ (sUp u) with hf
  have hP : 0 < modK R (z : K) := modK_pos hA.isOpen hA.isCompact z
  have key : ∀ N : Pr (m + 1) → K, f (1 + EE N) =
      ((modK R (z : K) ^ m : ℝ) : ℂ) * GG R ψ Φ (D' : K) (fun _ => (z : K)) ((z : K) • N) := by
    intro N
    have hu : ∀ _k : Fin m, IsUnit (z : K) := fun _ => z.isUnit
    simp only [hf, GG, if_pos hu, hprod, fa_modK_pow hA, hxt, hg1, fa_sUp_EE, fa_smul_EE, ZZ]
    have : ((modK R (z : K) ^ m : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (pow_pos hP m).ne'
    push_cast
    push_cast at this
    field_simp
  set Λ' : AddSubgroup K := mulR R ((z⁻¹ * ϖ ^ b₁ : Kˣ) : K) with hΛ'
  have hinv' : BInv Λ' (fun N : Pr (m + 1) → K =>
      GG R ψ Φ (D' : K) (fun _ => (z : K)) ((z : K) • N)) := by
    intro N l hl
    show GG R ψ Φ (D' : K) (fun _ => (z : K)) ((z : K) • (N + l)) = _
    rw [smul_add]
    refine fa_inv_y hI _ _ _ fun p => ?_
    obtain ⟨r, hr, e⟩ := fa_mem_mulR.1 (hl p)
    refine fa_mem_mulR.2 ⟨r, hr, ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, e]
    push_cast
    linear_combination ((ϖ : K) ^ b₁ * r) * hzz
  have hsc := bx_scale hD z (fa_lat hA (ϖ ^ b₁)) (fa_lat hA (z⁻¹ * ϖ ^ b₁))
    (GG R ψ Φ (D' : K) (fun _ => (z : K))) (fa_inv_y hI _) hinv'
  have hU := sumU hD (m + 1) f (by
      intro u r hu hr hrI
      simp only [hf]
      rw [← Matrix.smul_mul, fa_sub_mul, hΦ.1 _ 1 r (isLowUni_one K) (by
        intro i j; rw [Matrix.one_apply]; split_ifs; exacts [R.one_mem, R.zero_mem]) hr hrI,
        (Formalism.DoubleCosetMeasures.P.simpleAdd K (m + 1) u r).2 hu hr, AddChar.map_add_eq_mul,
        psi_R hD (Formalism.DoubleCosetMeasures.P.sUp_mem R _ hrI), mul_one]) (by
      refine (fin_single hD (m + 1) (ϖ ^ a * z)).subset ?_
      intro q hq
      have h1 : Φ (m + 1) (((z : K) • sec_m (Quotient.out q)).submatrix Fin.rev id) ≠ 0 :=
        left_ne_zero_of_mul hq
      intro i j
      have h2 := hC.L0 _ (hΦ.2.1 _ h1 (Fin.rev i) j)
      simp only [Matrix.submatrix_apply, Fin.rev_rev, id, Matrix.smul_apply, smul_eq_mul] at h2
      show ((ϖ ^ a * z : Kˣ) : K) • sec_m (Quotient.out q) i j ∈ R
      have h3 : ((ϖ ^ a * z : Kˣ) : K) • sec_m (Quotient.out q) i j =
          (ϖ : K) ^ a * ((z : K) * sec_m (Quotient.out q) i j) := by
        push_cast; rw [smul_eq_mul, mul_assoc]
      rw [h3]; exact h2) (fa_lat hA (z⁻¹ * ϖ ^ b₁)) (by
      intro N l hl
      show f (1 + EE (N + l)) = f (1 + EE N)
      rw [key, key]
      exact congrArg _ (hinv' N l hl))
  rw [omPhi_single, hU, bx_congr _ key, bx_mul_left, ← hsc, fa_card_Pr]
  have hcard : (m + 1) * (m + 1 - 1) / 2 = m * (m - 1) / 2 + m := by
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have e : (k + 1 + 1) * (k + 1 + 1 - 1) = (k + 1) * (k + 1 - 1) + 2 * (k + 1) := by
      simp only [Nat.add_sub_cancel]; ring
    rw [e, Nat.add_mul_div_left _ _ (by norm_num)]
  rw [hcard, pow_add]
  push_cast
  ring

end FA1

section FA2

variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ} {ϖ : Kˣ} {L₀ Λ₀ : AddSubgroup K} {Q : Set K} {a b : ℕ}

/- English proof (translation)
Use function extensionality and compare the values at `p`. Simplify using `only [ys, Pi.add_apply]`. Apply the tactic sequence `rcases ee (Sum.inr p) with q | j <;> simp`.
-/
theorem fa_ys_add {m : ℕ} (n n' : Pr (m + 1) → K) (τ τ' : Fin m → K) :
    ys (n + n') (τ + τ') = ys n τ + ys n' τ' := by
  funext p
  simp only [ys, Pi.add_apply]
  rcases ee (Sum.inr p) with q | j <;> simp

/- English proof (translation)
Simplify using `only [ys]`. Break down `ee (Sum.inr p) with q | j` into its components or cases. Conclude with `hn q`. Conclude with `hτ j`.
-/
theorem fa_ys_mem {m : ℕ} (Λ : AddSubgroup K) (n : Pr (m + 1) → K) (τ : Fin m → K)
    (hn : ∀ p, n p ∈ Λ) (hτ : ∀ j, τ j ∈ Λ) (p : Pr (m + 1)) : ys n τ p ∈ Λ := by
  simp only [ys]
  rcases ee (Sum.inr p) with q | j
  · exact hn q
  · exact hτ j

/- English proof (translation)
Establish `hA` using `hC.adic`. Establish `htt : (t : K) * ((t⁻¹ : Kˣ) : K) = 1` using `by simp`. Use `set Λ₁ : AddSubgroup K := mulR R ((ϖ ^ b₁ : Kˣ) : K) with hΛ₁`. Use `set Λt : AddSubgroup K := mulR R ((t * ϖ ^ b₁ : Kˣ) : K) with hΛt`. Establish `hlat1 : IsLat Λ₁` using `fa_lat hA _`.

Establish `hlatt : IsLat Λt` using `fa_lat hA _`. Establish `hmemt : ∀ x : K, x ∈ Λt → ∃ r ∈ R, x = (t : K) * (ϖ : K) ^ b₁ * r`. Introduce `x hx`. Take `⟨r, hr, e⟩` from `fa_mem_mulR.1 hx`. Conclude with `⟨r, hr, by rw [e]; push_cast; ring⟩`.

Establish `hsmul : ∀ x : K, x ∈ Λ₁ → (t : K) * x ∈ Λt`. Introduce `x hx`. Take `⟨r, hr, e⟩` from `fa_mem_mulR.1 hx`. Conclude with `fa_mem_mulR.2 ⟨r, hr, by rw [e]; push_cast; ring⟩`. Use `set J : (Fin m → K) → (Pr (m + 1) → K) → ℂ := fun x y => GG R ψ Φ (D' : K) x y * ψ (g0 (D' : K) x * ((t⁻¹ : Kˣ) : K)) with hJdef`.

Establish `hJ : ∀ (x l : Fin m → K) (y l' : Pr (m + 1) → K), (∀ k, l k ∈ Λt) → (∀ p, l' p ∈ Λt) → J (x + l) (y + l') = J x y`. Introduce `x l y l' hl hl'`. Take `⟨h1, h2⟩` from `hI t htR x l y l' (fun k => hmemt _ (hl k)) (fun p => hmemt _ (hl' p))`. Simplify using `only [hJdef]`. Distinguish the cases in `h0 : GG R ψ Φ (D' : K) x y = 0`.

Rewrite using `[h1, h0]`. Simplify using the standard rewrite rules. Take `⟨r, hr, e⟩` from `h2 h0`. Rewrite using `[h1]`. Use `congr 1`.

Establish `: g0 (D' : K) (x + l) * ((t⁻¹ : Kˣ) : K) = g0 (D' : K) x * ((t⁻¹ : Kˣ) : K) + r`. Take the linear combination `((t⁻¹ : Kˣ) : K) * e + r * htt`. Rewrite using `[this, AddChar.map_add_eq_mul, psi_R hD hr, mul_one]`. Establish `hJ1 : ∀ (x : Fin m → K) (y l' : Pr (m + 1) → K), (∀ p, l' p ∈ Λ₁) → J x (y + l') = J x y`. Introduce `x y l' hl'`.

Simplify using `only [hJdef]`. Rewrite using `[fa_inv_y hI x y l' hl']`. Use `set k : Matrix (Fin (m + 1)) (Fin (m + 1)) K → ℂ := fun u => ∑ᶠ ξ : Fin m → KR R, Φ (m + 1) ((Hm (t : K) (c : K) (outV R ξ) u).submatrix Fin.rev id) * ψ (lastE (outV R ξ) + sUp u) with hk`. Use `set f : (Pr (m + 1) → K) → ℂ := fun n => bx R Λt (Fin m) (fun τ => J (xs n) (ys n τ)) with hf`. Establish `hkf : ∀ N : Pr (m + 1) → K, k (1 + EE N) = f ((t : K) • N)`.

Introduce `N`. Simplify using `only [hk, hf]`. Rewrite using `[hLA N, ← bx_mul_left]`. Rewrite using `[bx_indep hD hlatt hlat1 (fun τ => J (xs ((t : K) • N)) (ys ((t : K) • N) τ)) (by`. Introduce `τ l hl`.

Establish `e : ys ((t : K) • N) (τ + l) = ys ((t : K) • N) τ + ys 0 l`. Rewrite using `[← fa_ys_add, add_zero]`. Use `show J _ (ys ((t : K) • N) (τ + l)) = _`. Rewrite using `[e]`. Use `hJ (xs ((t : K) • N)) 0 (ys ((t : K) • N) τ) (ys 0 l) (fun _ => Λt.zero_mem) (fa_ys_mem Λt 0 l (fun _ => Λt.zero_mem) hl)` as an intermediate fact.

Simplify using `using this)`. Use the proof step `(by`. Introduce `τ l hl`. Establish `e : ys ((t : K) • N) (τ + l) = ys ((t : K) • N) τ + ys 0 l`. Rewrite using `[← fa_ys_add, add_zero]`.

Use `show J _ (ys ((t : K) • N) (τ + l)) = _`. Rewrite using `[e]`. Conclude with `hJ1 _ _ _ (fa_ys_mem Λ₁ 0 l (fun _ => Λ₁.zero_mem) hl))]`. Conclude with `bx_congr _ fun τ => by simp only [hJdef]; ring`. Establish `hfinv : BInv Λt f`.

Introduce `n l hl`. Simplify using `only [hf]`. Use `bx_congr _ fun τ => ?_` and prove the remaining obligations. Establish `e : ys (n + l) τ = ys n τ + ys l 0` using `by rw [← fa_ys_add, add_zero]`. Rewrite using `[e]`.

Conclude with `hJ (xs n) (xs l) _ _ (fun i => hl _) (fa_ys_mem Λt l 0 hl (fun _ => Λt.zero_mem))`. Establish `hfinv' : BInv Λ₁ (fun N : Pr (m + 1) → K => f ((t : K) • N))`. Introduce `N l hl`. Use `show f ((t : K) • (N + l)) = f ((t : K) • N)`. Rewrite using `[smul_add]`.

Conclude with `hfinv _ _ fun p => hsmul _ (hl p)`. Establish `hU` using `sumU hD (m + 1) k (by`. Introduce `u r hu hr hrI`. Simplify using `only [hk]`. Use `finsum_congr fun ξ => ?_` and prove the remaining obligations.

Rewrite using `[fa_Hm_mul _ _ _ _ _ hr, fa_sub_mul, hΦ.1 _ 1 r (isLowUni_one K) (by`. Introduce `i j`. Rewrite using `[Matrix.one_apply]`. Use `split_ifs`. Use `exacts [R.one_mem, R.zero_mem]) hr hrI,`.

Use the proof step `(Formalism.DoubleCosetMeasures.P.simpleAdd K (m + 1) u r).2 hu hr, ← add_assoc, AddChar.map_add_eq_mul _ _ (sUp r),`. Use `psi_R hD (Formalism.DoubleCosetMeasures.P.sUp_mem R _ hrI), mul_one]) (by`. Use `(fin_single hD (m + 1) (ϖ ^ a * t)).subset ?_` and prove the remaining obligations. Introduce `q hq`. Establish `hq' : k (sec_m (Quotient.out q)) ≠ 0` using `hq`.

Establish `hu : IsUpUni (sec_m (Quotient.out q))` using `(Quotient.out q).2`. Choose the witnesses or unpack the hypotheses as in `⟨ξ, hξ⟩ : ∃ ξ : Fin m → KR R, Φ (m + 1) ((Hm (t : K) (c : K) (outV R ξ) (sec_m (Quotient.out q))).submatrix Fin.rev id) * ψ (lastE (outV R ξ) + sUp (sec_m (Quotient.out q))) ≠ 0 := by`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Conclude with `hq' (finsum_eq_zero_of_forall_eq_zero hcon)`.

Establish `h1` using `hΦ.2.1 _ (left_ne_zero_of_mul hξ)`. Introduce `i j`. Establish `h3 : ((ϖ ^ a * t : Kˣ) : K) • sec_m (Quotient.out q) i j = (ϖ : K) ^ a * ((t : K) * sec_m (Quotient.out q) i j)` using `by push_cast; rw [smul_eq_mul, mul_assoc]`. Use `show ((ϖ ^ a * t : Kˣ) : K) • sec_m (Quotient.out q) i j ∈ R`. Rewrite using `[h3]`.

Use `Fin.lastCases ?_ (fun i' => ?_) i` and prove the remaining obligations. Establish `: sec_m (Quotient.out q) (Fin.last m) j ∈ R`. Distinguish the cases in `hj : j = Fin.last m`. Rewrite using `[hj, hu.2]`. Conclude with `R.one_mem`.

Establish `h0 : sec_m (Quotient.out q) (Fin.last m) j = 0` using `hu.1 (lt_of_le_of_ne (Fin.le_last j) hj)`. Conclude with `Eq.mpr (congrArg (fun x => x ∈ R) h0) R.zero_mem`. Conclude with `R.mul_mem (R.pow_mem hA.mem a) (R.mul_mem htR this)`. Establish `h2` using `hC.L0 _ (h1 (Fin.rev i'.succ) j)`. Simplify `h2) hlat1 (by` using `[Hm, Bd]`.

Introduce `N l hl`. Use `show k (1 + EE (N + l)) = k (1 + EE N)`. Rewrite using `[hkf, hkf]`. Conclude with `hfinv' N l hl)`. Establish `hsc` using `bx_scale hD t hlatt hlat1 f hfinv hfinv'`.

Use `set Jh : (Fin m ⊕ Pr (m + 1) → K) → ℂ := fun v => J (fun i => v (Sum.inl i)) (fun p => v (Sum.inr p)) with hJh`. Establish `hsJh : BSupp L₀ Jh`. Introduce `v hv`. Establish `h0 : GG R ψ Φ (D' : K) (fun i => v (Sum.inl i)) (fun p => v (Sum.inr p)) ≠ 0` using `left_ne_zero_of_mul hv`. Take `⟨h1, h2, -⟩` from `GG_supp hC Φ hΦ D' hD'Q _ _ h0`.

Introduce and unpack `(i | p)`. Conclude with `(h1 i).1`. Conclude with `h2 p`. Establish `h7` using `bx_sum hD (ι := Pr (m + 1)) (κ := Fin m) hlatt hL₀ (fun w => Jh (fun k => w (ee k))) (by`. Introduce `w hw j`.

Take `⟨k, rfl⟩` from `fa_ee_bij.2 j`. Conclude with `hsJh (fun k => w (ee k)) hw k)`. Establish `h8` using `bx_equiv (R := R) (Equiv.ofBijective ee (fa_ee_bij (m := m))).symm Λt Jh`. Establish `h9` using `bx_sum hD (ι := Fin m) (κ := Pr (m + 1)) hlatt hL₀ Jh hsJh`. Establish `e7 : bx R Λt (Pr (m + 1)) f = bx R Λt (Fin m ⊕ Pr (m + 1)) Jh`.

Rewrite using `[h8]`. Conclude with `h7.symm`. Establish `hF : ∀ x : Fin m → K, bx R Λ₁ (Pr (m + 1)) (GG R ψ Φ (D' : K) x) * ψ (g0 (D' : K) x * ((t⁻¹ : Kˣ) : K)) = bx R Λt (Pr (m + 1)) (J x)`. Introduce `x`. Rewrite using `[bx_indep hD hlatt hlat1 (J x) (by`.

Introduce `y l' hl'`. Use `hJ x 0 y l' (fun _ => Λt.zero_mem) hl'` as an intermediate fact. Simplify using `using this) (fun y l' hl' => hJ1 x y l' hl'), mul_comm, ← bx_mul_left]`. Conclude with `bx_congr _ fun y => by simp only [hJdef]; ring`. Establish `e9 : bx R Λt (Fin m ⊕ Pr (m + 1)) Jh = bx R Λt (Fin m) (fun x => bx R Λt (Pr (m + 1)) (J x))` using `h9`.

Establish `e10 : bx R Λt (Fin m) (fun x => bx R Λt (Pr (m + 1)) (J x)) = intK R Λ m (fun x : Fin m → K => bx R Λ₁ (Pr (m + 1)) (GG R ψ Φ (D' : K) x) * ψ (g0 (D' : K) x * ((t⁻¹ : Kˣ) : K)))`. Rewrite using `[intK_eq_bx, bx_congr _ hF]`. Use `bx_indep hD hlatt hΛ _ ?_ ?_` and prove the remaining obligations. Introduce `x l hl`. Use `bx_congr _ fun y => ?_` and prove the remaining obligations.

Use `hJ x l y 0 hl (fun _ => Λt.zero_mem)` as an intermediate fact. Simplify using `using this`. Introduce `x l hl`. Use `hΛinv x l hl` as an intermediate fact. Simplify using `only [hF] at this`.

Conclude with `this`. Establish `hP : 0 < modK R (t : K)` using `modK_pos hA.isOpen hA.isCompact t`. Establish `hom` using `orbital_integral_two_blocks (ψ := ψ) hD m t c Φ (ϖ ^ a) hΦ.1 (by`. Introduce `Z hZ i j`. Use `hC.L0 _ (hΦ.2.1 Z hZ i j)` as an intermediate fact.

Simplify `this)` using `[Bd]`. Rewrite using `[hom]`. Establish `e1 : (∑ᶠ q : upUniG K (m + 1) ⧸ intSub R (upUniG K (m + 1)), ∑ᶠ ξ : Fin m → KR R, Φ (m + 1) ((Hm (t : K) (c : K) (outV R ξ) (sec_m (Quotient.out q))).submatrix Fin.rev id) * ψ (lastE (outV R ξ) + sUp (sec_m (Quotient.out q)))) = bx R Λ₁ (Pr (m + 1)) (fun N => f ((t : K) • N))`. Rewrite using `[← bx_congr _ hkf]`. Conclude with `hU`.

Rewrite using `[e1, ← e10, ← e9, ← e7, ← hsc, fa_card_Pr]`. Establish `hcard : (m + 1) * (m + 1 - 1) / 2 = m * (m + 1) / 2`. Rewrite using `[Nat.add_sub_cancel, mul_comm]`. Rewrite using `[hcard]`. Establish `hne : ((modK R (t : K) : ℝ) : ℂ) ^ (m * (m + 1) / 2) ≠ 0`.

Conclude with `(pow_pos hP _).ne'` after adjusting the coercions. Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
theorem fa_main (hD : LocalDatum K R ψ) (hC : Cst R ϖ L₀ Λ₀ Q a b) (hL₀ : IsLat L₀) {m : ℕ}
    (Φ : ∀ n : ℕ, Matrix (Fin n) (Fin n) K → ℂ)
    (hΦ : PhiHyp R (m + 1) L₀ Λ₀ Q Φ) (t c D' : Kˣ) (hD'Q : (D' : K) ∈ Q ∨ -(D' : K) ∈ Q) {b₁ : ℕ}
    (hI : InvP R ψ ϖ Φ m (D' : K) b₁) (htR : (t : K) ∈ R)
    (hLA : ∀ N : Pr (m + 1) → K,
      ∑ᶠ ξ : Fin m → KR R,
        Φ (m + 1) ((Hm (t : K) (c : K) (outV R ξ) (1 + EE N)).submatrix Fin.rev id) *
          ψ (lastE (outV R ξ) + sUp (1 + EE N)) =
      ψ (g0 (D' : K) (xs ((t : K) • N)) * ((t⁻¹ : Kˣ) : K)) *
        bx R (mulR R ((ϖ ^ b₁ : Kˣ) : K)) (Fin m)
          (fun τ => GG R ψ Φ (D' : K) (xs ((t : K) • N)) (ys ((t : K) • N) τ)))
    (Λ : AddSubgroup K) (hΛ : IsLat Λ)
    (hΛinv : LatInvN Λ (fun x : Fin m → K =>
      bx R (mulR R ((ϖ ^ b₁ : Kˣ) : K)) (Pr (m + 1)) (GG R ψ Φ (D' : K) x) *
        ψ (g0 (D' : K) x * ((t⁻¹ : Kˣ) : K)))) :
    omPhi R ψ (pt2 h0 m t c) Φ = ((((modK R (t : K)) ^ (m * (m + 1) / 2))⁻¹ : ℝ) : ℂ) *
      intK R Λ m (fun x : Fin m → K =>
        bx R (mulR R ((ϖ ^ b₁ : Kˣ) : K)) (Pr (m + 1)) (GG R ψ Φ (D' : K) x) *
          ψ (g0 (D' : K) x * ((t⁻¹ : Kˣ) : K))) := by
  have hA := hC.adic
  have htt : (t : K) * ((t⁻¹ : Kˣ) : K) = 1 := by simp
  set Λ₁ : AddSubgroup K := mulR R ((ϖ ^ b₁ : Kˣ) : K) with hΛ₁
  set Λt : AddSubgroup K := mulR R ((t * ϖ ^ b₁ : Kˣ) : K) with hΛt
  have hlat1 : IsLat Λ₁ := fa_lat hA _
  have hlatt : IsLat Λt := fa_lat hA _
  have hmemt : ∀ x : K, x ∈ Λt → ∃ r ∈ R, x = (t : K) * (ϖ : K) ^ b₁ * r := by
    intro x hx
    obtain ⟨r, hr, e⟩ := fa_mem_mulR.1 hx
    exact ⟨r, hr, by rw [e]; push_cast; ring⟩
  have hsmul : ∀ x : K, x ∈ Λ₁ → (t : K) * x ∈ Λt := by
    intro x hx
    obtain ⟨r, hr, e⟩ := fa_mem_mulR.1 hx
    exact fa_mem_mulR.2 ⟨r, hr, by rw [e]; push_cast; ring⟩
  set J : (Fin m → K) → (Pr (m + 1) → K) → ℂ := fun x y =>
    GG R ψ Φ (D' : K) x y * ψ (g0 (D' : K) x * ((t⁻¹ : Kˣ) : K)) with hJdef
  have hJ : ∀ (x l : Fin m → K) (y l' : Pr (m + 1) → K), (∀ k, l k ∈ Λt) → (∀ p, l' p ∈ Λt) →
      J (x + l) (y + l') = J x y := by
    intro x l y l' hl hl'
    obtain ⟨h1, h2⟩ := hI t htR x l y l' (fun k => hmemt _ (hl k)) (fun p => hmemt _ (hl' p))
    simp only [hJdef]
    by_cases h0 : GG R ψ Φ (D' : K) x y = 0
    · rw [h1, h0]; simp
    · obtain ⟨r, hr, e⟩ := h2 h0
      rw [h1]
      congr 1
      have : g0 (D' : K) (x + l) * ((t⁻¹ : Kˣ) : K) = g0 (D' : K) x * ((t⁻¹ : Kˣ) : K) + r := by
        linear_combination ((t⁻¹ : Kˣ) : K) * e + r * htt
      rw [this, AddChar.map_add_eq_mul, psi_R hD hr, mul_one]
  have hJ1 : ∀ (x : Fin m → K) (y l' : Pr (m + 1) → K), (∀ p, l' p ∈ Λ₁) → J x (y + l') = J x y := by
    intro x y l' hl'
    simp only [hJdef]
    rw [fa_inv_y hI x y l' hl']
  set k : Matrix (Fin (m + 1)) (Fin (m + 1)) K → ℂ := fun u =>
    ∑ᶠ ξ : Fin m → KR R, Φ (m + 1) ((Hm (t : K) (c : K) (outV R ξ) u).submatrix Fin.rev id) *
      ψ (lastE (outV R ξ) + sUp u) with hk
  set f : (Pr (m + 1) → K) → ℂ := fun n => bx R Λt (Fin m) (fun τ => J (xs n) (ys n τ)) with hf
  have hkf : ∀ N : Pr (m + 1) → K, k (1 + EE N) = f ((t : K) • N) := by
    intro N
    simp only [hk, hf]
    rw [hLA N, ← bx_mul_left]
    rw [bx_indep hD hlatt hlat1 (fun τ => J (xs ((t : K) • N)) (ys ((t : K) • N) τ))
      (by
        intro τ l hl
        have e : ys ((t : K) • N) (τ + l) = ys ((t : K) • N) τ + ys 0 l := by
          rw [← fa_ys_add, add_zero]
        show J _ (ys ((t : K) • N) (τ + l)) = _
        rw [e]
        have := hJ (xs ((t : K) • N)) 0 (ys ((t : K) • N) τ) (ys 0 l) (fun _ => Λt.zero_mem)
          (fa_ys_mem Λt 0 l (fun _ => Λt.zero_mem) hl)
        simpa using this)
      (by
        intro τ l hl
        have e : ys ((t : K) • N) (τ + l) = ys ((t : K) • N) τ + ys 0 l := by
          rw [← fa_ys_add, add_zero]
        show J _ (ys ((t : K) • N) (τ + l)) = _
        rw [e]
        exact hJ1 _ _ _ (fa_ys_mem Λ₁ 0 l (fun _ => Λ₁.zero_mem) hl))]
    exact bx_congr _ fun τ => by simp only [hJdef]; ring
  have hfinv : BInv Λt f := by
    intro n l hl
    simp only [hf]
    refine bx_congr _ fun τ => ?_
    have e : ys (n + l) τ = ys n τ + ys l 0 := by rw [← fa_ys_add, add_zero]
    rw [e]
    exact hJ (xs n) (xs l) _ _ (fun i => hl _) (fa_ys_mem Λt l 0 hl (fun _ => Λt.zero_mem))
  have hfinv' : BInv Λ₁ (fun N : Pr (m + 1) → K => f ((t : K) • N)) := by
    intro N l hl
    show f ((t : K) • (N + l)) = f ((t : K) • N)
    rw [smul_add]
    exact hfinv _ _ fun p => hsmul _ (hl p)
  have hU := sumU hD (m + 1) k (by
      intro u r hu hr hrI
      simp only [hk]
      refine finsum_congr fun ξ => ?_
      rw [fa_Hm_mul _ _ _ _ _ hr, fa_sub_mul, hΦ.1 _ 1 r (isLowUni_one K) (by
        intro i j; rw [Matrix.one_apply]; split_ifs; exacts [R.one_mem, R.zero_mem]) hr hrI,
        (Formalism.DoubleCosetMeasures.P.simpleAdd K (m + 1) u r).2 hu hr, ← add_assoc, AddChar.map_add_eq_mul _ _ (sUp r),
        psi_R hD (Formalism.DoubleCosetMeasures.P.sUp_mem R _ hrI), mul_one]) (by
      refine (fin_single hD (m + 1) (ϖ ^ a * t)).subset ?_
      intro q hq
      have hq' : k (sec_m (Quotient.out q)) ≠ 0 := hq
      have hu : IsUpUni (sec_m (Quotient.out q)) := (Quotient.out q).2
      obtain ⟨ξ, hξ⟩ : ∃ ξ : Fin m → KR R, Φ (m + 1) ((Hm (t : K) (c : K) (outV R ξ)
          (sec_m (Quotient.out q))).submatrix Fin.rev id) *
          ψ (lastE (outV R ξ) + sUp (sec_m (Quotient.out q))) ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hq' (finsum_eq_zero_of_forall_eq_zero hcon)
      have h1 := hΦ.2.1 _ (left_ne_zero_of_mul hξ)
      intro i j
      have h3 : ((ϖ ^ a * t : Kˣ) : K) • sec_m (Quotient.out q) i j =
          (ϖ : K) ^ a * ((t : K) * sec_m (Quotient.out q) i j) := by
        push_cast; rw [smul_eq_mul, mul_assoc]
      show ((ϖ ^ a * t : Kˣ) : K) • sec_m (Quotient.out q) i j ∈ R
      rw [h3]
      refine Fin.lastCases ?_ (fun i' => ?_) i
      · have : sec_m (Quotient.out q) (Fin.last m) j ∈ R := by
          by_cases hj : j = Fin.last m
          · rw [hj, hu.2]; exact R.one_mem
          · have h0 : sec_m (Quotient.out q) (Fin.last m) j = 0 :=
              hu.1 (lt_of_le_of_ne (Fin.le_last j) hj)
            exact Eq.mpr (congrArg (fun x => x ∈ R) h0) R.zero_mem
        exact R.mul_mem (R.pow_mem hA.mem a) (R.mul_mem htR this)
      · have h2 := hC.L0 _ (h1 (Fin.rev i'.succ) j)
        simpa [Hm, Bd] using h2) hlat1 (by
      intro N l hl
      show k (1 + EE (N + l)) = k (1 + EE N)
      rw [hkf, hkf]
      exact hfinv' N l hl)
  have hsc := bx_scale hD t hlatt hlat1 f hfinv hfinv'

  set Jh : (Fin m ⊕ Pr (m + 1) → K) → ℂ := fun v => J (fun i => v (Sum.inl i)) (fun p => v (Sum.inr p))
    with hJh
  have hsJh : BSupp L₀ Jh := by
    intro v hv
    have h0 : GG R ψ Φ (D' : K) (fun i => v (Sum.inl i)) (fun p => v (Sum.inr p)) ≠ 0 :=
      left_ne_zero_of_mul hv
    obtain ⟨h1, h2, -⟩ := GG_supp hC Φ hΦ D' hD'Q _ _ h0
    rintro (i | p)
    · exact (h1 i).1
    · exact h2 p
  have h7 := bx_sum hD (ι := Pr (m + 1)) (κ := Fin m) hlatt hL₀ (fun w => Jh (fun k => w (ee k))) (by
    intro w hw j
    obtain ⟨k, rfl⟩ := fa_ee_bij.2 j
    exact hsJh (fun k => w (ee k)) hw k)
  have h8 := bx_equiv (R := R) (Equiv.ofBijective ee (fa_ee_bij (m := m))).symm Λt Jh
  have h9 := bx_sum hD (ι := Fin m) (κ := Pr (m + 1)) hlatt hL₀ Jh hsJh
  have e7 : bx R Λt (Pr (m + 1)) f = bx R Λt (Fin m ⊕ Pr (m + 1)) Jh := by
    rw [h8]
    exact h7.symm
  have hF : ∀ x : Fin m → K, bx R Λ₁ (Pr (m + 1)) (GG R ψ Φ (D' : K) x) *
      ψ (g0 (D' : K) x * ((t⁻¹ : Kˣ) : K)) = bx R Λt (Pr (m + 1)) (J x) := by
    intro x
    rw [bx_indep hD hlatt hlat1 (J x) (by
        intro y l' hl'
        have := hJ x 0 y l' (fun _ => Λt.zero_mem) hl'
        simpa using this) (fun y l' hl' => hJ1 x y l' hl'), mul_comm, ← bx_mul_left]
    exact bx_congr _ fun y => by simp only [hJdef]; ring
  have e9 : bx R Λt (Fin m ⊕ Pr (m + 1)) Jh = bx R Λt (Fin m) (fun x => bx R Λt (Pr (m + 1)) (J x)) :=
    h9
  have e10 : bx R Λt (Fin m) (fun x => bx R Λt (Pr (m + 1)) (J x)) =
      intK R Λ m (fun x : Fin m → K => bx R Λ₁ (Pr (m + 1)) (GG R ψ Φ (D' : K) x) *
        ψ (g0 (D' : K) x * ((t⁻¹ : Kˣ) : K))) := by
    rw [intK_eq_bx, bx_congr _ hF]
    refine bx_indep hD hlatt hΛ _ ?_ ?_
    · intro x l hl
      refine bx_congr _ fun y => ?_
      have := hJ x l y 0 hl (fun _ => Λt.zero_mem)
      simpa using this
    · intro x l hl
      have := hΛinv x l hl
      simp only [hF] at this
      exact this
  have hP : 0 < modK R (t : K) := modK_pos hA.isOpen hA.isCompact t
  have hom := orbital_integral_two_blocks (ψ := ψ) hD m t c Φ (ϖ ^ a) hΦ.1 (by
    intro Z hZ i j
    have := hC.L0 _ (hΦ.2.1 Z hZ i j)
    simpa [Bd] using this)
  rw [hom]
  have e1 : (∑ᶠ q : upUniG K (m + 1) ⧸ intSub R (upUniG K (m + 1)), ∑ᶠ ξ : Fin m → KR R,
        Φ (m + 1) ((Hm (t : K) (c : K) (outV R ξ) (sec_m (Quotient.out q))).submatrix Fin.rev id) *
          ψ (lastE (outV R ξ) + sUp (sec_m (Quotient.out q)))) =
      bx R Λ₁ (Pr (m + 1)) (fun N => f ((t : K) • N)) := by
    rw [← bx_congr _ hkf]
    exact hU
  rw [e1, ← e10, ← e9, ← e7, ← hsc, fa_card_Pr]
  have hcard : (m + 1) * (m + 1 - 1) / 2 = m * (m + 1) / 2 := by
    rw [Nat.add_sub_cancel, mul_comm]
  rw [hcard]
  have hne : ((modK R (t : K) : ℝ) : ℂ) ^ (m * (m + 1) / 2) ≠ 0 := by
    exact_mod_cast (pow_pos hP _).ne'
  push_cast
  field_simp

end FA2

/- English proof (translation)
Introduce `K _ _ _ R ψ hD hn m hm L₀ Λ₀ Q hL₀ hΛ₀ hQc hQu`. Take `⟨ϖ, hA⟩` from `adic_of_datum hD hn`. Take `⟨a1, ha1⟩` from `adic_bounded hA hL₀.2`. Take `⟨a2, ha2⟩` from `adic_bounded hA hQc`. Take `⟨a3, ha3⟩` from `hA.inv_bounded hQc hQu`.

Take `⟨b, hb⟩` from `hA.basis (Λ₀ : Set K) (hΛ₀.1.mem_nhds Λ₀.zero_mem)`. Establish `hC : Cst R ϖ L₀ Λ₀ Q (a1 + a2 + a3) b` using `{ adic := hA L0 := fun x hx => Bd.mono hA.mem (by omega) (ha1 x hx) Qb := fun d hd => Bd.mono hA.mem (by omega) (ha2 d hd) Qi := fun d hd d' e => Bd.mono hA.mem (by omega) (show Bd R ϖ a3 d' from ha3 d hd d' e) abelian₂ := by`. Introduce and unpack `x ⟨r, hr, rfl⟩`. Conclude with `hb r hr }`. Take `⟨b₁, hInv⟩` from `GG_inv hD hC m`.

Take `⟨M, hLA⟩` from `levelA hD hC hL₀ m hm`. Use `⟨mulR R ((ϖ⁻¹ ^ ((m + 1) * (a1 + a2 + a3)) : Kˣ) : K), mulR R ((ϖ ^ b₁ : Kˣ) : K), fa_lat hA _, fa_lat hA _, {x | Sm R ϖ M x}, ?_, ?_⟩` and prove the remaining obligations. Establish `h1` using `I_nhds hA.isOpen (ϖ ^ M)`. Use `Filter.mem_of_superset h1 ?_` and prove the remaining obligations. Introduce and unpack `x ⟨r, hr, rfl⟩`.

Conclude with `⟨r, hr, by simp⟩`. Introduce `Φ hΦ D hDQ`. Establish `hD'Q : (((-1) ^ m * D : Kˣ) : K) ∈ Q ∨ -(((-1) ^ m * D : Kˣ) : K) ∈ Q`. Break down `neg_one_pow_eq_or Kˣ m with h | h` into its components or cases. Use `left`.

Rewrite using `[h]`. Simplify using `using hDQ`. Use `right`. Rewrite using `[h]`. Simplify using `using hDQ`.

Establish `hI : InvP R ψ ϖ Φ m (((-1) ^ m * D : Kˣ) : K) b₁` using `hInv Φ hΦ _ hD'Q`. Use `⟨fun x => bx R (mulR R ((ϖ ^ b₁ : Kˣ) : K)) (Pr (m + 1)) (GG R ψ Φ (((-1) ^ m * D : Kˣ) : K) x), fa_amp hC Φ hΦ _ hD'Q hI, ?_, ?_⟩` and prove the remaining obligations. Introduce `z hz`. Conclude with `fa_crit hD hC hm Φ hΦ _ z hz hI`. Introduce `t c ht hct Λ hΛ hΛinv`.

Use `fa_main hD hC hL₀ Φ hΦ t c _ hD'Q hI (Sm.mem hA.mem ht) ?_ Λ hΛ hΛinv` and prove the remaining obligations. Use `hLA Φ hΦ t c _ ht ?_ hD'Q _ (fa_lat hA _) (fun x => fa_inv_y hI x)` and prove the remaining obligations. Rewrite using `[← hct]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fa_oscReduction : OscReduction := by
  intro K _ _ _ R ψ hD hn m hm L₀ Λ₀ Q hL₀ hΛ₀ hQc hQu
  obtain ⟨ϖ, hA⟩ := adic_of_datum hD hn
  obtain ⟨a1, ha1⟩ := adic_bounded hA hL₀.2
  obtain ⟨a2, ha2⟩ := adic_bounded hA hQc
  obtain ⟨a3, ha3⟩ := hA.inv_bounded hQc hQu
  obtain ⟨b, hb⟩ := hA.basis (Λ₀ : Set K) (hΛ₀.1.mem_nhds Λ₀.zero_mem)
  have hC : Cst R ϖ L₀ Λ₀ Q (a1 + a2 + a3) b :=
    { adic := hA
      L0 := fun x hx => Bd.mono hA.mem (by omega) (ha1 x hx)
      Qb := fun d hd => Bd.mono hA.mem (by omega) (ha2 d hd)
      Qi := fun d hd d' e => Bd.mono hA.mem (by omega) (show Bd R ϖ a3 d' from ha3 d hd d' e)
      abelian₂ := by
        rintro x ⟨r, hr, rfl⟩
        exact hb r hr }
  obtain ⟨b₁, hInv⟩ := GG_inv hD hC m
  obtain ⟨M, hLA⟩ := levelA hD hC hL₀ m hm
  refine ⟨mulR R ((ϖ⁻¹ ^ ((m + 1) * (a1 + a2 + a3)) : Kˣ) : K), mulR R ((ϖ ^ b₁ : Kˣ) : K),
    fa_lat hA _, fa_lat hA _, {x | Sm R ϖ M x}, ?_, ?_⟩
  · have h1 := I_nhds hA.isOpen (ϖ ^ M)
    refine Filter.mem_of_superset h1 ?_
    rintro x ⟨r, hr, rfl⟩
    exact ⟨r, hr, by simp⟩
  intro Φ hΦ D hDQ
  have hD'Q : (((-1) ^ m * D : Kˣ) : K) ∈ Q ∨ -(((-1) ^ m * D : Kˣ) : K) ∈ Q := by
    rcases neg_one_pow_eq_or Kˣ m with h | h
    · left; rw [h]; simpa using hDQ
    · right; rw [h]; simpa using hDQ
  have hI : InvP R ψ ϖ Φ m (((-1) ^ m * D : Kˣ) : K) b₁ := hInv Φ hΦ _ hD'Q
  refine ⟨fun x => bx R (mulR R ((ϖ ^ b₁ : Kˣ) : K)) (Pr (m + 1))
    (GG R ψ Φ (((-1) ^ m * D : Kˣ) : K) x), fa_amp hC Φ hΦ _ hD'Q hI, ?_, ?_⟩
  · intro z hz
    exact fa_crit hD hC hm Φ hΦ _ z hz hI
  · intro t c ht hct Λ hΛ hΛinv
    refine fa_main hD hC hL₀ Φ hΦ t c _ hD'Q hI (Sm.mem hA.mem ht) ?_ Λ hΛ hΛinv
    refine hLA Φ hΦ t c _ ht ?_ hD'Q _ (fa_lat hA _) (fun x => fa_inv_y hI x)
    rw [← hct]
    push_cast
    ring

end Formalism.FourierDecayAlt.P.OrbitalIntegralReduction

namespace Formalism.FourierDecayAlt.P

/- English proof (translation)
The claim follows from `OrbitalIntegralReduction.fa_oscReduction`.
-/
theorem orbital_integral_change_of_variables : Formalism.FourierDecayAlt.A6.OscReduction := OrbitalIntegralReduction.fa_oscReduction

end Formalism.FourierDecayAlt.P
