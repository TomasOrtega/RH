import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne

noncomputable section

namespace GlobalTheory.KumDlog

open GlobalTheory.K5

variable {p : ℕ} [Fact p.Prime] {Ω : Type*} [Field Ω] [Algebra (O0 p) Ω]

def IsDer (S : Subalgebra (O0 p) Ω) (D : Ω → Ω) : Prop :=
  (∀ x ∈ S, ∀ y ∈ S, IsInt p (D (x + y) - D x - D y)) ∧
  (∀ x ∈ S, ∀ y ∈ S, IsInt p (D (x * y) - x * D y - y * D x)) ∧
  ∀ c : O0 p, IsInt p (D (algebraMap (O0 p) Ω c))

def FixI (G : Subgroup (Gal p Ω)) : Subalgebra (O0 p) Ω where
  carrier := {x | IsInt p x ∧ ∀ g ∈ G, g x = x}
  mul_mem' := fun {a b} ha hb =>
    ⟨IsIntegral.mul ha.1 hb.1, fun g hg => by rw [map_mul, ha.2 g hg, hb.2 g hg]⟩
  add_mem' := fun {a b} ha hb =>
    ⟨IsIntegral.add ha.1 hb.1, fun g hg => by rw [map_add, ha.2 g hg, hb.2 g hg]⟩
  algebraMap_mem' := fun c => ⟨isIntegral_algebraMap, fun g _ => g.commutes c⟩

def Hinf (T : Tower p Ω) : Subgroup (Gal p Ω) := ⨅ n, Gn T n

def Hfix (T : Tower p Ω) (r : Ω) : Subgroup (Gal p Ω) :=
  Hinf T ⊓ MulAction.stabilizer (Gal p Ω) r

def Lev (T : Tower p Ω) (m : ℕ) : Subalgebra (O0 p) Ω :=
  Algebra.adjoin (O0 p) {T.ζ m, T.qq m}

def Vals (T : Tower p Ω) (m : ℕ) (dz dq : Ω → Ω) : Prop :=
  IsInt p (dz (T.ζ m) - p * T.ζ m / (p : Ω) ^ m) ∧ IsInt p (dz (T.qq m)) ∧
  IsInt p (dq (T.ζ m)) ∧ IsInt p (dq (T.qq m) - p * T.qq m / (p : Ω) ^ m)

def DualData (B C : Subalgebra (O0 p) Ω) {ι : Type} [Fintype ι] (u v : ι → Ω) (tr : Ω → Ω) : Prop :=
  B ≤ C ∧ (∀ x ∈ C, IsInt p x) ∧ (∀ k, u k ∈ C) ∧ (∀ k, v k ∈ C) ∧ (∀ x ∈ C, tr x ∈ B) ∧
  (∀ x ∈ C, ∀ y ∈ C, tr (x + y) = tr x + tr y) ∧ (∀ b ∈ B, ∀ x ∈ C, tr (b * x) = b * tr x) ∧
  (∀ y ∈ C, ∑ k, u k * tr (v k * y) = p * y) ∧ (∀ y ∈ C, ∑ k, v k * tr (u k * y) = p * y) ∧
  ∑ k, u k * v k = p

/- English proof (translation)
Unfold both sides to obtain the same proposition, which implies itself.
-/
theorem mem_FixI {G : Subgroup (Gal p Ω)} {x : Ω} :
    x ∈ FixI G ↔ IsInt p x ∧ ∀ g ∈ G, g x = x := Iff.rfl

/- English proof (translation)
Unfold both sides to obtain the same proposition, which implies itself.
-/
theorem mem_Gn {T : Tower p Ω} {n : ℕ} {g : Gal p Ω} :
    g ∈ Gn T n ↔ g (T.ζ n) = T.ζ n ∧ g (T.qq n) = T.qq n := Iff.rfl

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem mem_Hinf {T : Tower p Ω} {g : Gal p Ω} :
    g ∈ Hinf T ↔ ∀ n, g (T.ζ n) = T.ζ n ∧ g (T.qq n) = T.qq n := by
  simp only [Hinf, Subgroup.mem_iInf, mem_Gn]

/- English proof (translation)
Unfold both sides to obtain the same proposition, which implies itself.
-/
theorem mem_Hfix {T : Tower p Ω} {r : Ω} {g : Gal p Ω} :
    g ∈ Hfix T r ↔ g ∈ Hinf T ∧ g r = r := Iff.rfl

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem int_add {x y : Ω} (hx : IsInt p x) (hy : IsInt p y) : IsInt p (x + y) := IsIntegral.add hx hy
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem int_sub {x y : Ω} (hx : IsInt p x) (hy : IsInt p y) : IsInt p (x - y) := IsIntegral.sub hx hy
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem int_mul {x y : Ω} (hx : IsInt p x) (hy : IsInt p y) : IsInt p (x * y) := IsIntegral.mul hx hy
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem int_neg {x : Ω} (hx : IsInt p x) : IsInt p (-x) := IsIntegral.neg hx
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem int_pow {x : Ω} (hx : IsInt p x) (k : ℕ) : IsInt p (x ^ k) := IsIntegral.pow hx k
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem int_alg (c : O0 p) : IsInt p (algebraMap (O0 p) Ω c) := isIntegral_algebraMap
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem int_zero : IsInt p (0 : Ω) := isIntegral_zero
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem int_one : IsInt p (1 : Ω) := isIntegral_one
/- English proof (translation)
Simplify to obtain the desired conclusion from the available facts.
-/
theorem int_nat (k : ℕ) : IsInt p (k : Ω) := by
  simpa using (int_alg (k : O0 p) : IsInt p (algebraMap (O0 p) Ω _))
/- English proof (translation)
Simplify to obtain the desired conclusion from the available facts.
-/
theorem int_int (k : ℤ) : IsInt p (k : Ω) := by
  simpa using (int_alg (k : O0 p) : IsInt p (algebraMap (O0 p) Ω _))
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem int_sum {ι : Type*} (s : Finset ι) (f : ι → Ω) (h : ∀ i ∈ s, IsInt p (f i)) :
    IsInt p (∑ i ∈ s, f i) := IsIntegral.sum f h
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem int_congr {x y : Ω} (hx : IsInt p x) (h : y = x) : IsInt p y := h ▸ hx
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem int_gal (g : Gal p Ω) {x : Ω} (hx : IsInt p x) : IsInt p (g x) :=
  IsIntegral.map (g : Ω →ₐ[O0 p] Ω) hx
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem int_of_pow {x : Ω} {k : ℕ} (hk : 0 < k) (hx : IsInt p (x ^ k)) : IsInt p x :=
  IsIntegral.of_pow hk hx

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately.
-/
theorem zeta_pow (T : Tower p Ω) (n j : ℕ) : T.ζ (n + j) ^ (p ^ j) = T.ζ n := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ', pow_mul, ← add_assoc, T.ζpow, ih]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately.
-/
theorem qq_pow (T : Tower p Ω) (n j : ℕ) : T.qq (n + j) ^ (p ^ j) = T.qq n := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ', pow_mul, ← add_assoc, T.qpow, ih]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ppow_pos (n : ℕ) : 0 < p ^ n := pow_pos (Fact.out : p.Prime).pos n

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem int_zeta (T : Tower p Ω) (n : ℕ) : IsInt p (T.ζ n) :=
  int_of_pow (ppow_pos n) (by rw [(T.prim n).pow_eq_one]; exact int_one)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem zeta_ne (T : Tower p Ω) (n : ℕ) : T.ζ n ≠ 0 := (T.prim n).ne_zero (ppow_pos n).ne'

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem int_zeta_inv (T : Tower p Ω) (n : ℕ) : IsInt p (T.ζ n)⁻¹ :=
  int_of_pow (ppow_pos n) (by rw [inv_pow, (T.prim n).pow_eq_one, inv_one]; exact int_one)

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem kummerTower_qq_pow_level_eq_q (T : Tower p Ω) (n : ℕ) : T.qq n ^ (p ^ n) = algebraMap (O0 p) Ω (qO p) := by
  have := qq_pow T 0 n
  rwa [zero_add, T.q0] at this

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem isUnit_qO : IsUnit (qO p) := by
  refine IsUnit.map _ (IsUnit.of_mul_eq_one (HahnSeries.single (-1 : ℤ) (1 : ℤ_[p])) ?_)
  rw [HahnSeries.single_mul_single]; simp

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem int_qq (T : Tower p Ω) (n : ℕ) : IsInt p (T.qq n) :=
  int_of_pow (ppow_pos n) (by rw [kummerTower_qq_pow_level_eq_q]; exact int_alg _)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem qq_ne (T : Tower p Ω) (n : ℕ) : T.qq n ≠ 0 := by
  intro h
  have h1 := kummerTower_qq_pow_level_eq_q T n
  rw [h, zero_pow (ppow_pos (p := p) n).ne'] at h1
  exact ((isUnit_qO (p := p)).map (algebraMap (O0 p) Ω)).ne_zero h1.symm

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem int_qq_inv (T : Tower p Ω) (n : ℕ) : IsInt p (T.qq n)⁻¹ := by
  refine int_of_pow (ppow_pos (p := p) n) ?_
  obtain ⟨w, hw⟩ := (isUnit_qO (p := p))
  rw [inv_pow, kummerTower_qq_pow_level_eq_q, ← hw]
  refine int_congr (int_alg (↑w⁻¹ : O0 p)) ?_
  exact inv_eq_of_mul_eq_one_right (by rw [← map_mul]; simp)

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending. A detailed English derivation is pending.
-/
theorem Lev_int (T : Tower p Ω) (m : ℕ) : ∀ x ∈ Lev T m, IsInt p x := by
  have : Lev T m ≤ integralClosure (O0 p) Ω := by
    refine Algebra.adjoin_le ?_
    rintro x (rfl | rfl)
    · exact int_zeta T m
    · exact int_qq T m
  exact fun x hx => this hx

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem zeta_mem_Lev (T : Tower p Ω) (m : ℕ) : T.ζ m ∈ Lev T m :=
  Algebra.subset_adjoin (by simp)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem qq_mem_Lev (T : Tower p Ω) (m : ℕ) : T.qq m ∈ Lev T m :=
  Algebra.subset_adjoin (by simp)

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem Lev_mono (T : Tower p Ω) {m m' : ℕ} (h : m ≤ m') : Lev T m ≤ Lev T m' := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  refine Algebra.adjoin_le ?_
  rintro x (rfl | rfl)
  · rw [← zeta_pow T m j]; exact pow_mem (zeta_mem_Lev T _) _
  · rw [← qq_pow T m j]; exact pow_mem (qq_mem_Lev T _) _

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Supply the required witnesses or components.
-/
theorem Lev_le_FixI (T : Tower p Ω) (m : ℕ) {G : Subgroup (Gal p Ω)} (hG : G ≤ Gn T m) :
    Lev T m ≤ FixI G := by
  refine Algebra.adjoin_le ?_
  rintro x (rfl | rfl)
  · exact ⟨int_zeta T m, fun g hg => (hG hg).1⟩
  · exact ⟨int_qq T m, fun g hg => (hG hg).2⟩

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Hinf_le (T : Tower p Ω) (m : ℕ) : Hinf T ≤ Gn T m := iInf_le _ m

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem IsDer.mono {S S' : Subalgebra (O0 p) Ω} {D : Ω → Ω} (h : IsDer S D) (hS : S' ≤ S) :
    IsDer S' D :=
  ⟨fun x hx y hy => h.1 x (hS hx) y (hS hy), fun x hx y hy => h.2.1 x (hS hx) y (hS hy), h.2.2⟩

/- English proof (translation)
Simplify to obtain the desired conclusion from the available facts.
-/
theorem IsDer.zero {S : Subalgebra (O0 p) Ω} {D : Ω → Ω} (h : IsDer S D) : IsInt p (D 0) := by
  simpa using h.2.2 0

/- English proof (translation)
Simplify to obtain the desired conclusion from the available facts.
-/
theorem IsDer.one {S : Subalgebra (O0 p) Ω} {D : Ω → Ω} (h : IsDer S D) : IsInt p (D 1) := by
  simpa using h.2.2 1

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

A detailed English derivation is pending.
-/
theorem IsDer.sum {S : Subalgebra (O0 p) Ω} {D : Ω → Ω} (h : IsDer S D) {ι : Type*}
    (s : Finset ι) (f : ι → Ω) (hf : ∀ i ∈ s, f i ∈ S) :
    IsInt p (D (∑ i ∈ s, f i) - ∑ i ∈ s, D (f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h.zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have h1 := h.1 (f a) (hf a (by simp)) (∑ i ∈ s, f i)
      (sum_mem fun i hi => hf i (by simp [hi]))
    exact int_congr (int_add h1 (ih fun i hi => hf i (by simp [hi]))) (by ring)

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem IsDer.pow {S : Subalgebra (O0 p) Ω} {D : Ω → Ω} (h : IsDer S D)
    (hS : ∀ x ∈ S, IsInt p x) {x : Ω} (hx : x ∈ S) (k : ℕ) :
    IsInt p (D (x ^ (k + 1)) - (k + 1 : ℕ) * x ^ k * D x) := by
  induction k with
  | zero => simpa using int_zero
  | succ k ih =>
    have h1 := h.2.1 x hx (x ^ (k + 1)) (pow_mem hx _)
    refine int_congr (int_add h1 (int_mul (hS x hx) ih)) ?_
    rw [← pow_succ']; push_cast; ring

/- English proof (translation)
Separate the alternatives or extract the components of the hypothesis. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem IsDer.pow' {S : Subalgebra (O0 p) Ω} {D : Ω → Ω} (h : IsDer S D)
    (hS : ∀ x ∈ S, IsInt p x) {x : Ω} (hx : x ∈ S) (k : ℕ) :
    IsInt p (x * D (x ^ k) - k * x ^ k * D x) := by
  rcases k with _ | k
  · simpa using int_mul (hS x hx) h.one
  · exact int_congr (int_mul (hS x hx) (h.pow hS hx k)) (by ring)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem IsDer.alg_mul {S : Subalgebra (O0 p) Ω} {D : Ω → Ω} (h : IsDer S D)
    (hS : ∀ x ∈ S, IsInt p x) (c : O0 p) {x : Ω} (hx : x ∈ S) :
    IsInt p (D (algebraMap (O0 p) Ω c * x) - algebraMap (O0 p) Ω c * D x) :=
  int_congr (int_add (h.2.1 _ (S.algebraMap_mem c) x hx) (int_mul (hS x hx) (h.2.2 c))) (by ring)

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem IsDer.sub {S : Subalgebra (O0 p) Ω} {D D' : Ω → Ω} (h : IsDer S D) (h' : IsDer S D') :
    IsDer S (fun x => D x - D' x) :=
  ⟨fun x hx y hy => int_congr (int_sub (h.1 x hx y hy) (h'.1 x hx y hy)) (by ring),
   fun x hx y hy => int_congr (int_sub (h.2.1 x hx y hy) (h'.2.1 x hx y hy)) (by ring),
   fun c => int_sub (h.2.2 c) (h'.2.2 c)⟩

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem IsDer.smul {S : Subalgebra (O0 p) Ω} {D : Ω → Ω} (h : IsDer S D) {c : Ω}
    (hc : IsInt p c) : IsDer S (fun x => c * D x) :=
  ⟨fun x hx y hy => int_congr (int_mul hc (h.1 x hx y hy)) (by ring),
   fun x hx y hy => int_congr (int_mul hc (h.2.1 x hx y hy)) (by ring),
   fun a => int_mul hc (h.2.2 a)⟩

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem IsDer.conj {S : Subalgebra (O0 p) Ω} {D : Ω → Ω} (h : IsDer S D) (g : Gal p Ω)
    (hg : ∀ x ∈ S, g x ∈ S) : IsDer S (fun x => g.symm (D (g x))) := by
  refine ⟨fun x hx y hy => ?_, fun x hx y hy => ?_, fun c => ?_⟩
  · refine int_congr (int_gal g.symm (h.1 _ (hg x hx) _ (hg y hy))) ?_
    simp
  · refine int_congr (int_gal g.symm (h.2.1 _ (hg x hx) _ (hg y hy))) ?_
    simp
  · refine int_gal g.symm ?_
    rw [g.commutes]; exact h.2.2 c

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Treat this case separately.

Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
theorem IsDer.adjoin {S : Subalgebra (O0 p) Ω} {D : Ω → Ω} (h : IsDer S D)
    (hS : ∀ x ∈ S, IsInt p x) {t : Set Ω} (ht : t ⊆ S) (h0 : ∀ x ∈ t, IsInt p (D x)) :
    ∀ x ∈ Algebra.adjoin (O0 p) t, IsInt p (D x) := by
  have hle : Algebra.adjoin (O0 p) t ≤ S := Algebra.adjoin_le ht
  intro x hx
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact h0 x hx
  | algebraMap c => exact h.2.2 c
  | add x y hx hy ihx ihy =>
    exact int_congr (int_add (h.1 x (hle hx) y (hle hy)) (int_add ihx ihy)) (by ring)
  | mul x y hx hy ihx ihy =>
    exact int_congr (int_add (h.2.1 x (hle hx) y (hle hy))
      (int_add (int_mul (hS x (hle hx)) ihy) (int_mul (hS y (hle hy)) ihx))) (by ring)

end GlobalTheory.KumDlog
