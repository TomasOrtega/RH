import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.FixBound

def enorm {R : Type} [NormedRing R] {n : ℕ} (A : Matrix (Fin n) (Fin n) R) : ℝ := ∑ i, ∑ j, ‖A i j‖

/- English proof (translation)
The claim follows from `Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _`.
-/
theorem enorm_nonneg {R : Type} [NormedRing R] {n : ℕ} (A : Matrix (Fin n) (Fin n) R) : 0 ≤ enorm A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

/- English proof (translation)
Unfold `enorm`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_le_enorm {R : Type} [NormedRing R] {n : ℕ} (A : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    ‖A i j‖ ≤ enorm A := by
  unfold enorm
  calc ‖A i j‖ ≤ ∑ j', ‖A i j'‖ :=
        Finset.single_le_sum (f := fun j' => ‖A i j'‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', ‖A i' j'‖ :=
        Finset.single_le_sum (f := fun i' => ∑ j', ‖A i' j'‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)

/- English proof (translation)
Unfold `enorm`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem enorm_le_of {R : Type} [NormedRing R] {n : ℕ} (A : Matrix (Fin n) (Fin n) R) (t : ℝ)
    (h : ∀ i j, ‖A i j‖ ≤ t) : enorm A ≤ n * n * t := by
  unfold enorm
  calc ∑ i, ∑ j, ‖A i j‖ ≤ ∑ _i : Fin n, ∑ _j : Fin n, t :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h i j
    _ = n * n * t := by simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, mul_assoc]

/- English proof (translation)
Unfold `enorm`. Establish `hB : ∀ k, ∑ j, ‖B k j‖ ≤ ∑ k', ∑ j, ‖B k' j‖` using `fun k => Finset.single_le_sum (f := fun k' => ∑ j, ‖B k' j‖) (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ k)`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mul_apply]`.

Conclude with `(norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => norm_mul_le _ _)`. Use `_ = ∑ i, ∑ k, ‖A i k‖ * ∑ j, ‖B k j‖ := by`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun k _ => (Finset.mul_sum _ _ _).symm`.

Use `_ ≤ ∑ i, ∑ k, ‖A i k‖ * ∑ k', ∑ j, ‖B k' j‖ := Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hB k) (norm_nonneg _)`. Use `_ = _ := by`. Rewrite using `[Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun i _ => (Finset.sum_mul _ _ _).symm`.
-/
theorem enorm_mul_le {R : Type} [NormedRing R] {n : ℕ} (A B : Matrix (Fin n) (Fin n) R) :
    enorm (A * B) ≤ enorm A * enorm B := by
  unfold enorm
  have hB : ∀ k, ∑ j, ‖B k j‖ ≤ ∑ k', ∑ j, ‖B k' j‖ := fun k =>
    Finset.single_le_sum (f := fun k' => ∑ j, ‖B k' j‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ k)
  calc ∑ i, ∑ j, ‖(A * B) i j‖ ≤ ∑ i, ∑ j, ∑ k, ‖A i k‖ * ‖B k j‖ := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        rw [Matrix.mul_apply]
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => norm_mul_le _ _)
    _ = ∑ i, ∑ k, ‖A i k‖ * ∑ j, ‖B k j‖ := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ => (Finset.mul_sum _ _ _).symm
    _ ≤ ∑ i, ∑ k, ‖A i k‖ * ∑ k', ∑ j, ‖B k' j‖ :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ =>
          mul_le_mul_of_nonneg_left (hB k) (norm_nonneg _)
    _ = _ := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => (Finset.sum_mul _ _ _).symm

variable {p : ℕ} [Fact p.Prime]

def mulMap (K : IntermediateField ℚ_[p] (PadicAlgCl p)) : KQ p K 1 →+* PadicAlgCl p :=
  (Algebra.TensorProduct.productMap K.val (Qr p 1).val : K ⊗[ℚ_[p]] Qr p 1 →ₐ[ℚ_[p]] PadicAlgCl p).toRingHom

/- English proof (translation)
Use `show Algebra.TensorProduct.productMap K.val (Qr p 1).val (a ⊗ₜ[ℚ_[p]] (1 : Qr p 1)) = _`. Simplify using `[Algebra.TensorProduct.productMap_apply_tmul]`.
-/
theorem mulMap_inclK (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (a : K) :
    mulMap K (inclK p K 1 a) = (a : PadicAlgCl p) := by
  show Algebra.TensorProduct.productMap K.val (Qr p 1).val (a ⊗ₜ[ℚ_[p]] (1 : Qr p 1)) = _
  simp [Algebra.TensorProduct.productMap_apply_tmul]

/- English proof (translation)
Use `show Algebra.TensorProduct.productMap K.val (Qr p 1).val ((1 : K) ⊗ₜ[ℚ_[p]] b) = _`. Simplify using `[Algebra.TensorProduct.productMap_apply_tmul]`.
-/
theorem mulMap_inclQ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (b : Qr p 1) :
    mulMap K (inclQ p K 1 b) = (b : PadicAlgCl p) := by
  show Algebra.TensorProduct.productMap K.val (Qr p 1).val ((1 : K) ⊗ₜ[ℚ_[p]] b) = _
  simp [Algebra.TensorProduct.productMap_apply_tmul]

/- English proof (translation)
Establish `h : intKQ p K 1 ≤ (Obar p).toSubring.comap (mulMap K)`. Use `Subring.closure_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ (⟨a, rfl⟩ | ⟨b, rfl⟩)`. Use `show mulMap K (inclK p K 1 a) ∈ Obar p`. Rewrite using `[mulMap_inclK]`.

Conclude with `a.2`. Use `show mulMap K (inclQ p K 1 b) ∈ Obar p`. Rewrite using `[mulMap_inclQ]`. Conclude with `b.2`. Conclude with `mem_Obar_iff.1 (h hx)`.
-/
theorem norm_mulMap_le_one (K : IntermediateField ℚ_[p] (PadicAlgCl p)) {x : KQ p K 1}
    (hx : x ∈ intKQ p K 1) : ‖mulMap K x‖ ≤ 1 := by
  have h : intKQ p K 1 ≤ (Obar p).toSubring.comap (mulMap K) := by
    refine Subring.closure_le.2 ?_
    rintro _ (⟨a, rfl⟩ | ⟨b, rfl⟩)
    · show mulMap K (inclK p K 1 a) ∈ Obar p
      rw [mulMap_inclK]; exact a.2
    · show mulMap K (inclQ p K 1 b) ∈ Obar p
      rw [mulMap_inclQ]; exact b.2
  exact mem_Obar_iff.1 (h hx)

def E (G : HTGroup p) (g : Gr G 1) : ℝ :=
  enorm ((g.1 : Matrix (Fin 1) (Fin 1) (Qr p 1)).map (algebraMap (Qr p 1) (PadicAlgCl p))) +
    ∑ w, enorm ((g.2 w : Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw w) 1)).map (mulMap (G.Fw w)))

/- English proof (translation)
The claim follows from `add_nonneg (enorm_nonneg _) (Finset.sum_nonneg fun _ _ => enorm_nonneg _)`.
-/
theorem E_nonneg (G : HTGroup p) (g : Gr G 1) : 0 ≤ E G g :=
  add_nonneg (enorm_nonneg _) (Finset.sum_nonneg fun _ _ => enorm_nonneg _)

/- English proof (translation)
Unfold `E`. Use `set a := enorm ((g.1 : Matrix (Fin 1) (Fin 1) (Qr p 1)).map (algebraMap (Qr p 1) (PadicAlgCl p)))`. Use `set a' := enorm ((h.1 : Matrix (Fin 1) (Fin 1) (Qr p 1)).map (algebraMap (Qr p 1) (PadicAlgCl p)))`. Use `set b := fun w => enorm ((g.2 w : Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw w) 1)).map (mulMap (G.Fw w)))`. Use `set b' := fun w => enorm ((h.2 w : Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw w) 1)).map (mulMap (G.Fw w)))`.

Establish `h1 : enorm (((g * h).1 : Matrix (Fin 1) (Fin 1) (Qr p 1)).map (algebraMap (Qr p 1) (PadicAlgCl p))) ≤ a * a'`. Rewrite using `[Prod.fst_mul, Units.val_mul, Matrix.map_mul]`. Conclude with `enorm_mul_le _ _`. Establish `h2 : ∀ w, enorm (((g * h).2 w : Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw w) 1)).map (mulMap (G.Fw w))) ≤ b w * b' w`. Introduce `w`.

Rewrite using `[Prod.snd_mul, Pi.mul_apply, Units.val_mul, Matrix.map_mul]`. Conclude with `enorm_mul_le _ _`. Establish `ha : 0 ≤ a` using `enorm_nonneg _`. Establish `ha' : 0 ≤ a'` using `enorm_nonneg _`. Establish `hb : ∀ w, 0 ≤ b w` using `fun _ => enorm_nonneg _`.

Establish `hb' : ∀ w, 0 ≤ b' w` using `fun _ => enorm_nonneg _`. Establish `hB : 0 ≤ ∑ w, b w` using `Finset.sum_nonneg fun w _ => hb w`. Establish `hB' : 0 ≤ ∑ w, b' w` using `Finset.sum_nonneg fun w _ => hb' w`. Establish `h3 : ∑ w, b w * b' w ≤ (∑ w, b w) * ∑ w, b' w`. Rewrite using `[Finset.sum_mul]`.

Conclude with `Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left (Finset.single_le_sum (f := b') (fun w _ => hb' w) (Finset.mem_univ w)) (hb w)`. Establish `h4 : ∑ w, enorm (((g * h).2 w : Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw w) 1)).map (mulMap (G.Fw w))) ≤ ∑ w, b w * b' w` using `Finset.sum_le_sum fun w _ => h2 w`. Use polynomial arithmetic with `[mul_nonneg ha hB', mul_nonneg hB ha']`.
-/
theorem E_mul (G : HTGroup p) (g h : Gr G 1) : E G (g * h) ≤ E G g * E G h := by
  unfold E
  set a := enorm ((g.1 : Matrix (Fin 1) (Fin 1) (Qr p 1)).map (algebraMap (Qr p 1) (PadicAlgCl p)))
  set a' := enorm ((h.1 : Matrix (Fin 1) (Fin 1) (Qr p 1)).map (algebraMap (Qr p 1) (PadicAlgCl p)))
  set b := fun w => enorm ((g.2 w : Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw w) 1)).map (mulMap (G.Fw w)))
  set b' := fun w => enorm ((h.2 w : Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw w) 1)).map (mulMap (G.Fw w)))
  have h1 : enorm (((g * h).1 : Matrix (Fin 1) (Fin 1) (Qr p 1)).map (algebraMap (Qr p 1) (PadicAlgCl p))) ≤ a * a' := by
    rw [Prod.fst_mul, Units.val_mul, Matrix.map_mul]; exact enorm_mul_le _ _
  have h2 : ∀ w, enorm (((g * h).2 w : Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw w) 1)).map (mulMap (G.Fw w))) ≤
      b w * b' w := by
    intro w
    rw [Prod.snd_mul, Pi.mul_apply, Units.val_mul, Matrix.map_mul]; exact enorm_mul_le _ _
  have ha : 0 ≤ a := enorm_nonneg _
  have ha' : 0 ≤ a' := enorm_nonneg _
  have hb : ∀ w, 0 ≤ b w := fun _ => enorm_nonneg _
  have hb' : ∀ w, 0 ≤ b' w := fun _ => enorm_nonneg _
  have hB : 0 ≤ ∑ w, b w := Finset.sum_nonneg fun w _ => hb w
  have hB' : 0 ≤ ∑ w, b' w := Finset.sum_nonneg fun w _ => hb' w
  have h3 : ∑ w, b w * b' w ≤ (∑ w, b w) * ∑ w, b' w := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (f := b') (fun w _ => hb' w) (Finset.mem_univ w)) (hb w)
  have h4 : ∑ w, enorm (((g * h).2 w : Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw w) 1)).map (mulMap (G.Fw w))) ≤
      ∑ w, b w * b' w := Finset.sum_le_sum fun w _ => h2 w
  nlinarith [mul_nonneg ha hB', mul_nonneg hB ha']

/- English proof (translation)
The claim follows from `(E_mul G g h).trans (mul_le_mul hg hh (E_nonneg G h) ((E_nonneg G g).trans hg))`.
-/
theorem E_mul_le (G : HTGroup p) {g h : Gr G 1} {s t : ℝ} (hg : E G g ≤ s) (hh : E G h ≤ t) :
    E G (g * h) ≤ s * t :=
  (E_mul G g h).trans (mul_le_mul hg hh (E_nonneg G h) ((E_nonneg G g).trans hg))

/- English proof (translation)
Rewrite `hk` using `[KHT, Subgroup.mem_prod]`. Take `⟨h1, h2⟩` from `hk`. Use `add_le_add ?_ (Finset.sum_le_sum fun w _ => ?_)` and prove the remaining obligations. Use `enorm_le_of _ _ fun i j => ?_` and prove the remaining obligations. Take `⟨x, hx⟩` from `h1`.

Rewrite using `[← hx]`. Conclude with `mem_Obar_iff.1 (((x : Matrix (Fin 1) (Fin 1) (GlobalTheory.LKLoc.intR p (Q0 p) 1)) i j).2)`. Use `enorm_le_of _ _ fun i j => ?_` and prove the remaining obligations. Take `⟨x, hx⟩` from `(Subgroup.mem_pi _).1 h2 w (Set.mem_univ w)`. Rewrite using `[← hx]`.

Conclude with `norm_mulMap_le_one _ (((x : Matrix (Fin G.n) (Fin G.n) (intKQ p (G.Fw w) 1)) i j).2)`.
-/
theorem E_int (G : HTGroup p) {k : Gr G 1} (hk : k ∈ KHT p G.m G.n 1 G.Fw) :
    E G k ≤ ((1 : ℕ) : ℝ) * ((1 : ℕ) : ℝ) * 1 + ∑ _w : Fin G.m, (G.n : ℝ) * G.n * 1 := by
  rw [KHT, Subgroup.mem_prod] at hk
  obtain ⟨h1, h2⟩ := hk
  refine add_le_add ?_ (Finset.sum_le_sum fun w _ => ?_)
  · refine enorm_le_of _ _ fun i j => ?_
    obtain ⟨x, hx⟩ := h1
    rw [← hx]
    exact mem_Obar_iff.1 (((x : Matrix (Fin 1) (Fin 1) (GlobalTheory.LKLoc.intR p (Q0 p) 1)) i j).2)
  · refine enorm_le_of _ _ fun i j => ?_
    obtain ⟨x, hx⟩ := (Subgroup.mem_pi _).1 h2 w (Set.mem_univ w)
    rw [← hx]
    exact norm_mulMap_le_one _ (((x : Matrix (Fin G.n) (Fin G.n) (intKQ p (G.Fw w) 1)) i j).2)

def Rw (G : HTGroup p) (w : Fin G.m) (c : G.C) : Matrix (Fin G.n) (Fin G.n) (PadicAlgCl p) :=
  (G.rho w c).map (algebraMap (G.Fw w) (PadicAlgCl p))

/- English proof (translation)
Unfold `Rw`. Rewrite using `[map_mul, Matrix.map_mul]`.
-/
theorem Rw_mul (G : HTGroup p) (w : Fin G.m) (c d : G.C) : Rw G w (c * d) = Rw G w c * Rw G w d := by
  unfold Rw; rw [map_mul, Matrix.map_mul]

/- English proof (translation)
Use extensionality with `a b`. Use `show mulMap (G.Fw w) (inclK p (G.Fw w) 1 (G.rho w (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) a b)) = _`. Rewrite using `[mulMap_inclK]`. Both sides reduce to the same expression.
-/
theorem formGroupToPadicPointsDegreeOne_snd_map_eq_rho (G : HTGroup p) (β : G.Cˣ) (y : grp G β) (w : Fin G.m) :
    (((toP1 G β y).2 w : GL (Fin G.n) (KQ p (G.Fw w) 1)) : Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw w) 1)).map
      (mulMap (G.Fw w)) = Rw G w (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) := by
  ext a b
  show mulMap (G.Fw w) (inclK p (G.Fw w) 1 (G.rho w (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) a b)) = _
  rw [mulMap_inclK]; rfl

/- English proof (translation)
Use `show algebraMap (Qr p 1) (PadicAlgCl p) ((GeneralLinearGroup.scalar (Fin 1) (Units.map (algebraMap ℚ_[p] (Qr p 1)).toMonoidHom (Units.map (algebraMap ℚ ℚ_[p]).toMonoidHom (y : G.Cˣ × ℚˣ).2)) : Matrix (Fin 1) (Fin 1) (Qr p 1)) 0 0) = _`. Simplify using `[GeneralLinearGroup.scalar]`.
-/
theorem formGroupToPadicPointsDegreeOne_fst_entry_eq_factor (G : HTGroup p) (β : G.Cˣ) (y : grp G β) :
    ((((toP1 G β y).1 : GL (Fin 1) (Qr p 1)) : Matrix (Fin 1) (Fin 1) (Qr p 1)).map
      (algebraMap (Qr p 1) (PadicAlgCl p))) 0 0 = algebraMap ℚ (PadicAlgCl p) (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) := by
  show algebraMap (Qr p 1) (PadicAlgCl p) ((GeneralLinearGroup.scalar (Fin 1)
    (Units.map (algebraMap ℚ_[p] (Qr p 1)).toMonoidHom (Units.map (algebraMap ℚ ℚ_[p]).toMonoidHom (y : G.Cˣ × ℚˣ).2)) :
      Matrix (Fin 1) (Fin 1) (Qr p 1)) 0 0) = _
  simp [GeneralLinearGroup.scalar]

/- English proof (translation)
Rewrite using `[IsScalarTower.algebraMap_apply ℚ ℚ_[p] (PadicAlgCl p), norm_algebraMap', eq_ratCast]`.
-/
theorem norm_algebraMap_rat (q : ℚ) : ‖algebraMap ℚ (PadicAlgCl p) q‖ = ‖(q : ℚ_[p])‖ := by
  rw [IsScalarTower.algebraMap_apply ℚ ℚ_[p] (PadicAlgCl p), norm_algebraMap', eq_ratCast]

/- English proof (translation)
Introduce `hd`. Establish `hp` using `(Fact.out : p.Prime)`. Establish `hn : ¬ (p : ℤ) ∣ q.num` using `fun hn => by`. Establish `h1 : p ∣ q.num.natAbs` using `Int.ofNat_dvd_left.1 hn`. Establish `h2` using `Nat.dvd_gcd h1 hd`.

Rewrite `h2` using `[q.reduced.gcd_eq_one]`. Conclude with `hp.one_lt.ne' (Nat.dvd_one.1 h2)`. Establish `h1 : padicNorm p (q.num : ℚ) = 1` using `(padicNorm.int_eq_one_iff _).2 hn`. Establish `h2 : padicNorm p ((q.den : ℤ) : ℚ) < 1` using `(padicNorm.int_lt_one_iff _).2 (Int.natCast_dvd_natCast.2 hd)`. Establish `h3 : (q.num : ℚ) = q * ((q.den : ℤ) : ℚ)` using `by push_cast; exact (Rat.mul_den_eq_num q).symm`.

Rewrite `h1` using `[h3, padicNorm.mul]`. Establish `h4` using `padicNorm.nonneg (p := p) ((q.den : ℤ) : ℚ)`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem not_dvd_den_of_padicNorm_le_one (q : ℚ) (hq : padicNorm p q ≤ 1) : ¬ p ∣ q.den := by
  intro hd
  have hp := (Fact.out : p.Prime)
  have hn : ¬ (p : ℤ) ∣ q.num := fun hn => by
    have h1 : p ∣ q.num.natAbs := Int.ofNat_dvd_left.1 hn
    have h2 := Nat.dvd_gcd h1 hd
    rw [q.reduced.gcd_eq_one] at h2
    exact hp.one_lt.ne' (Nat.dvd_one.1 h2)
  have h1 : padicNorm p (q.num : ℚ) = 1 := (padicNorm.int_eq_one_iff _).2 hn
  have h2 : padicNorm p ((q.den : ℤ) : ℚ) < 1 := (padicNorm.int_lt_one_iff _).2 (Int.natCast_dvd_natCast.2 hd)
  have h3 : (q.num : ℚ) = q * ((q.den : ℤ) : ℚ) := by push_cast; exact (Rat.mul_den_eq_num q).symm
  rw [h3, padicNorm.mul] at h1
  have h4 := padicNorm.nonneg (p := p) ((q.den : ℤ) : ℚ)
  nlinarith

/- English proof (translation)
Establish `h : (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * β * sh G (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = algebraMap ℚ G.C (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) * β` using `y.2.1`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [mul_assoc, Units.inv_mul_cancel_left]`. Use `_ = _ := by`. Rewrite using `[h, ← mul_assoc, ← Algebra.commutes, mul_assoc]`.
-/
theorem sh_eq (G : HTGroup p) (β : G.Cˣ) (y : grp G β) :
    sh G (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = algebraMap ℚ G.C (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) *
      ((((β⁻¹ : G.Cˣ) : G.C) * (((y : G.Cˣ × ℚˣ).1⁻¹ : G.Cˣ) : G.C)) * (β : G.C)) := by
  have h : (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * β * sh G (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) =
      algebraMap ℚ G.C (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) * β := y.2.1
  calc sh G (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)
      = (((β⁻¹ : G.Cˣ) : G.C) * (((y : G.Cˣ × ℚˣ).1⁻¹ : G.Cˣ) : G.C)) *
          ((((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * β * sh G (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) := by
        simp only [mul_assoc, Units.inv_mul_cancel_left]
    _ = _ := by
        rw [h, ← mul_assoc, ← Algebra.commutes, mul_assoc]

/- English proof (translation)
The claim follows from `(Finset.single_le_sum (f := fun w => enorm ((g.2 w : Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw w) 1)).map (mulMap (G.Fw w)))) (fun _ _ => enorm_nonneg _) (Finset.mem_univ w)).trans (le_add_of_nonneg_left (enorm_nonneg _))`.
-/
theorem enorm_le_E_w (G : HTGroup p) (g : Gr G 1) (w : Fin G.m) :
    enorm ((g.2 w : Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw w) 1)).map (mulMap (G.Fw w))) ≤ E G g :=
  (Finset.single_le_sum (f := fun w => enorm ((g.2 w : Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw w) 1)).map
    (mulMap (G.Fw w)))) (fun _ _ => enorm_nonneg _) (Finset.mem_univ w)).trans
    (le_add_of_nonneg_left (enorm_nonneg _))

/- English proof (translation)
The claim follows from `le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => enorm_nonneg _)`.
-/
theorem enorm_le_E_one (G : HTGroup p) (g : Gr G 1) :
    enorm ((g.1 : Matrix (Fin 1) (Fin 1) (Qr p 1)).map (algebraMap (Qr p 1) (PadicAlgCl p))) ≤ E G g :=
  le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => enorm_nonneg _)

/- English proof (translation)
Unfold `Rw`. Rewrite using `[Matrix.map_apply, RingHom.map_rat_algebraMap, Matrix.algebraMap_matrix_apply]`. Use `split_ifs`. Rewrite using `[← IsScalarTower.algebraMap_apply]`. Simplify using the standard rewrite rules.
-/
theorem norm_Rw_alg (G : HTGroup p) (w : Fin G.m) (q : ℚ) (i j : Fin G.n) :
    ‖Rw G w (algebraMap ℚ G.C q) i j‖ ≤ ‖algebraMap ℚ (PadicAlgCl p) q‖ := by
  unfold Rw
  rw [Matrix.map_apply, RingHom.map_rat_algebraMap, Matrix.algebraMap_matrix_apply]
  split_ifs
  · rw [← IsScalarTower.algebraMap_apply]
  · simp

/- English proof (translation)
Introduce `p _ G K' f' hf β h₂`. Take `⟨-, -, -, S, hS⟩` from `hf`. Establish `hp` using `(Fact.out : p.Prime)`. Take `⟨c, hc⟩ : ∃ c : ℝ, c = ((1 : ℕ) : ℝ) * ((1 : ℕ) : ℝ) * 1 + ∑ _w : Fin G.m, (G.n : ℝ) * G.n * 1` from `⟨_, rfl⟩`. Establish `hc0 : 0 ≤ c` using `by rw [hc]; positivity`.

Establish `hEint : ∀ {k : Gr G 1}, k ∈ KHT p G.m G.n 1 G.Fw → E G k ≤ c` using `fun hk => hc ▸ E_int G hk`. Take `⟨Ms, hMs⟩ : ∃ Ms : ℝ, Ms = ∑ s ∈ S, (E G s + E G s⁻¹)` from `⟨_, rfl⟩`. Establish `hMs0 : 0 ≤ Ms` using `hMs ▸ Finset.sum_nonneg fun _ _ => add_nonneg (E_nonneg _ _) (E_nonneg _ _)`. Take `⟨B₀, hB₀⟩ : ∃ B₀ : ℝ, B₀ = E G h₂ * c * Ms * c * E G h₂⁻¹` from `⟨_, rfl⟩`. Establish `hB₀0 : 0 ≤ B₀` using `hB₀ ▸ mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (E_nonneg G h₂) hc0) hMs0) hc0) (E_nonneg G h₂⁻¹)`.

Take `⟨Cb, hCb⟩ : ∃ Cb : ℝ, Cb = ∑ w, (enorm (Rw G w ((β⁻¹ : G.Cˣ) : G.C)) + enorm (Rw G w (β : G.C)))` from `⟨_, rfl⟩`. Establish `hCb0 : 0 ≤ Cb` using `hCb ▸ Finset.sum_nonneg fun _ _ => add_nonneg (enorm_nonneg _) (enorm_nonneg _)`. Establish `hCb1 : ∀ w, enorm (Rw G w ((β⁻¹ : G.Cˣ) : G.C)) ≤ Cb` using `fun w => hCb ▸ (le_add_of_nonneg_right (enorm_nonneg _)).trans (Finset.single_le_sum (f := fun w => enorm (Rw G w ((β⁻¹ : G.Cˣ) : G.C)) + enorm (Rw G w (β : G.C))) (fun _ _ => add_nonneg (enorm_nonneg _) (enorm_nonneg _)) (Finset.mem_univ w))`. Establish `hCb2 : ∀ w, enorm (Rw G w (β : G.C)) ≤ Cb` using `fun w => hCb ▸ (le_add_of_nonneg_left (enorm_nonneg _)).trans (Finset.single_le_sum (f := fun w => enorm (Rw G w ((β⁻¹ : G.Cˣ) : G.C)) + enorm (Rw G w (β : G.C))) (fun _ _ => add_nonneg (enorm_nonneg _) (enorm_nonneg _)) (Finset.mem_univ w))`. Establish `key : ∀ y : grp G β, f' (h₂⁻¹ * toP1 G β y * h₂) ≠ 0 → E G (toP1 G β y) ≤ B₀ ∧ E G (toP1 G β y⁻¹) ≤ B₀`.

Introduce `y hy`. Take `⟨s, hs, k₁, hk₁, k₂, hk₂, he⟩` from `hS _ hy`. Establish `hX : toP1 G β y = h₂ * k₁ * s * k₂ * h₂⁻¹`. Combine the equalities or inequalities in the displayed calculation. Establish `hXi : toP1 G β y⁻¹ = h₂ * k₂⁻¹ * s⁻¹ * k₁⁻¹ * h₂⁻¹`.

Rewrite using `[map_inv, hX]`. Use `group`. Establish `hsum : ∀ t ∈ S, 0 ≤ E G t + E G t⁻¹` using `fun _ _ => add_nonneg (E_nonneg _ _) (E_nonneg _ _)`. Establish `hsM : E G s ≤ Ms` using `hMs ▸ (le_add_of_nonneg_right (E_nonneg G s⁻¹)).trans (Finset.single_le_sum (f := fun t => E G t + E G t⁻¹) hsum hs)`. Establish `hsM' : E G s⁻¹ ≤ Ms` using `hMs ▸ (le_add_of_nonneg_left (E_nonneg G s)).trans (Finset.single_le_sum (f := fun t => E G t + E G t⁻¹) hsum hs)`.

Establish `hk₁'` using `(KHT p G.m G.n 1 G.Fw).inv_mem hk₁`. Establish `hk₂'` using `(KHT p G.m G.n 1 G.Fw).inv_mem hk₂`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hX, hB₀]`. Conclude with `E_mul_le G (E_mul_le G (E_mul_le G (E_mul_le G le_rfl (hEint hk₁)) hsM) (hEint hk₂)) le_rfl`.

Rewrite using `[hXi, hB₀]`. Conclude with `E_mul_le G (E_mul_le G (E_mul_le G (E_mul_le G le_rfl (hEint hk₂')) hsM') (hEint hk₁')) le_rfl`. Take `⟨e, he⟩` from `pow_unbounded_of_one_lt B₀ (by exact_mod_cast hp.one_lt : (1 : ℝ) < p)`. Use `⟨B₀ + (G.n * G.n * B₀) * ((Cb * B₀) * Cb), e, fun y hy => ?_⟩` and prove the remaining obligations. Take `⟨hE, hEi⟩` from `key y hy`.

Establish `hextra : 0 ≤ (G.n * G.n * B₀) * ((Cb * B₀) * Cb)` using `mul_nonneg (mul_nonneg (by positivity) hB₀0) (mul_nonneg (mul_nonneg hCb0 hB₀0) hCb0)`. Establish `hs1 : ‖algebraMap ℚ (PadicAlgCl p) (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ)‖ ≤ B₀`. Rewrite using `[← formGroupToPadicPointsDegreeOne_fst_entry_eq_factor]`. Conclude with `((norm_le_enorm _ 0 0).trans (enorm_le_E_one G _)).trans hE`. Establish `hs2 : ‖algebraMap ℚ (PadicAlgCl p) ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ)⁻¹)‖ ≤ B₀`.

Establish `h` using `formGroupToPadicPointsDegreeOne_fst_entry_eq_factor G β y⁻¹`. Establish `e1 : ((((y⁻¹ : grp G β) : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) = (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ)⁻¹` using `Units.val_inv_eq_inv_val _`. Rewrite `h` using `[e1]`. Rewrite using `[← h]`. Conclude with `((norm_le_enorm _ 0 0).trans (enorm_le_E_one G _)).trans hEi`.

Use `⟨fun w a b => ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Establish `h1 : ‖((G.rho w (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) a b : G.Fw w) : PadicAlgCl p)‖ = ‖Rw G w (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) a b‖` using `rfl`. Rewrite using `[h1, ← formGroupToPadicPointsDegreeOne_snd_map_eq_rho]`. Conclude with `(((norm_le_enorm _ a b).trans (enorm_le_E_w G _ w)).trans hE).trans (le_add_of_nonneg_right hextra)`. Establish `h1 : ‖((G.rho w (sh G (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) a b : G.Fw w) : PadicAlgCl p)‖ = ‖Rw G w (sh G (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) a b‖` using `rfl`.

Rewrite using `[h1]`. Use `(norm_le_enorm _ a b).trans ?_` and prove the remaining obligations. Rewrite using `[sh_eq, Rw_mul, Rw_mul, Rw_mul]`. Establish `hA : enorm (Rw G w (algebraMap ℚ G.C (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ))) ≤ G.n * G.n * B₀` using `enorm_le_of _ _ fun i j => (norm_Rw_alg G w _ i j).trans hs1`. Establish `hY : enorm (Rw G w (((y : G.Cˣ × ℚˣ).1⁻¹ : G.Cˣ) : G.C)) ≤ B₀`.

Establish `h` using `formGroupToPadicPointsDegreeOne_snd_map_eq_rho G β y⁻¹ w`. Establish `e1 : ((((y⁻¹ : grp G β) : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = (((y : G.Cˣ × ℚˣ).1⁻¹ : G.Cˣ) : G.C)` using `rfl`. Rewrite `h` using `[e1]`. Rewrite using `[← h]`. Conclude with `(enorm_le_E_w G _ w).trans hEi`.

Establish `hYb : enorm (Rw G w ((β⁻¹ : G.Cˣ) : G.C) * Rw G w (((y : G.Cˣ × ℚˣ).1⁻¹ : G.Cˣ) : G.C)) ≤ Cb * B₀` using `(enorm_mul_le _ _).trans (mul_le_mul (hCb1 w) hY (enorm_nonneg _) hCb0)`. Establish `hYbb : enorm (Rw G w ((β⁻¹ : G.Cˣ) : G.C) * Rw G w (((y : G.Cˣ × ℚˣ).1⁻¹ : G.Cˣ) : G.C) * Rw G w (β : G.C)) ≤ Cb * B₀ * Cb` using `(enorm_mul_le _ _).trans (mul_le_mul hYb (hCb2 w) (enorm_nonneg _) (mul_nonneg hCb0 hB₀0))`. Use `((enorm_mul_le _ _).trans (mul_le_mul hA hYbb (enorm_nonneg _) (mul_nonneg (by positivity) hB₀0))).trans ?_` and prove the remaining obligations. Conclude with `le_add_of_nonneg_left hB₀0`. Take `⟨q, hq⟩ : ∃ q : ℚ, q = (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ)⁻¹ * (p : ℚ) ^ e` from `⟨_, rfl⟩`.

Use `⟨q.num, q.den, ?_, hq ▸ (Rat.num_div_den q).symm⟩` and prove the remaining obligations. Use `not_dvd_den_of_padicNorm_le_one q ?_` and prove the remaining obligations. Establish `h2 : ‖(((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ)⁻¹ : ℚ) : ℚ_[p])‖ ≤ B₀`. Rewrite using `[← norm_algebraMap_rat]`. Conclude with `hs2`.

Establish `h3 : ‖((q : ℚ) : ℚ_[p])‖ ≤ 1`. Rewrite using `[hq, Rat.cast_mul, norm_mul, Rat.cast_pow, Rat.cast_natCast, Padic.norm_p_pow, _root_.zpow_neg, zpow_natCast]`. Establish `hpe : (0 : ℝ) < (p : ℝ) ^ e` using `pow_pos (by exact_mod_cast hp.pos) e`. Rewrite using `[← div_eq_mul_inv, div_le_one hpe]`. Conclude with `h2.trans he.le`.

Rewrite `h3` using `[Padic.eq_padicNorm]`. Conclude with `h3` after adjusting the coercions.
-/
theorem bounded_of_support : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ),
    IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' → ∀ (β : G.Cˣ) (h₂ : Gr G 1), ∃ (B : ℝ) (e : ℕ),
    ∀ y : grp G β, f' (h₂⁻¹ * toP1 G β y * h₂) ≠ 0 →
      (∀ (w : Fin G.m) (a b : Fin G.n),
        ‖((G.rho w (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) a b : G.Fw w) : PadicAlgCl p)‖ ≤ B ∧
        ‖((G.rho w (sh G (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) a b : G.Fw w) : PadicAlgCl p)‖ ≤ B) ∧
      ∃ (k : ℤ) (m : ℕ), ¬ p ∣ m ∧ (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ)⁻¹ * (p : ℚ) ^ e = k / m := by
  intro p _ G K' f' hf β h₂
  obtain ⟨-, -, -, S, hS⟩ := hf
  have hp := (Fact.out : p.Prime)
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = ((1 : ℕ) : ℝ) * ((1 : ℕ) : ℝ) * 1 + ∑ _w : Fin G.m, (G.n : ℝ) * G.n * 1 :=
    ⟨_, rfl⟩
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hEint : ∀ {k : Gr G 1}, k ∈ KHT p G.m G.n 1 G.Fw → E G k ≤ c := fun hk => hc ▸ E_int G hk
  obtain ⟨Ms, hMs⟩ : ∃ Ms : ℝ, Ms = ∑ s ∈ S, (E G s + E G s⁻¹) := ⟨_, rfl⟩
  have hMs0 : 0 ≤ Ms := hMs ▸ Finset.sum_nonneg fun _ _ => add_nonneg (E_nonneg _ _) (E_nonneg _ _)
  obtain ⟨B₀, hB₀⟩ : ∃ B₀ : ℝ, B₀ = E G h₂ * c * Ms * c * E G h₂⁻¹ := ⟨_, rfl⟩
  have hB₀0 : 0 ≤ B₀ := hB₀ ▸ mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (E_nonneg G h₂) hc0) hMs0) hc0)
    (E_nonneg G h₂⁻¹)
  obtain ⟨Cb, hCb⟩ : ∃ Cb : ℝ, Cb = ∑ w, (enorm (Rw G w ((β⁻¹ : G.Cˣ) : G.C)) + enorm (Rw G w (β : G.C))) :=
    ⟨_, rfl⟩
  have hCb0 : 0 ≤ Cb := hCb ▸ Finset.sum_nonneg fun _ _ => add_nonneg (enorm_nonneg _) (enorm_nonneg _)
  have hCb1 : ∀ w, enorm (Rw G w ((β⁻¹ : G.Cˣ) : G.C)) ≤ Cb := fun w =>
    hCb ▸ (le_add_of_nonneg_right (enorm_nonneg _)).trans (Finset.single_le_sum
      (f := fun w => enorm (Rw G w ((β⁻¹ : G.Cˣ) : G.C)) + enorm (Rw G w (β : G.C)))
      (fun _ _ => add_nonneg (enorm_nonneg _) (enorm_nonneg _)) (Finset.mem_univ w))
  have hCb2 : ∀ w, enorm (Rw G w (β : G.C)) ≤ Cb := fun w =>
    hCb ▸ (le_add_of_nonneg_left (enorm_nonneg _)).trans (Finset.single_le_sum
      (f := fun w => enorm (Rw G w ((β⁻¹ : G.Cˣ) : G.C)) + enorm (Rw G w (β : G.C)))
      (fun _ _ => add_nonneg (enorm_nonneg _) (enorm_nonneg _)) (Finset.mem_univ w))
  have key : ∀ y : grp G β, f' (h₂⁻¹ * toP1 G β y * h₂) ≠ 0 →
      E G (toP1 G β y) ≤ B₀ ∧ E G (toP1 G β y⁻¹) ≤ B₀ := by
    intro y hy
    obtain ⟨s, hs, k₁, hk₁, k₂, hk₂, he⟩ := hS _ hy
    have hX : toP1 G β y = h₂ * k₁ * s * k₂ * h₂⁻¹ := by
      calc toP1 G β y = h₂ * (h₂⁻¹ * toP1 G β y * h₂) * h₂⁻¹ := by group
        _ = h₂ * (k₁ * s * k₂) * h₂⁻¹ := by rw [he]
        _ = _ := by group
    have hXi : toP1 G β y⁻¹ = h₂ * k₂⁻¹ * s⁻¹ * k₁⁻¹ * h₂⁻¹ := by
      rw [map_inv, hX]; group
    have hsum : ∀ t ∈ S, 0 ≤ E G t + E G t⁻¹ := fun _ _ => add_nonneg (E_nonneg _ _) (E_nonneg _ _)
    have hsM : E G s ≤ Ms := hMs ▸ (le_add_of_nonneg_right (E_nonneg G s⁻¹)).trans
      (Finset.single_le_sum (f := fun t => E G t + E G t⁻¹) hsum hs)
    have hsM' : E G s⁻¹ ≤ Ms := hMs ▸ (le_add_of_nonneg_left (E_nonneg G s)).trans
      (Finset.single_le_sum (f := fun t => E G t + E G t⁻¹) hsum hs)
    have hk₁' := (KHT p G.m G.n 1 G.Fw).inv_mem hk₁
    have hk₂' := (KHT p G.m G.n 1 G.Fw).inv_mem hk₂
    refine ⟨?_, ?_⟩
    · rw [hX, hB₀]
      exact E_mul_le G (E_mul_le G (E_mul_le G (E_mul_le G le_rfl (hEint hk₁)) hsM) (hEint hk₂)) le_rfl
    · rw [hXi, hB₀]
      exact E_mul_le G (E_mul_le G (E_mul_le G (E_mul_le G le_rfl (hEint hk₂')) hsM') (hEint hk₁')) le_rfl
  obtain ⟨e, he⟩ := pow_unbounded_of_one_lt B₀ (by exact_mod_cast hp.one_lt : (1 : ℝ) < p)
  refine ⟨B₀ + (G.n * G.n * B₀) * ((Cb * B₀) * Cb), e, fun y hy => ?_⟩
  obtain ⟨hE, hEi⟩ := key y hy
  have hextra : 0 ≤ (G.n * G.n * B₀) * ((Cb * B₀) * Cb) :=
    mul_nonneg (mul_nonneg (by positivity) hB₀0) (mul_nonneg (mul_nonneg hCb0 hB₀0) hCb0)

  have hs1 : ‖algebraMap ℚ (PadicAlgCl p) (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ)‖ ≤ B₀ := by
    rw [← formGroupToPadicPointsDegreeOne_fst_entry_eq_factor]
    exact ((norm_le_enorm _ 0 0).trans (enorm_le_E_one G _)).trans hE
  have hs2 : ‖algebraMap ℚ (PadicAlgCl p) ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ)⁻¹)‖ ≤ B₀ := by
    have h := formGroupToPadicPointsDegreeOne_fst_entry_eq_factor G β y⁻¹
    have e1 : ((((y⁻¹ : grp G β) : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) = (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ)⁻¹ :=
      Units.val_inv_eq_inv_val _
    rw [e1] at h
    rw [← h]
    exact ((norm_le_enorm _ 0 0).trans (enorm_le_E_one G _)).trans hEi
  refine ⟨fun w a b => ⟨?_, ?_⟩, ?_⟩
  · have h1 : ‖((G.rho w (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) a b : G.Fw w) : PadicAlgCl p)‖ =
        ‖Rw G w (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) a b‖ := rfl
    rw [h1, ← formGroupToPadicPointsDegreeOne_snd_map_eq_rho]
    exact (((norm_le_enorm _ a b).trans (enorm_le_E_w G _ w)).trans hE).trans (le_add_of_nonneg_right hextra)
  · have h1 : ‖((G.rho w (sh G (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) a b : G.Fw w) : PadicAlgCl p)‖ =
        ‖Rw G w (sh G (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) a b‖ := rfl
    rw [h1]
    refine (norm_le_enorm _ a b).trans ?_
    rw [sh_eq, Rw_mul, Rw_mul, Rw_mul]
    have hA : enorm (Rw G w (algebraMap ℚ G.C (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ))) ≤ G.n * G.n * B₀ :=
      enorm_le_of _ _ fun i j => (norm_Rw_alg G w _ i j).trans hs1
    have hY : enorm (Rw G w (((y : G.Cˣ × ℚˣ).1⁻¹ : G.Cˣ) : G.C)) ≤ B₀ := by
      have h := formGroupToPadicPointsDegreeOne_snd_map_eq_rho G β y⁻¹ w
      have e1 : ((((y⁻¹ : grp G β) : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = (((y : G.Cˣ × ℚˣ).1⁻¹ : G.Cˣ) : G.C) := rfl
      rw [e1] at h
      rw [← h]
      exact (enorm_le_E_w G _ w).trans hEi
    have hYb : enorm (Rw G w ((β⁻¹ : G.Cˣ) : G.C) * Rw G w (((y : G.Cˣ × ℚˣ).1⁻¹ : G.Cˣ) : G.C)) ≤ Cb * B₀ :=
      (enorm_mul_le _ _).trans (mul_le_mul (hCb1 w) hY (enorm_nonneg _) hCb0)
    have hYbb : enorm (Rw G w ((β⁻¹ : G.Cˣ) : G.C) * Rw G w (((y : G.Cˣ × ℚˣ).1⁻¹ : G.Cˣ) : G.C) *
        Rw G w (β : G.C)) ≤ Cb * B₀ * Cb :=
      (enorm_mul_le _ _).trans (mul_le_mul hYb (hCb2 w) (enorm_nonneg _) (mul_nonneg hCb0 hB₀0))
    refine ((enorm_mul_le _ _).trans (mul_le_mul hA hYbb (enorm_nonneg _) (mul_nonneg (by positivity) hB₀0))).trans ?_
    exact le_add_of_nonneg_left hB₀0
  · obtain ⟨q, hq⟩ : ∃ q : ℚ, q = (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ)⁻¹ * (p : ℚ) ^ e := ⟨_, rfl⟩
    refine ⟨q.num, q.den, ?_, hq ▸ (Rat.num_div_den q).symm⟩
    refine not_dvd_den_of_padicNorm_le_one q ?_
    have h2 : ‖(((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ)⁻¹ : ℚ) : ℚ_[p])‖ ≤ B₀ := by
      rw [← norm_algebraMap_rat]; exact hs2
    have h3 : ‖((q : ℚ) : ℚ_[p])‖ ≤ 1 := by
      rw [hq, Rat.cast_mul, norm_mul, Rat.cast_pow, Rat.cast_natCast, Padic.norm_p_pow, _root_.zpow_neg, zpow_natCast]
      have hpe : (0 : ℝ) < (p : ℝ) ^ e := pow_pos (by exact_mod_cast hp.pos) e
      rw [← div_eq_mul_inv, div_le_one hpe]
      exact h2.trans he.le
    rw [Padic.eq_padicNorm] at h3
    exact_mod_cast h3

end GlobalTheory.FixBound
