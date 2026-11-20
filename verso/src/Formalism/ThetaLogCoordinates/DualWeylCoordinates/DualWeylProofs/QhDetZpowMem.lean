import Formalism.ThetaLogCoordinates.DualWeylCoordinates.StatementH

noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

@[to_additive]
/- English proof (translation)
Establish `h1 : ∏ a' : Fin s, F (Fin.castLE hs a') = ∏ a ∈ (univ : Finset (Fin s)).map (Fin.castLEEmb hs), F a`. Rewrite using `[Finset.prod_map]`. Both sides reduce to the same expression. Rewrite using `[h1]`. Apply `Finset.prod_subset (Finset.subset_univ _)` to reduce the goal to its premises.

Introduce `a _ ha`. Apply `h` to reduce the goal to its premises. Assume the negation of the conclusion as `hlt`. Use `push Not at hlt`. Conclude with `ha (Finset.mem_map.2 ⟨⟨a.val, hlt⟩, Finset.mem_univ _, by ext; rfl⟩)`.
-/
lemma qh_prod_castLE {M : Type*} [CommMonoid M] {s n : ℕ} (hs : s ≤ n) (F : Fin n → M)
    (h : ∀ a : Fin n, s ≤ a.val → F a = 1) : ∏ a' : Fin s, F (Fin.castLE hs a') = ∏ a, F a := by
  have h1 : ∏ a' : Fin s, F (Fin.castLE hs a') = ∏ a ∈ (univ : Finset (Fin s)).map (Fin.castLEEmb hs), F a := by
    rw [Finset.prod_map]; rfl
  rw [h1]
  apply Finset.prod_subset (Finset.subset_univ _)
  intro a _ ha
  apply h
  by_contra hlt
  push Not at hlt
  exact ha (Finset.mem_map.2 ⟨⟨a.val, hlt⟩, Finset.mem_univ _, by ext; rfl⟩)

variable {n : ℕ} {R : Type} [CommRing R]

/- English proof (translation)
Unfold `evGLR`. Conclude with `IsLocalization.Away.lift_eq _ _ _`.
-/
lemma qh_evGLR_alg {R' : Type} [CommRing R'] [Algebra R R'] (g : GL (Fin n) R')
    (P : MvPolynomial (Fin n × Fin n) R) :
    evGLR g (algebraMap _ (GLCoord R n) P) =
      MvPolynomial.eval₂Hom (algebraMap R R') (fun ab : Fin n × Fin n => g.val ab.1 ab.2) P := by
  unfold evGLR
  exact IsLocalization.Away.lift_eq _ _ _

/- English proof (translation)
Rewrite using `[IsScalarTower.algebraMap_apply R (MvPolynomial (Fin n × Fin n) R) (GLCoord R n), qh_evGLR_alg]`. Simplify using the standard rewrite rules.
-/
lemma qh_evGLR_algR {R' : Type} [CommRing R'] [Algebra R R'] (g : GL (Fin n) R') (r : R) :
    evGLR g (algebraMap R (GLCoord R n) r) = algebraMap R R' r := by
  rw [IsScalarTower.algebraMap_apply R (MvPolynomial (Fin n × Fin n) R) (GLCoord R n), qh_evGLR_alg]
  simp

/- English proof (translation)
Establish `h1 : b.val.det = ∏ i, b.val i i` using `Matrix.det_of_isLowerTriangular _ (fun i j hij => hb i j hij)`. Establish `h2 : IsUnit (∏ i, b.val i i)` using `h1 ▸ Matrix.isUnits_det_units b`. Conclude with `(IsUnit.prod_univ_iff.1 h2) a`.
-/
lemma qh_diag_isUnit {R' : Type} [CommRing R'] (b : GL (Fin n) R')
    (hb : ∀ a c : Fin n, a < c → b.val a c = 0) (a : Fin n) : IsUnit (b.val a a) := by
  have h1 : b.val.det = ∏ i, b.val i i := Matrix.det_of_isLowerTriangular _ (fun i j hij => hb i j hij)
  have h2 : IsUnit (∏ i, b.val i i) := h1 ▸ Matrix.isUnits_det_units b
  exact (IsUnit.prod_univ_iff.1 h2) a

/- English proof (translation)
Rewrite using `[← zpow_natCast, ← zpow_natCast, ← zpow_add]`. Use `congr 1`. Use `Int.toNat_sub_toNat_neg z` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
lemma qh_zpow_split {G : Type*} [CommGroup G] (u : G) (z : ℤ) : u ^ z * u ^ (-z).toNat = u ^ z.toNat := by
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_add]
  congr 1
  have := Int.toNat_sub_toNat_neg z
  omega

/- English proof (translation)
Establish `key : ∀ (R' : Type) [CommRing R'] (u : Fin n → R'ˣ), ((∏ a, u a ^ mu a : R'ˣ) : R') * ((∏ a, u a ^ (-(mu a)).toNat : R'ˣ) : R') = ((∏ a, u a ^ (mu a).toNat : R'ˣ) : R')`. Introduce `R' _ u`. Rewrite using `[← Units.val_mul, ← Finset.prod_mul_distrib]`. Use `congr 2`. Use function extensionality and compare the values at `a`.

Conclude with `qh_zpow_split _ _`. Prove the components needed by the constructor for the conclusion. Introduce `hf R' _ _ b g u hb hu`. Establish `h` using `hf R' b g hb`. Simplify using `only [← hu] at h`.

Establish `e1 : ∏ a, (u a : R') ^ (-(mu a)).toNat = ((∏ a, u a ^ (-(mu a)).toNat : R'ˣ) : R')`. Simplify using the standard rewrite rules. Establish `e2 : ∏ a, (u a : R') ^ (mu a).toNat = ((∏ a, u a ^ (mu a).toNat : R'ˣ) : R')`. Simplify using the standard rewrite rules. Rewrite `h` using `[e1, e2, ← key R' u]`.

Apply `(Units.mul_left_inj (∏ a, u a ^ (-(mu a)).toNat : R'ˣ)).1` to reduce the goal to its premises. Rewrite using `[h]`. Expand and normalize the polynomial expressions, which then agree. Introduce `hf R' _ _ b g hb`. Establish `h` using `hf R' b g (fun a => (qh_diag_isUnit b hb a).unit) hb (fun a => rfl)`.

Use `set u : Fin n → R'ˣ := fun a => (qh_diag_isUnit b hb a).unit with hu`. Establish `hu' : ∀ a, b.val a a = (u a : R')` using `fun a => rfl`. Simplify using `only [hu']`. Establish `e1 : ∏ a, (u a : R') ^ (-(mu a)).toNat = ((∏ a, u a ^ (-(mu a)).toNat : R'ˣ) : R')`. Simplify using the standard rewrite rules.

Establish `e2 : ∏ a, (u a : R') ^ (mu a).toNat = ((∏ a, u a ^ (mu a).toNat : R'ˣ) : R')`. Simplify using the standard rewrite rules. Rewrite using `[e1, e2, ← key R' u, h]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma qh_mem_iff (mu : Fin n → ℤ) (f : GLCoord R n) :
    f ∈ inducedSections R mu ↔ ∀ (R' : Type) [CommRing R'] [Algebra R R'] (b g : GL (Fin n) R') (u : Fin n → R'ˣ),
      (∀ a c : Fin n, a < c → b.val a c = 0) → (∀ a, (u a : R') = b.val a a) →
      evGLR (b * g) f = ((∏ a, u a ^ mu a : R'ˣ) : R') * evGLR g f := by
  have key : ∀ (R' : Type) [CommRing R'] (u : Fin n → R'ˣ),
      ((∏ a, u a ^ mu a : R'ˣ) : R') * ((∏ a, u a ^ (-(mu a)).toNat : R'ˣ) : R') =
        ((∏ a, u a ^ (mu a).toNat : R'ˣ) : R') := by
    intro R' _ u
    rw [← Units.val_mul, ← Finset.prod_mul_distrib]
    congr 2
    funext a
    exact qh_zpow_split _ _
  constructor
  · intro hf R' _ _ b g u hb hu
    have h := hf R' b g hb
    simp only [← hu] at h
    have e1 : ∏ a, (u a : R') ^ (-(mu a)).toNat = ((∏ a, u a ^ (-(mu a)).toNat : R'ˣ) : R') := by
      simp
    have e2 : ∏ a, (u a : R') ^ (mu a).toNat = ((∏ a, u a ^ (mu a).toNat : R'ˣ) : R') := by
      simp
    rw [e1, e2, ← key R' u] at h
    apply (Units.mul_left_inj (∏ a, u a ^ (-(mu a)).toNat : R'ˣ)).1
    rw [h]; ring
  · intro hf R' _ _ b g hb
    have h := hf R' b g (fun a => (qh_diag_isUnit b hb a).unit) hb (fun a => rfl)
    set u : Fin n → R'ˣ := fun a => (qh_diag_isUnit b hb a).unit with hu
    have hu' : ∀ a, b.val a a = (u a : R') := fun a => rfl
    simp only [hu']
    have e1 : ∏ a, (u a : R') ^ (-(mu a)).toNat = ((∏ a, u a ^ (-(mu a)).toNat : R'ˣ) : R') := by
      simp
    have e2 : ∏ a, (u a : R') ^ (mu a).toNat = ((∏ a, u a ^ (mu a).toNat : R'ˣ) : R') := by
      simp
    rw [e1, e2, ← key R' u, h]; ring

/- English proof (translation)
Introduce `R' _ _ b g _`. Simplify using the standard rewrite rules.
-/
lemma qh_zero_mem (mu : Fin n → ℤ) : (0 : GLCoord R n) ∈ inducedSections R mu := by
  intro R' _ _ b g _; simp

/- English proof (translation)
Introduce `R' _ _ b g hb`. Rewrite using `[map_add, map_add, add_mul, mul_add, hf R' b g hb, hf' R' b g hb]`.
-/
lemma qh_add_mem {mu : Fin n → ℤ} {f f' : GLCoord R n} (hf : f ∈ inducedSections R mu) (hf' : f' ∈ inducedSections R mu) :
    f + f' ∈ inducedSections R mu := by
  intro R' _ _ b g hb
  rw [map_add, map_add, add_mul, mul_add, hf R' b g hb, hf' R' b g hb]

/- English proof (translation)
Introduce `R' _ _ b g hb`. Rewrite using `[Algebra.smul_def, map_mul, map_mul, qh_evGLR_algR, qh_evGLR_algR, mul_assoc, hf R' b g hb]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma qh_smul_mem {mu : Fin n → ℤ} (r : R) {f : GLCoord R n} (hf : f ∈ inducedSections R mu) :
    r • f ∈ inducedSections R mu := by
  intro R' _ _ b g hb
  rw [Algebra.smul_def, map_mul, map_mul, qh_evGLR_algR, qh_evGLR_algR, mul_assoc, hf R' b g hb]
  ring

/- English proof (translation)
Introduce `x hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x h => exact hS h`. Consider the case `zero => exact qh_zero_mem mu`. Consider the case `add x y _ _ hx hy => exact qh_add_mem hx hy`.

Consider the case `smul r x _ hx => exact qh_smul_mem r hx`.
-/
lemma qh_span_le {mu : Fin n → ℤ} {S : Set (GLCoord R n)} (hS : S ⊆ inducedSections R mu) :
    (Submodule.span R S : Set (GLCoord R n)) ⊆ inducedSections R mu := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x h => exact hS h
  | zero => exact qh_zero_mem mu
  | add x y _ _ hx hy => exact qh_add_mem hx hy
  | smul r x _ hx => exact qh_smul_mem r hx

/- English proof (translation)
Introduce `R' _ _ b g _`. Simplify using the standard rewrite rules.
-/
lemma qh_one_mem : (1 : GLCoord R n) ∈ inducedSections R (0 : Fin n → ℤ) := by
  intro R' _ _ b g _; simp

/- English proof (translation)
Rewrite `hf`, `hf'`, the goal using `[qh_mem_iff]`. Introduce `R' _ _ b g u hb hu`. Rewrite using `[map_mul, map_mul, hf R' b g u hb hu, hf' R' b g u hb hu]`. Simplify using `only [Pi.add_apply, zpow_add, Finset.prod_mul_distrib, Units.val_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma qh_mul_mem {mu mu' : Fin n → ℤ} {f f' : GLCoord R n} (hf : f ∈ inducedSections R mu) (hf' : f' ∈ inducedSections R mu') :
    f * f' ∈ inducedSections R (mu + mu') := by
  rw [qh_mem_iff] at hf hf' ⊢
  intro R' _ _ b g u hb hu
  rw [map_mul, map_mul, hf R' b g u hb hu, hf' R' b g u hb hu]
  simp only [Pi.add_apply, zpow_add, Finset.prod_mul_distrib, Units.val_mul]
  ring

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using qh_one_mem`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.prod_insert ha, Finset.sum_insert ha]`. Conclude with `qh_mul_mem (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))`.
-/
lemma qh_prod_mem {ι : Type*} (s : Finset ι) (f : ι → GLCoord R n) (m : ι → Fin n → ℤ)
    (h : ∀ i ∈ s, f i ∈ inducedSections R (m i)) : ∏ i ∈ s, f i ∈ inducedSections R (∑ i ∈ s, m i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using qh_one_mem
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact qh_mul_mem (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

def qhDet (R : Type) [CommRing R] (n : ℕ) : (GLCoord R n)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (genMat R n).det).unit

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma qhDet_val : ((qhDet R n : (GLCoord R n)ˣ) : GLCoord R n) = algebraMap _ _ (genMat R n).det := rfl

/- English proof (translation)
Rewrite using `[qhDet_val, qh_evGLR_alg, RingHom.map_det, genMat_map_evalR]`.
-/
lemma qh_evGLR_det {R' : Type} [CommRing R'] [Algebra R R'] (g : GL (Fin n) R') :
    evGLR g ((qhDet R n : (GLCoord R n)ˣ) : GLCoord R n) = g.val.det := by
  rw [qhDet_val, qh_evGLR_alg, RingHom.map_det, genMat_map_evalR]

/- English proof (translation)
Rewrite using `[qh_mem_iff]`. Introduce `R' _ _ b g u hb hu`. Establish `h1 : ∀ h : GL (Fin n) R', evGLR h (((qhDet R n) ^ z : (GLCoord R n)ˣ) : GLCoord R n) = (((Units.map (evGLR h : GLCoord R n →+* R').toMonoidHom (qhDet R n)) ^ z : R'ˣ) : R')`. Introduce `h`. Rewrite using `[← map_zpow]`.

Both sides reduce to the same expression. Establish `h2 : Units.map (evGLR (b * g) : GLCoord R n →+* R').toMonoidHom (qhDet R n) = (∏ a, u a) * Units.map (evGLR g : GLCoord R n →+* R').toMonoidHom (qhDet R n)`. Use `ext`. Simplify using `only [Units.coe_map, Units.val_mul, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]`. Rewrite using `[qh_evGLR_det, qh_evGLR_det, Units.val_mul, Matrix.det_mul, Matrix.det_of_isLowerTriangular _ (fun i j hij => hb i j hij)]`.

Simplify using `[hu]`. Rewrite using `[h1, h1, h2, mul_zpow, Finset.prod_zpow, Units.val_mul]`.
-/
lemma qh_det_zpow_mem (z : ℤ) : (((qhDet R n) ^ z : (GLCoord R n)ˣ) : GLCoord R n) ∈ inducedSections R (fun _ : Fin n => z) := by
  rw [qh_mem_iff]
  intro R' _ _ b g u hb hu
  have h1 : ∀ h : GL (Fin n) R', evGLR h (((qhDet R n) ^ z : (GLCoord R n)ˣ) : GLCoord R n) =
      (((Units.map (evGLR h : GLCoord R n →+* R').toMonoidHom (qhDet R n)) ^ z : R'ˣ) : R') := by
    intro h
    rw [← map_zpow]; rfl
  have h2 : Units.map (evGLR (b * g) : GLCoord R n →+* R').toMonoidHom (qhDet R n) =
      (∏ a, u a) * Units.map (evGLR g : GLCoord R n →+* R').toMonoidHom (qhDet R n) := by
    ext
    simp only [Units.coe_map, Units.val_mul, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
    rw [qh_evGLR_det, qh_evGLR_det, Units.val_mul, Matrix.det_mul,
      Matrix.det_of_isLowerTriangular _ (fun i j hij => hb i j hij)]
    simp [hu]
  rw [h1, h1, h2, mul_zpow, Finset.prod_zpow, Units.val_mul]

def qhN (R : Type) [CommRing R] {n : ℕ} (s : ℕ) (hs : s ≤ n) (J : Fin s → Fin n) : GLCoord R n :=
  algebraMap _ (GLCoord R n)
    (Matrix.det (Matrix.of fun p q : Fin s => genMat R n (Fin.castLE hs p) (J q)))

/- English proof (translation)
Rewrite using `[qhN, qh_evGLR_alg, RingHom.map_det]`. Use `congr 1`. Use extensionality with `p q`. Simplify using `[genMat]`.
-/
lemma qh_evGLR_N {R' : Type} [CommRing R'] [Algebra R R'] (g : GL (Fin n) R') (s : ℕ) (hs : s ≤ n)
    (J : Fin s → Fin n) :
    evGLR g (qhN R s hs J) = Matrix.det (Matrix.of fun p q : Fin s => g.val (Fin.castLE hs p) (J q)) := by
  rw [qhN, qh_evGLR_alg, RingHom.map_det]
  congr 1
  ext p q
  simp [genMat]

/- English proof (translation)
Rewrite using `[qh_mem_iff]`. Introduce `R' _ _ b g u hb hu`. Rewrite using `[qh_evGLR_N, qh_evGLR_N]`. Establish `h1 : (Matrix.of fun p q : Fin s => (b * g).val (Fin.castLE hs p) (J q)) = (Matrix.of fun p q : Fin s => b.val (Fin.castLE hs p) (Fin.castLE hs q)) * (Matrix.of fun p q : Fin s => g.val (Fin.castLE hs p) (J q))`. Use extensionality with `p q`.

Rewrite using `[Units.val_mul, Matrix.of_apply, Matrix.mul_apply, Matrix.mul_apply]`. Use `symm`. Apply `qh_sum_castLE hs (fun a => b.val (Fin.castLE hs p) a * g.val a (J q))` to reduce the goal to its premises. Introduce `a ha`. Rewrite using `[hb _ _ (by rw [Fin.lt_def]; simp; omega), zero_mul]`.

Establish `h2 : (Matrix.of fun p q : Fin s => b.val (Fin.castLE hs p) (Fin.castLE hs q)).det = ∏ p : Fin s, b.val (Fin.castLE hs p) (Fin.castLE hs p)` using `Matrix.det_of_isLowerTriangular _ (fun i j hij => hb _ _ (by rw [Fin.lt_def]; simpa using hij))`. Rewrite using `[h1, Matrix.det_mul, h2]`. Use `congr 1`. Simplify using `only [← hu]`. Establish `h3 : ∀ a : Fin n, ((u a ^ (if a.val < s then (1 : ℤ) else 0) : R'ˣ) : R') = if a.val < s then (u a : R') else 1`.

Apply the tactic sequence `intro a; split_ifs <;> simp`. Rewrite using `[Units.coe_prod]`. Simplify using `only [h3]`. Rewrite using `[← qh_prod_castLE hs (fun a : Fin n => if a.val < s then (u a : R') else 1) (fun a ha => if_neg (by omega))]`. Apply `Finset.prod_congr rfl` to reduce the goal to its premises.

Introduce `p _`. Simplify using the standard rewrite rules.
-/
lemma qh_N_mem (s : ℕ) (hs : s ≤ n) (J : Fin s → Fin n) :
    qhN R s hs J ∈ inducedSections R (fun a : Fin n => if a.val < s then 1 else 0) := by
  rw [qh_mem_iff]
  intro R' _ _ b g u hb hu
  rw [qh_evGLR_N, qh_evGLR_N]
  have h1 : (Matrix.of fun p q : Fin s => (b * g).val (Fin.castLE hs p) (J q)) =
      (Matrix.of fun p q : Fin s => b.val (Fin.castLE hs p) (Fin.castLE hs q)) *
        (Matrix.of fun p q : Fin s => g.val (Fin.castLE hs p) (J q)) := by
    ext p q
    rw [Units.val_mul, Matrix.of_apply, Matrix.mul_apply, Matrix.mul_apply]
    symm
    apply qh_sum_castLE hs (fun a => b.val (Fin.castLE hs p) a * g.val a (J q))
    intro a ha
    rw [hb _ _ (by rw [Fin.lt_def]; simp; omega), zero_mul]
  have h2 : (Matrix.of fun p q : Fin s => b.val (Fin.castLE hs p) (Fin.castLE hs q)).det =
      ∏ p : Fin s, b.val (Fin.castLE hs p) (Fin.castLE hs p) :=
    Matrix.det_of_isLowerTriangular _ (fun i j hij => hb _ _ (by rw [Fin.lt_def]; simpa using hij))
  rw [h1, Matrix.det_mul, h2]
  congr 1
  simp only [← hu]
  have h3 : ∀ a : Fin n, ((u a ^ (if a.val < s then (1 : ℤ) else 0) : R'ˣ) : R') =
      if a.val < s then (u a : R') else 1 := by
    intro a; split_ifs <;> simp
  rw [Units.coe_prod]
  simp only [h3]
  rw [← qh_prod_castLE hs (fun a : Fin n => if a.val < s then (u a : R') else 1)
    (fun a ha => if_neg (by omega))]
  apply Finset.prod_congr rfl
  intro p _
  simp

end Formalism.InvariantFactorPaths.ColumnFamilies
