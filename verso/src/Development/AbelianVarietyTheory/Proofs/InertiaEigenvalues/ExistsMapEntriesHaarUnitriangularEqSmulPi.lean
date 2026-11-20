import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal

noncomputable section

namespace GlobalTheory.UnipCoord

abbrev Pos (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

variable {R : Type} [CommRing R] {n : ℕ}

def mat (x : Pos n → R) : Matrix (Fin n) (Fin n) R :=
  fun i j => if h : i < j then x ⟨(i, j), h⟩ else if i = j then 1 else 0

/- English proof (translation)
Simplify using `[mat, h]`.
-/
theorem mat_lt (x : Pos n → R) {i j : Fin n} (h : i < j) : mat x i j = x ⟨(i, j), h⟩ := by
  simp [mat, h]

/- English proof (translation)
Simplify using `[mat]`.
-/
theorem mat_self (x : Pos n → R) (i : Fin n) : mat x i i = 1 := by
  simp [mat]

/- English proof (translation)
Simplify using `[mat, not_lt.2 h.le, h.ne']`.
-/
theorem mat_gt (x : Pos n → R) {i j : Fin n} (h : j < i) : mat x i j = 0 := by
  simp [mat, not_lt.2 h.le, h.ne']

/- English proof (translation)
Establish `hu : (mat x).IsUpperTriangular` using `fun i j h => mat_gt x h`. Rewrite using `[Matrix.det_of_isUpperTriangular hu]`. Simplify using `[mat_self]`.
-/
theorem det_mat (x : Pos n → R) : (mat x).det = 1 := by
  have hu : (mat x).IsUpperTriangular := fun i j h => mat_gt x h
  rw [Matrix.det_of_isUpperTriangular hu]
  simp [mat_self]

def unit (x : Pos n → R) : GL (Fin n) R :=
  ⟨mat x, (mat x).adjugate, by rw [Matrix.mul_adjugate, det_mat, one_smul],
    by rw [Matrix.adjugate_mul, det_mat, one_smul]⟩

/- English proof (translation)
The claim follows from `(GlobalTheory.SmGL.mem_unipB R).2 ⟨fun i j h => mat_gt x h, fun i => mat_self x i⟩`.
-/
theorem unit_mem (x : Pos n → R) : unit x ∈ GlobalTheory.SmGL.unipB R (Fin n) :=
  (GlobalTheory.SmGL.mem_unipB R).2 ⟨fun i j h => mat_gt x h, fun i => mat_self x i⟩

def ofCoords (x : Pos n → R) : GlobalTheory.SmGL.unipB R (Fin n) := ⟨unit x, unit_mem x⟩

def coords (u : GlobalTheory.SmGL.unipB R (Fin n)) : Pos n → R :=
  fun p => ((u : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) p.1.1 p.1.2

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem val_ofCoords (x : Pos n → R) :
    (((ofCoords x : GlobalTheory.SmGL.unipB R (Fin n)) : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = mat x := rfl

/- English proof (translation)
Use function extensionality and compare the values at `p`. Simplify using `only [coords, val_ofCoords, mat_lt x p.2]`.
-/
theorem coords_ofCoords (x : Pos n → R) : coords (ofCoords x) = x := by
  funext p
  simp only [coords, val_ofCoords, mat_lt x p.2]

/- English proof (translation)
Take `⟨h1, h2⟩` from `(GlobalTheory.SmGL.mem_unipB R).1 u.2`. Use extensionality with `i j`. Break down `lt_trichotomy i j with h | rfl | h` into its components or cases. Rewrite using `[mat_lt _ h]`. Both sides reduce to the same expression.

Rewrite using `[mat_self, h2]`. Rewrite using `[mat_gt _ h, h1 i j h]`.
-/
theorem mat_coords (u : GlobalTheory.SmGL.unipB R (Fin n)) :
    mat (coords u) = ((u : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.SmGL.mem_unipB R).1 u.2
  ext i j
  rcases lt_trichotomy i j with h | rfl | h
  · rw [mat_lt _ h]; rfl
  · rw [mat_self, h2]
  · rw [mat_gt _ h, h1 i j h]

/- English proof (translation)
The claim follows from `Subtype.ext (Units.ext (mat_coords u))`.
-/
theorem ofCoords_coords (u : GlobalTheory.SmGL.unipB R (Fin n)) : ofCoords (coords u) = u :=
  Subtype.ext (Units.ext (mat_coords u))

def equiv : GlobalTheory.SmGL.unipB R (Fin n) ≃ (Pos n → R) where
  toFun := coords
  invFun := ofCoords
  left_inv := ofCoords_coords
  right_inv := coords_ofCoords

end GlobalTheory.UnipCoord

namespace GlobalTheory.UnipCoord
variable {R : Type} [CommRing R] {n : ℕ} [TopologicalSpace R] [IsTopologicalRing R]

/- English proof (translation)
Use `continuous_pi fun i => continuous_pi fun j => ?_` and prove the remaining obligations. Distinguish the cases in `h : i < j`. Simplify using `only [mat, dif_pos h]`. Conclude with `continuous_apply _`. Simplify using `only [mat, dif_neg h]`.

Conclude with `continuous_const`.
-/
theorem continuous_mat : Continuous (mat : (Pos n → R) → Matrix (Fin n) (Fin n) R) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  by_cases h : i < j
  · simp only [mat, dif_pos h]; exact continuous_apply _
  · simp only [mat, dif_neg h]; exact continuous_const

/- English proof (translation)
The claim follows from `continuous_pi fun p => (continuous_apply _).comp ((continuous_apply _).comp ((Units.continuous_val (M := Matrix (Fin n) (Fin n) R)).comp continuous_subtype_val))`.
-/
theorem continuous_coords : Continuous (coords : GlobalTheory.SmGL.unipB R (Fin n) → Pos n → R) :=
  continuous_pi fun p => (continuous_apply _).comp ((continuous_apply _).comp
    ((Units.continuous_val (M := Matrix (Fin n) (Fin n) R)).comp continuous_subtype_val))

/- English proof (translation)
Establish `h : Continuous (fun x : Pos n → R => unit x)` using `Units.continuous_iff.2 ⟨continuous_mat, continuous_mat.matrix_adjugate⟩`. Conclude with `h.subtype_mk _`.
-/
theorem continuous_ofCoords : Continuous (ofCoords : (Pos n → R) → GlobalTheory.SmGL.unipB R (Fin n)) := by
  have h : Continuous (fun x : Pos n → R => unit x) :=
    Units.continuous_iff.2 ⟨continuous_mat, continuous_mat.matrix_adjugate⟩
  exact h.subtype_mk _

def homeo : GlobalTheory.SmGL.unipB R (Fin n) ≃ₜ (Pos n → R) where
  toEquiv := equiv
  continuous_toFun := continuous_coords
  continuous_invFun := continuous_ofCoords

end GlobalTheory.UnipCoord

namespace GlobalTheory.UnipCoord

/- English proof (translation)
Set `e` to `MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => R) p`. Establish `he` using `measurePreserving_piEquivPiSubtypeProd (fun _ : ι => μ) p`. Establish `hsk : MeasurePreserving (fun z : ({i // ¬ p i} → R) × ({i // p i} → R) => (z.1, G z.1 + z.2)) ((Measure.pi fun _ => μ).prod (Measure.pi fun _ => μ)) ((Measure.pi fun _ => μ).prod (Measure.pi fun _ => μ))` using `(MeasurePreserving.id _).skew_product (g := fun b a => G b + a) ((hG.comp measurable_fst).add measurable_snd) (Filter.Eventually.of_forall fun b => map_add_left_eq_self _ _)`. Establish `hψ : MeasurePreserving (fun z : ({i // p i} → R) × ({i // ¬ p i} → R) => (G z.2 + z.1, z.2)) ((Measure.pi fun _ => μ).prod (Measure.pi fun _ => μ)) ((Measure.pi fun _ => μ).prod (Measure.pi fun _ => μ))` using `(Measure.measurePreserving_swap.comp hsk).comp Measure.measurePreserving_swap`. Establish `hc` using `(he.symm e).comp (hψ.comp he)`.

Use `hc using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `y i`. Apply the tactic sequence `by_cases h : p i <;> simp [e, MeasurableEquiv.piEquivPiSubtypeProd, h]`.
-/
theorem measurePreserving_shear {R : Type} [AddGroup R] [MeasurableSpace R] [MeasurableAdd₂ R]
    {ι : Type} [Fintype ι] (p : ι → Prop) [DecidablePred p] (μ : Measure R) [SigmaFinite μ]
    [μ.IsAddLeftInvariant] (G : ({i // ¬ p i} → R) → ({i // p i} → R)) (hG : Measurable G) :
    MeasurePreserving (fun (y : ι → R) (i : ι) => if h : p i then G (fun j => y j) ⟨i, h⟩ + y i else y i)
      (Measure.pi fun _ => μ) (Measure.pi fun _ => μ) := by
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => R) p
  have he := measurePreserving_piEquivPiSubtypeProd (fun _ : ι => μ) p
  have hsk : MeasurePreserving (fun z : ({i // ¬ p i} → R) × ({i // p i} → R) => (z.1, G z.1 + z.2))
      ((Measure.pi fun _ => μ).prod (Measure.pi fun _ => μ))
      ((Measure.pi fun _ => μ).prod (Measure.pi fun _ => μ)) :=
    (MeasurePreserving.id _).skew_product (g := fun b a => G b + a)
      ((hG.comp measurable_fst).add measurable_snd)
      (Filter.Eventually.of_forall fun b => map_add_left_eq_self _ _)
  have hψ : MeasurePreserving (fun z : ({i // p i} → R) × ({i // ¬ p i} → R) => (G z.2 + z.1, z.2))
      ((Measure.pi fun _ => μ).prod (Measure.pi fun _ => μ))
      ((Measure.pi fun _ => μ).prod (Measure.pi fun _ => μ)) :=
    (Measure.measurePreserving_swap.comp hsk).comp Measure.measurePreserving_swap
  have hc := (he.symm e).comp (hψ.comp he)
  convert hc using 1
  funext y i
  by_cases h : p i <;> simp [e, MeasurableEquiv.piEquivPiSubtypeProd, h]

end GlobalTheory.UnipCoord

namespace GlobalTheory.UnipCoord
variable {R : Type} [CommRing R] {n : ℕ}

def rowG (x : Pos n → R) (ρ : ℕ) :
    ({q : Pos n // ¬ (q.1.1 : ℕ) = ρ} → R) → ({q : Pos n // (q.1.1 : ℕ) = ρ} → R) :=
  fun b q => x q.1 + ∑ k : Fin n, if h : q.1.1.1 < k ∧ k < q.1.1.2 then
    x ⟨(q.1.1.1, k), h.1⟩ * b ⟨⟨(k, q.1.1.2), h.2⟩, by
      show ¬ (k : ℕ) = ρ
      have h1 := Fin.lt_def.1 h.1
      have h2 := q.2
      omega⟩ else 0

/- English proof (translation)
Establish `key : ∀ k : Fin n, mat x a k * mat y k b = (if k = a then y ⟨(a, b), hab⟩ else 0) + (if k = b then x ⟨(a, b), hab⟩ else 0) + (if h : a < k ∧ k < b then x ⟨(a, k), h.1⟩ * y ⟨(k, b), h.2⟩ else 0)`. Introduce `k`. Break down `lt_trichotomy k a with h1 | rfl | h1` into its components or cases. Establish `: ¬ (a < k ∧ k < b)` using `fun h => (lt_asymm h1 h.1)`. Simplify using `[mat_gt x h1, h1.ne, (h1.trans hab).ne, this]`.

Simplify using `[mat_self, mat_lt y hab, hab.ne, lt_irrefl]`. Break down `lt_trichotomy k b with h2 | rfl | h2` into its components or cases. Simplify using `[mat_lt x h1, mat_lt y h2, h1.ne', h2.ne, h1, h2]`. Simplify using `[mat_lt x h1, mat_self, h1.ne', lt_irrefl]`. Establish `: ¬ (a < k ∧ k < b)` using `fun h => (lt_asymm h2 h.2)`.

Simplify using `[mat_gt y h2, h1.ne', h2.ne', this]`. Rewrite using `[Matrix.mul_apply, Finset.sum_congr rfl fun k _ => key k, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']`. Simplify using the standard rewrite rules.
-/
theorem mat_mul_apply_row (x y : Pos n → R) (a b : Fin n) (hab : a < b) :
    (mat x * mat y) a b = y ⟨(a, b), hab⟩ + x ⟨(a, b), hab⟩ +
      ∑ k : Fin n, if h : a < k ∧ k < b then x ⟨(a, k), h.1⟩ * y ⟨(k, b), h.2⟩ else 0 := by
  have key : ∀ k : Fin n, mat x a k * mat y k b = (if k = a then y ⟨(a, b), hab⟩ else 0) +
      (if k = b then x ⟨(a, b), hab⟩ else 0) +
      (if h : a < k ∧ k < b then x ⟨(a, k), h.1⟩ * y ⟨(k, b), h.2⟩ else 0) := by
    intro k
    rcases lt_trichotomy k a with h1 | rfl | h1
    · have : ¬ (a < k ∧ k < b) := fun h => (lt_asymm h1 h.1)
      simp [mat_gt x h1, h1.ne, (h1.trans hab).ne, this]
    · simp [mat_self, mat_lt y hab, hab.ne, lt_irrefl]
    · rcases lt_trichotomy k b with h2 | rfl | h2
      · simp [mat_lt x h1, mat_lt y h2, h1.ne', h2.ne, h1, h2]
      · simp [mat_lt x h1, mat_self, h1.ne', lt_irrefl]
      · have : ¬ (a < k ∧ k < b) := fun h => (lt_asymm h2 h.2)
        simp [mat_gt y h2, h1.ne', h2.ne', this]
  rw [Matrix.mul_apply, Finset.sum_congr rfl fun k _ => key k, Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp

/- English proof (translation)
Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single a]`. Rewrite using `[mat_self, one_mul]`. Introduce `k _ hk`. Break down `lt_or_gt_of_ne hk with h | h` into its components or cases. Rewrite using `[mat_gt x h, zero_mul]`.

Rewrite using `[mat_lt x h, hx _ rfl, zero_mul]`. Simplify using the standard rewrite rules.
-/
theorem mat_mul_apply_other (x y : Pos n → R) (a b : Fin n) (hx : ∀ p : Pos n, p.1.1 = a → x p = 0) :
    (mat x * mat y) a b = mat y a b := by
  rw [Matrix.mul_apply, Finset.sum_eq_single a]
  · rw [mat_self, one_mul]
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [mat_gt x h, zero_mul]
    · rw [mat_lt x h, hx _ rfl, zero_mul]
  · simp

/- English proof (translation)
Use function extensionality and compare the values at `q`. Take `⟨⟨a, b⟩, hab⟩` from `q`. Express the relevant statement in the definitionally equal form `(mat x * mat y) a b = _`. Distinguish the cases in `h : (a : ℕ) = ρ`. Rewrite using `[dif_pos h, mat_mul_apply_row x y a b hab]`.

Simplify using `only [rowG]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[dif_neg h, mat_mul_apply_other x y a b (fun p hp => hx p (by rw [hp]; exact h)), mat_lt y hab]`.
-/
theorem coords_mul_row (x y : Pos n → R) (ρ : ℕ) (hx : ∀ p : Pos n, ¬ (p.1.1 : ℕ) = ρ → x p = 0) :
    coords (ofCoords x * ofCoords y) = fun q =>
      if h : (q.1.1 : ℕ) = ρ then rowG x ρ (fun j => y j) ⟨q, h⟩ + y q else y q := by
  funext q
  obtain ⟨⟨a, b⟩, hab⟩ := q
  change (mat x * mat y) a b = _
  by_cases h : (a : ℕ) = ρ
  · rw [dif_pos h, mat_mul_apply_row x y a b hab]
    simp only [rowG]
    ring
  · rw [dif_neg h, mat_mul_apply_other x y a b (fun p hp => hx p (by rw [hp]; exact h)), mat_lt y hab]

end GlobalTheory.UnipCoord

namespace GlobalTheory.UnipCoord
variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [MeasurableSpace R] [BorelSpace R]
  [SecondCountableTopology R] {n : ℕ} [MeasurableSpace (GL (Fin n) R)] [BorelSpace (GL (Fin n) R)]

/- English proof (translation)
Use `measurable_pi_lambda _ fun q => ?_` and prove the remaining obligations. Use `Measurable.const_add (Finset.measurable_sum _ fun k _ => ?_) _` and prove the remaining obligations. Distinguish the cases in `h : q.1.1.1 < k ∧ k < q.1.1.2`. Simplify using `only [dif_pos h]`. Conclude with `(measurable_pi_apply _).const_mul _`.

Simplify using `only [dif_neg h]`. Conclude with `measurable_const`.
-/
theorem measurable_rowG (x : Pos n → R) (ρ : ℕ) : Measurable (rowG x ρ) := by
  refine measurable_pi_lambda _ fun q => ?_
  refine Measurable.const_add (Finset.measurable_sum _ fun k _ => ?_) _
  by_cases h : q.1.1.1 < k ∧ k < q.1.1.2
  · simp only [dif_pos h]
    exact (measurable_pi_apply _).const_mul _
  · simp only [dif_neg h]
    exact measurable_const

def coordMeasure (μR : Measure R) : Measure (GlobalTheory.SmGL.unipB R (Fin n)) :=
  Measure.map ofCoords (Measure.pi fun _ : Pos n => μR)

/- English proof (translation)
The claim follows from `continuous_ofCoords.measurable`.
-/
theorem measurable_ofCoords : Measurable (ofCoords : (Pos n → R) → GlobalTheory.SmGL.unipB R (Fin n)) :=
  continuous_ofCoords.measurable

/- English proof (translation)
The claim follows from `continuous_coords.measurable`.
-/
theorem measurable_coords : Measurable (coords : GlobalTheory.SmGL.unipB R (Fin n) → Pos n → R) :=
  continuous_coords.measurable

/- English proof (translation)
Establish `hsh` using `measurePreserving_shear (fun q : Pos n => (q.1.1 : ℕ) = ρ) μR (rowG x ρ) (measurable_rowG x ρ)`. Establish `hc : (fun y => ofCoords x * ofCoords y) = ofCoords ∘ fun (y : Pos n → R) (q : Pos n) => if h : (q.1.1 : ℕ) = ρ then rowG x ρ (fun j => y j) ⟨q, h⟩ + y q else y q`. Use function extensionality and compare the values at `y`. Rewrite using `[Function.comp_apply, ← coords_mul_row x y ρ hx, ofCoords_coords]`. Rewrite using `[coordMeasure, Measure.map_map (measurable_const_mul _) measurable_ofCoords]`.

Express the relevant statement in the definitionally equal form `Measure.map (fun y => ofCoords x * ofCoords y) _ = _`. Rewrite using `[hc, ← Measure.map_map measurable_ofCoords hsh.measurable, hsh.map_eq]`.
-/
theorem map_mul_row (μR : Measure R) [SigmaFinite μR] [μR.IsAddLeftInvariant] (x : Pos n → R) (ρ : ℕ)
    (hx : ∀ p : Pos n, ¬ (p.1.1 : ℕ) = ρ → x p = 0) :
    Measure.map (ofCoords x * ·) (coordMeasure (n := n) μR) = coordMeasure μR := by
  have hsh := measurePreserving_shear (fun q : Pos n => (q.1.1 : ℕ) = ρ) μR (rowG x ρ) (measurable_rowG x ρ)
  have hc : (fun y => ofCoords x * ofCoords y) = ofCoords ∘ fun (y : Pos n → R) (q : Pos n) =>
      if h : (q.1.1 : ℕ) = ρ then rowG x ρ (fun j => y j) ⟨q, h⟩ + y q else y q := by
    funext y
    rw [Function.comp_apply, ← coords_mul_row x y ρ hx, ofCoords_coords]
  rw [coordMeasure, Measure.map_map (measurable_const_mul _) measurable_ofCoords]
  change Measure.map (fun y => ofCoords x * ofCoords y) _ = _
  rw [hc, ← Measure.map_map measurable_ofCoords hsh.measurable, hsh.map_eq]

end GlobalTheory.UnipCoord

namespace GlobalTheory.UnipCoord
variable {R : Type} [CommRing R] {n : ℕ}

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Simplify using `only [Subgroup.coe_mul, Units.val_mul, val_ofCoords]`. Use extensionality with `i j`. Break down `lt_trichotomy i j with hij | rfl | hij` into its components or cases.

Distinguish the cases in `hi : (i : ℕ) = ρ`. Rewrite using `[mat_mul_apply_other _ _ i j (fun p hp => by simp [hp, hi]), mat_lt _ hij, mat_lt _ hij]`. Simplify using `[hi]`. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single j]`. Rewrite using `[mat_self, mul_one, mat_lt _ hij, mat_lt _ hij]`.

Simplify using `[hi]`. Introduce `k _ hk`. Break down `lt_trichotomy k j with hkj | rfl | hkj` into its components or cases. Rewrite using `[mat_lt _ hkj]`. Distinguish the cases in `hk' : (k : ℕ) = ρ`.

Break down `lt_trichotomy i k with hik | rfl | hik` into its components or cases. Rewrite using `[mat_lt _ hik]`. Establish `: (i : ℕ) < ρ` using `hk' ▸ Fin.lt_def.1 hik`. Rewrite using `[if_neg hi, hx ⟨(i, k), hik⟩ this, zero_mul]`. Conclude with `absurd hk' hi`.

Rewrite using `[mat_gt _ hik, zero_mul]`. Simplify using `[hk']`. Conclude with `absurd rfl hk`. Rewrite using `[mat_gt _ hkj, mul_zero]`. Simplify using the standard rewrite rules.

Rewrite using `[mat_self, Matrix.mul_apply, Finset.sum_eq_single i]`. Rewrite using `[mat_self, mat_self, one_mul]`. Introduce `k _ hk`. Break down `lt_or_gt_of_ne hk with h | h` into its components or cases. Rewrite using `[mat_gt _ h, zero_mul]`.

Rewrite using `[mat_gt _ h, mul_zero]`. Simplify using the standard rewrite rules. Rewrite using `[mat_gt _ hij, Matrix.mul_apply]`. Use `(Finset.sum_eq_zero fun k _ => ?_).symm` and prove the remaining obligations. Break down `lt_or_ge k i with h | h` into its components or cases.

Rewrite using `[mat_gt _ h, zero_mul]`. Rewrite using `[mat_gt _ (lt_of_lt_of_le hij h), mul_zero]`.
-/
theorem ofCoords_eq_mul (x : Pos n → R) (ρ : ℕ) (hx : ∀ p : Pos n, (p.1.1 : ℕ) < ρ → x p = 0) :
    ofCoords x = ofCoords (fun p => if (p.1.1 : ℕ) = ρ then 0 else x p) *
      ofCoords (fun p => if (p.1.1 : ℕ) = ρ then x p else 0) := by
  apply Subtype.ext; apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, val_ofCoords]
  ext i j
  rcases lt_trichotomy i j with hij | rfl | hij
  · by_cases hi : (i : ℕ) = ρ
    · rw [mat_mul_apply_other _ _ i j (fun p hp => by simp [hp, hi]), mat_lt _ hij, mat_lt _ hij]
      simp [hi]
    · rw [Matrix.mul_apply, Finset.sum_eq_single j]
      · rw [mat_self, mul_one, mat_lt _ hij, mat_lt _ hij]; simp [hi]
      · intro k _ hk
        rcases lt_trichotomy k j with hkj | rfl | hkj
        · rw [mat_lt _ hkj]
          by_cases hk' : (k : ℕ) = ρ
          · rcases lt_trichotomy i k with hik | rfl | hik
            · rw [mat_lt _ hik]
              have : (i : ℕ) < ρ := hk' ▸ Fin.lt_def.1 hik
              rw [if_neg hi, hx ⟨(i, k), hik⟩ this, zero_mul]
            · exact absurd hk' hi
            · rw [mat_gt _ hik, zero_mul]
          · simp [hk']
        · exact absurd rfl hk
        · rw [mat_gt _ hkj, mul_zero]
      · simp
  · rw [mat_self, Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [mat_self, mat_self, one_mul]
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with h | h
      · rw [mat_gt _ h, zero_mul]
      · rw [mat_gt _ h, mul_zero]
    · simp
  · rw [mat_gt _ hij, Matrix.mul_apply]
    refine (Finset.sum_eq_zero fun k _ => ?_).symm
    rcases lt_or_ge k i with h | h
    · rw [mat_gt _ h, zero_mul]
    · rw [mat_gt _ (lt_of_lt_of_le hij h), mul_zero]

variable [TopologicalSpace R] [IsTopologicalRing R] [MeasurableSpace R] [BorelSpace R]
  [SecondCountableTopology R] [MeasurableSpace (GL (Fin n) R)] [BorelSpace (GL (Fin n) R)]

/- English proof (translation)
Introduce `m`. Proceed by induction on `m with`. Consider the case `zero`. Introduce `x hx`. Conclude with `map_mul_row μR x 0 fun p _ => hx p (by simpa using p.1.1.2)`.

Consider the case `succ m ih`. Introduce `x hx`. Establish `hsplit` using `ofCoords_eq_mul x (n - (m + 1)) fun p hp => hx p (by omega)`. Establish `ha` using `ih (fun p => if (p.1.1 : ℕ) = n - (m + 1) then 0 else x p) fun p hp => by`. Distinguish the cases in `h : (p.1.1 : ℕ) = n - (m + 1)`.

Simplify using `[h]`. Simplify using `only [h, if_false]; exact hx p (by omega)`. Establish `hw` using `map_mul_row μR (fun p => if (p.1.1 : ℕ) = n - (m + 1) then x p else 0) (n - (m + 1)) fun p hp => by simp [hp]`. Rewrite using `[hsplit]`. Use `conv_lhs => rw [show (fun y => ofCoords (fun p => if (p.1.1 : ℕ) = n - (m + 1) then 0 else x p) * ofCoords (fun p => if (p.1.1 : ℕ) = n - (m + 1) then x p else 0) * y) = (ofCoords (fun p => if (p.1.1 : ℕ) = n - (m + 1) then 0 else x p) * ·) ∘ (ofCoords (fun p => if (p.1.1 : ℕ) = …`.

Use function extensionality and compare the values at `fun y => mul_assoc _ _ _]`. Rewrite using `[← Measure.map_map (measurable_const_mul _) (measurable_const_mul _), hw, ha]`.
-/
theorem map_mul_ofCoords (μR : Measure R) [SigmaFinite μR] [μR.IsAddLeftInvariant] :
    ∀ m : ℕ, ∀ x : Pos n → R, (∀ p : Pos n, (p.1.1 : ℕ) + m < n → x p = 0) →
      Measure.map (ofCoords x * ·) (coordMeasure (n := n) μR) = coordMeasure μR := by
  intro m
  induction m with
  | zero =>
    intro x hx
    exact map_mul_row μR x 0 fun p _ => hx p (by simpa using p.1.1.2)
  | succ m ih =>
    intro x hx
    have hsplit := ofCoords_eq_mul x (n - (m + 1)) fun p hp => hx p (by omega)
    have ha := ih (fun p => if (p.1.1 : ℕ) = n - (m + 1) then 0 else x p) fun p hp => by
      by_cases h : (p.1.1 : ℕ) = n - (m + 1)
      · simp [h]
      · simp only [h, if_false]; exact hx p (by omega)
    have hw := map_mul_row μR (fun p => if (p.1.1 : ℕ) = n - (m + 1) then x p else 0) (n - (m + 1))
      fun p hp => by simp [hp]
    rw [hsplit]
    conv_lhs => rw [show (fun y => ofCoords (fun p => if (p.1.1 : ℕ) = n - (m + 1) then 0 else x p) *
        ofCoords (fun p => if (p.1.1 : ℕ) = n - (m + 1) then x p else 0) * y) =
      (ofCoords (fun p => if (p.1.1 : ℕ) = n - (m + 1) then 0 else x p) * ·) ∘
        (ofCoords (fun p => if (p.1.1 : ℕ) = n - (m + 1) then x p else 0) * ·) from
      funext fun y => mul_assoc _ _ _]
    rw [← Measure.map_map (measurable_const_mul _) (measurable_const_mul _), hw, ha]

instance (μR : Measure R) [SigmaFinite μR] [μR.IsAddLeftInvariant] :
    (coordMeasure (n := n) μR).IsMulLeftInvariant := by
  refine ⟨fun u => ?_⟩
  rw [← ofCoords_coords u]
  exact map_mul_ofCoords μR n _ fun p hp => by omega

instance [T2Space R] (μR : Measure R) [IsFiniteMeasureOnCompacts μR] [SigmaFinite μR] :
    IsFiniteMeasureOnCompacts (coordMeasure (n := n) μR) := by
  refine ⟨fun K hK => ?_⟩
  rw [coordMeasure, Measure.map_apply measurable_ofCoords hK.measurableSet]
  have : ofCoords ⁻¹' K = coords '' K := Set.ext fun y => ⟨fun hy => ⟨ofCoords y, hy, coords_ofCoords y⟩,
    fun ⟨u, hu, he⟩ => by rw [Set.mem_preimage, ← he, ofCoords_coords]; exact hu⟩
  rw [this]
  exact (hK.image continuous_coords).measure_lt_top

instance (μR : Measure R) [μR.IsOpenPosMeasure] [SigmaFinite μR] :
    (coordMeasure (n := n) μR).IsOpenPosMeasure :=
  continuous_ofCoords.isOpenPosMeasure_map fun u => ⟨coords u, ofCoords_coords u⟩

end GlobalTheory.UnipCoord

open GlobalTheory.UnipCoord in

/- English proof (translation)
Introduce `R _ _ _ _ _ _ _ _ n _ _ μR _ ν _`. Use `haveI : LocallyCompactSpace (GlobalTheory.SmGL.unipB R (Fin n)) := (homeo (R := R) (n := n)).isOpenEmbedding.locallyCompactSpace`. Use `haveI : SecondCountableTopology (GlobalTheory.SmGL.unipB R (Fin n)) := (homeo (R := R) (n := n)).isInducing.secondCountableTopology`. Use `haveI : (coordMeasure (n := n) μR).IsHaarMeasure := Measure.IsHaarMeasure.mk`. Take `⟨c, hc⟩ : ∃ c : ℝ≥0∞, ν = c • coordMeasure μR` from `⟨_, Measure.isMulLeftInvariant_eq_smul ν (coordMeasure μR)⟩`.

Use `⟨c, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Measure.map coords ν = _`. Rewrite using `[hc, Measure.map_smul, coordMeasure, Measure.map_map measurable_coords measurable_ofCoords]`. Establish `: coords ∘ (ofCoords : (Pos n → R) → GlobalTheory.SmGL.unipB R (Fin n)) = id` using `funext coords_ofCoords`. Rewrite using `[this, Measure.map_id]`.
-/
theorem GlobalTheory.UnipCoord.map_coords_haar : ∀ (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R]
    [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R] (n : ℕ)
    [MeasurableSpace (GL (Fin n) R)] [BorelSpace (GL (Fin n) R)] (μR : Measure R) [μR.IsAddHaarMeasure]
    (ν : Measure (GlobalTheory.SmGL.unipB R (Fin n))) [ν.IsHaarMeasure],
    ∃ c : ℝ≥0∞, Measure.map (fun (u : GlobalTheory.SmGL.unipB R (Fin n)) (p : {p : Fin n × Fin n // p.1 < p.2}) =>
        ((u : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) p.1.1 p.1.2) ν = c • Measure.pi (fun _ => μR) := by
  intro R _ _ _ _ _ _ _ _ n _ _ μR _ ν _
  haveI : LocallyCompactSpace (GlobalTheory.SmGL.unipB R (Fin n)) :=
    (homeo (R := R) (n := n)).isOpenEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (GlobalTheory.SmGL.unipB R (Fin n)) :=
    (homeo (R := R) (n := n)).isInducing.secondCountableTopology
  haveI : (coordMeasure (n := n) μR).IsHaarMeasure := Measure.IsHaarMeasure.mk
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0∞, ν = c • coordMeasure μR :=
    ⟨_, Measure.isMulLeftInvariant_eq_smul ν (coordMeasure μR)⟩
  refine ⟨c, ?_⟩
  change Measure.map coords ν = _
  rw [hc, Measure.map_smul, coordMeasure, Measure.map_map measurable_coords measurable_ofCoords]
  have : coords ∘ (ofCoords : (Pos n → R) → GlobalTheory.SmGL.unipB R (Fin n)) = id := funext coords_ofCoords
  rw [this, Measure.map_id]
