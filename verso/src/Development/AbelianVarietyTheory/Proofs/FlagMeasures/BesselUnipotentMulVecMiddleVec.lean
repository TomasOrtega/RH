import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
import Formalism.FormalDegreeBessel.FinalG

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.YInv

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.gram_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, sum_inner, inner_sum, inner_smul_left, inner_smul_right, starRingEnd_apply, Finset.mul_sum, Finset.sum_mul]`. Use `first`. Consider the case `exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => by ring`. Consider the case `(rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => by ring)`.
-/
private theorem gram_sum_smul_eq_conjTranspose_mul_gram_mul {n r : ℕ} (w : Fin r → EuclideanSpace ℂ (Fin n))
    (U : Matrix (Fin r) (Fin r) ℂ) :
    Matrix.gram ℂ (fun a => ∑ b, U b a • w b) = Uᴴ * Matrix.gram ℂ w * U := by
  ext i j
  simp only [Matrix.gram_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, sum_inner, inner_sum,
    inner_smul_left, inner_smul_right, starRingEnd_apply, Finset.mul_sum, Finset.sum_mul]
  first
    | exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => by ring
    | (rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => by ring)

/- English proof (translation)
Unfold `gramProj`. Establish `hlin : (fun a => P.starProjection (WithLp.toLp 2 (∑ b, U b a • v b))) = fun a => ∑ b, U b a • P.starProjection (WithLp.toLp 2 (v b))`. Use function extensionality and compare the values at `a`. Simplify using `[map_sum, map_smul]`. Rewrite using `[hlin, gram_sum_smul_eq_conjTranspose_mul_gram_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, hU]`.

Simplify using the standard rewrite rules.
-/
theorem gramProj_comb {n r : ℕ} (P : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (v : Fin r → Fin n → ℂ)
    (U : Matrix (Fin r) (Fin r) ℂ) (hU : U.det = 1) :
    gramProj P (fun a => ∑ b, U b a • v b) = gramProj P v := by
  unfold gramProj
  have hlin : (fun a => P.starProjection (WithLp.toLp 2 (∑ b, U b a • v b))) =
      fun a => ∑ b, U b a • P.starProjection (WithLp.toLp 2 (v b)) := by
    funext a
    simp [map_sum, map_smul]
  rw [hlin, gram_sum_smul_eq_conjTranspose_mul_gram_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, hU]
  simp

/- English proof (translation)
Rewrite using `[EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]`. Simplify using `only [WithLp.ofLp_toLp]`. Rewrite using `[Matrix.star_mulVec, dotProduct_comm, ← dotProduct_mulVec, Matrix.mulVec_mulVec, ← Matrix.star_eq_conjTranspose, (Matrix.mem_unitaryGroup_iff').1 hκ, Matrix.one_mulVec, dotProduct_comm]`.
-/
private theorem inner_unitary_mulVec_eq_inner {n : ℕ} (κ : Matrix (Fin n) (Fin n) ℂ)
    (hκ : κ ∈ Matrix.unitaryGroup (Fin n) ℂ) (a b : Fin n → ℂ) :
    inner ℂ (WithLp.toLp 2 (κ *ᵥ a)) (WithLp.toLp 2 (κ *ᵥ b)) = inner ℂ (WithLp.toLp 2 a) (WithLp.toLp 2 b) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
  simp only [WithLp.ofLp_toLp]
  rw [Matrix.star_mulVec, dotProduct_comm, ← dotProduct_mulVec, Matrix.mulVec_mulVec,
    ← Matrix.star_eq_conjTranspose, (Matrix.mem_unitaryGroup_iff').1 hκ, Matrix.one_mulVec, dotProduct_comm]

/- English proof (translation)
Establish `hu' : κ * star κ = 1` using `(Matrix.mem_unitaryGroup_iff).1 hκ`. Establish `hproj : ∀ y : Fin n → ℂ, P.starProjection (WithLp.toLp 2 (κ *ᵥ y)) = WithLp.toLp 2 (κ *ᵥ WithLp.ofLp (Q.starProjection (WithLp.toLp 2 y)))`. Introduce `y`. Apply `Submodule.eq_starProjection_of_mem_of_inner_eq_zero` to reduce the goal to its premises. Conclude with `(h _).1 (by simpa using Q.starProjection_apply_mem (WithLp.toLp 2 y))`.

Introduce `w hw`. Establish `hw' : WithLp.toLp 2 (star κ *ᵥ WithLp.ofLp w) ∈ Q`. Use `(h _).2 ?_` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_mulVec, hu', Matrix.one_mulVec]`. Simplify using `using hw`.

Establish `hweq : w = WithLp.toLp 2 (κ *ᵥ (star κ *ᵥ WithLp.ofLp w))`. Rewrite using `[Matrix.mulVec_mulVec, hu', Matrix.one_mulVec]`. Rewrite using `[hweq, ← WithLp.toLp_sub, ← Matrix.mulVec_sub, inner_unitary_mulVec_eq_inner κ hκ]`. Establish `hz` using `Submodule.starProjection_inner_eq_zero (WithLp.toLp 2 y) _ hw'`. Simplify `hz` using `[inner_sub_left]`.

Establish `hg : Matrix.gram ℂ (fun a => Q.starProjection (WithLp.toLp 2 (v a))) = Matrix.gram ℂ (fun a => P.starProjection (WithLp.toLp 2 (κ *ᵥ v a)))`. Use extensionality with `i j`. Simplify using `only [Matrix.gram_apply]`. Rewrite using `[hproj, hproj, inner_unitary_mulVec_eq_inner κ hκ]`. Unfold `gramProj`.

Rewrite using `[hg]`.
-/
theorem gramProj_unitary {n r : ℕ} (P Q : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (v : Fin r → Fin n → ℂ)
    (κ : Matrix (Fin n) (Fin n) ℂ) (hκ : κ ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (h : ∀ p : Fin n → ℂ, WithLp.toLp 2 p ∈ Q ↔ WithLp.toLp 2 (κ *ᵥ p) ∈ P) :
    gramProj Q v = gramProj P (fun a => κ *ᵥ v a) := by
  have hu' : κ * star κ = 1 := (Matrix.mem_unitaryGroup_iff).1 hκ
  have hproj : ∀ y : Fin n → ℂ, P.starProjection (WithLp.toLp 2 (κ *ᵥ y)) =
      WithLp.toLp 2 (κ *ᵥ WithLp.ofLp (Q.starProjection (WithLp.toLp 2 y))) := by
    intro y
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    · exact (h _).1 (by simpa using Q.starProjection_apply_mem (WithLp.toLp 2 y))
    · intro w hw
      have hw' : WithLp.toLp 2 (star κ *ᵥ WithLp.ofLp w) ∈ Q := by
        refine (h _).2 ?_
        rw [Matrix.mulVec_mulVec, hu', Matrix.one_mulVec]
        simpa using hw
      have hweq : w = WithLp.toLp 2 (κ *ᵥ (star κ *ᵥ WithLp.ofLp w)) := by
        rw [Matrix.mulVec_mulVec, hu', Matrix.one_mulVec]
      rw [hweq, ← WithLp.toLp_sub, ← Matrix.mulVec_sub, inner_unitary_mulVec_eq_inner κ hκ]
      have hz := Submodule.starProjection_inner_eq_zero (WithLp.toLp 2 y) _ hw'
      simpa [inner_sub_left] using hz
  have hg : Matrix.gram ℂ (fun a => Q.starProjection (WithLp.toLp 2 (v a))) =
      Matrix.gram ℂ (fun a => P.starProjection (WithLp.toLp 2 (κ *ᵥ v a))) := by
    ext i j
    simp only [Matrix.gram_apply]
    rw [hproj, hproj, inner_unitary_mulVec_eq_inner κ hκ]
  unfold gramProj
  rw [hg]

/- English proof (translation)
Establish `h` using `congrArg Matrix.det (hpkFacts k r).2.1`. Rewrite `h` using `[Matrix.det_mul, Matrix.det_one]`. Conclude with `⟨⟨_, _, h, h⟩, rfl⟩`.
-/
private theorem isUnit_det_of_mem_UWset (k r : ℕ) : IsUnit (Hpk k r).det := by
  have h := congrArg Matrix.det (hpkFacts k r).2.1
  rw [Matrix.det_mul, Matrix.det_one] at h
  exact ⟨⟨_, _, h, h⟩, rfl⟩

variable {k r : ℕ}

/- English proof (translation)
The claim follows from `((uHGroup _ (Hpk k r) (isUnit_det_of_mem_UWset k r)).2.2 g hg).1`.
-/
theorem det_unit {g : Mat k r} (hg : g ∈ GG k r) : IsUnit g.det :=
  ((uHGroup _ (Hpk k r) (isUnit_det_of_mem_UWset k r)).2.2 g hg).1

/- English proof (translation)
The claim follows from `(uHGroup _ (Hpk k r) (isUnit_det_of_mem_UWset k r)).2.1 g hg h hh`.
-/
theorem mul_mem {g h : Mat k r} (hg : g ∈ GG k r) (hh : h ∈ GG k r) : g * h ∈ GG k r :=
  (uHGroup _ (Hpk k r) (isUnit_det_of_mem_UWset k r)).2.1 g hg h hh

/- English proof (translation)
Establish `hU : gᴴ * Hpk k r * g = Hpk k r` using `hg`. Unfold `Formalism.QuantumDeterminants.herm`. Rewrite using `[Matrix.star_mulVec, ← dotProduct_mulVec]`. Simplify using `only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hU]`.
-/
theorem herm_mul {g : Mat k r} (hg : g ∈ GG k r) (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (g *ᵥ v) (g *ᵥ w) = herm (Hpk k r) v w := by
  have hU : gᴴ * Hpk k r * g = Hpk k r := hg
  unfold Formalism.QuantumDeterminants.herm
  rw [Matrix.star_mulVec, ← dotProduct_mulVec]
  simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hU]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, bvec, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]`. Distinguish the cases in `hi : i.val < r`. Rewrite using `[Finset.sum_eq_single ⟨i.val, hi⟩]`. Establish `hii : i = eI k r ⟨i.val, hi⟩` using `Fin.ext rfl`.

Simplify using `[← hii]`. Introduce `b _ hb`. Establish `hne : i ≠ eI k r b`. Introduce `e`. Apply `hb` to reduce the goal to its premises.

Apply `Fin.ext` to reduce the goal to its premises. Use `show b.val = i.val`. Rewrite using `[e]`. Both sides reduce to the same expression. Simplify using `[hne]`.

Simplify using the standard rewrite rules. Rewrite using `[hv i (not_lt.mp hi)]`. Use `(Finset.sum_eq_zero fun b _ => ?_).symm` and prove the remaining obligations. Establish `hne : i ≠ eI k r b`. Introduce `e`.

Apply `hi` to reduce the goal to its premises. Rewrite using `[e]`. Conclude with `b.isLt`. Simplify using `[hne]`.
-/
theorem eq_sum_of_zero (v : Fin (2 * r + k + 1) → ℂ) (hv : ∀ i : Fin (2 * r + k + 1), r ≤ i.val → v i = 0) :
    v = ∑ b : Fin r, v (eI k r b) • bvec (eI k r b) := by
  funext i
  simp only [Finset.sum_apply, Pi.smul_apply, bvec, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  by_cases hi : i.val < r
  · rw [Finset.sum_eq_single ⟨i.val, hi⟩]
    · have hii : i = eI k r ⟨i.val, hi⟩ := Fin.ext rfl
      simp [← hii]
    · intro b _ hb
      have hne : i ≠ eI k r b := by
        intro e
        apply hb
        apply Fin.ext
        show b.val = i.val
        rw [e]
        rfl
      simp [hne]
    · simp
  · rw [hv i (not_lt.mp hi)]
    refine (Finset.sum_eq_zero fun b _ => ?_).symm
    have hne : i ≠ eI k r b := by
      intro e
      apply hi
      rw [e]
      exact b.isLt
    simp [hne]

/- English proof (translation)
Establish `hc : n *ᵥ bvec (eI k r a) = fun i => n i (eI k r a)`. Use function extensionality and compare the values at `i`. Simplify using `[bvec, Matrix.mulVec, dotProduct, Pi.single_apply]`. Rewrite using `[hc]`. Use `eq_sum_of_zero _ fun i hi => ?_` and prove the remaining obligations.

Establish `hle : (eI k r a).val ≤ i.val` using `le_of_lt (lt_of_lt_of_le a.isLt hi)`. Rewrite using `[hn.2.1 a i hle]`. Establish `hne : i ≠ eI k r a`. Introduce `e`. Rewrite `hi` using `[e]`.

Conclude with `absurd a.isLt (not_lt.mpr hi)`. Simplify using `[hne]`.
-/
theorem N_e {n : Mat k r} (hn : n ∈ Nset k r) (a : Fin r) :
    n *ᵥ bvec (eI k r a) = ∑ b : Fin r, n (eI k r b) (eI k r a) • bvec (eI k r b) := by
  have hc : n *ᵥ bvec (eI k r a) = fun i => n i (eI k r a) := by
    funext i
    simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [hc]
  refine eq_sum_of_zero _ fun i hi => ?_
  have hle : (eI k r a).val ≤ i.val := le_of_lt (lt_of_lt_of_le a.isLt hi)
  rw [hn.2.1 a i hle]
  have hne : i ≠ eI k r a := by
    intro e
    rw [e] at hi
    exact absurd a.isLt (not_lt.mpr hi)
  simp [hne]

/- English proof (translation)
Establish `hent : ∀ b a : Fin r, a ≤ b → n (eI k r b) (eI k r a) = if b = a then 1 else 0`. Introduce `b a hab`. Rewrite using `[hn.2.1 a (eI k r b) hab]`. Distinguish the cases in `e : b = a`. Substitute `e` using the available equality.

Simplify using the standard rewrite rules. Establish `hne : eI k r b ≠ eI k r a`. Introduce `h'`. Establish `hv` using `congrArg Fin.val h'`. Conclude with `e (Fin.ext hv)`.

Simplify using `[hne, e]`. Rewrite using `[Matrix.det_of_upperTriangular]`. Use `Finset.prod_eq_one fun b _ => ?_` and prove the remaining obligations. Simplify using `[hent b b le_rfl]`. Introduce `b a hab`.

Establish `hba : b ≠ a` using `ne_of_gt hab`. Simplify using `[hent b a (le_of_lt hab), hba]`.
-/
theorem N_det {n : Mat k r} (hn : n ∈ Nset k r) :
    (Matrix.of fun b a : Fin r => n (eI k r b) (eI k r a)).det = 1 := by
  have hent : ∀ b a : Fin r, a ≤ b → n (eI k r b) (eI k r a) = if b = a then 1 else 0 := by
    intro b a hab
    rw [hn.2.1 a (eI k r b) hab]
    by_cases e : b = a
    · subst e
      simp
    · have hne : eI k r b ≠ eI k r a := by
        intro h'
        have hv := congrArg Fin.val h'
        exact e (Fin.ext hv)
      simp [hne, e]
  rw [Matrix.det_of_upperTriangular]
  · refine Finset.prod_eq_one fun b _ => ?_
    simp [hent b b le_rfl]
  · intro b a hab
    have hba : b ≠ a := ne_of_gt hab
    simp [hent b a (le_of_lt hab), hba]

/- English proof (translation)
Establish `hfix : ∀ i : Fin (2 * r + k + 1), r ≤ i.val → (n *ᵥ z) i = z i`. Introduce `i hi`. Establish `hterm : ∀ j, n i j * z j = if j = i then z i else 0`. Introduce `j`. Distinguish the cases in `hj : r ≤ j.val ∧ j.val ≤ r + k`.

Rewrite using `[hn.2.2 i j hj.1 hj.2 hi]`. Distinguish the cases in `e : j = i`. Substitute `e` using the available equality. Simplify using the standard rewrite rules. Simplify using `[e, Ne.symm e]`.

Establish `hz0 : z j = 0` using `hz j (by omega)`. Rewrite using `[hz0, mul_zero]`. Distinguish the cases in `e : j = i`. Substitute `e` using the available equality. Simplify using `[hz0]`.

Simplify using `[e]`. Simplify using `only [Matrix.mulVec, dotProduct, hterm]`. Simplify using the standard rewrite rules. Use `⟨fun b => (n *ᵥ z - z) (eI k r b), ?_⟩` and prove the remaining obligations. Establish `hs` using `eq_sum_of_zero (k := k) (n *ᵥ z - z) (fun i hi => by simp [hfix i hi])`.

Use `show n *ᵥ z = z + ∑ b : Fin r, (n *ᵥ z - z) (eI k r b) • bvec (eI k r b)`. Rewrite using `[← hs]`. Normalize the expressions using the abelian group laws.
-/
theorem besselUnipotent_mulVec_middle_vec {n : Mat k r} (hn : n ∈ Nset k r) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) :
    ∃ c : Fin r → ℂ, n *ᵥ z = z + ∑ b : Fin r, c b • bvec (eI k r b) := by
  have hfix : ∀ i : Fin (2 * r + k + 1), r ≤ i.val → (n *ᵥ z) i = z i := by
    intro i hi
    have hterm : ∀ j, n i j * z j = if j = i then z i else 0 := by
      intro j
      by_cases hj : r ≤ j.val ∧ j.val ≤ r + k
      · rw [hn.2.2 i j hj.1 hj.2 hi]
        by_cases e : j = i
        · subst e
          simp
        · simp [e, Ne.symm e]
      · have hz0 : z j = 0 := hz j (by omega)
        rw [hz0, mul_zero]
        by_cases e : j = i
        · subst e
          simp [hz0]
        · simp [e]
    simp only [Matrix.mulVec, dotProduct, hterm]
    simp
  refine ⟨fun b => (n *ᵥ z - z) (eI k r b), ?_⟩
  have hs := eq_sum_of_zero (k := k) (n *ᵥ z - z) (fun i hi => by simp [hfix i hi])
  show n *ᵥ z = z + ∑ b : Fin r, (n *ᵥ z - z) (eI k r b) • bvec (eI k r b)
  rw [← hs]
  abel

/- English proof (translation)
Unfold `Formalism.QuantumDeterminants.herm at hu hv ⊢`. Rewrite using `[Matrix.mulVec_add, Matrix.mulVec_sum, star_add, add_dotProduct, hu, zero_add, star_sum, sum_dotProduct]`. Use `Finset.sum_eq_zero fun b _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_smul, star_smul, smul_dotProduct, hv b, smul_zero]`.
-/
theorem herm_comb (w u : Fin (2 * r + k + 1) → ℂ) (M : Mat k r) (c : Fin r → ℂ) (v : Fin r → Fin (2 * r + k + 1) → ℂ)
    (hu : herm (Hpk k r) w (M *ᵥ u) = 0) (hv : ∀ b, herm (Hpk k r) w (M *ᵥ v b) = 0) :
    herm (Hpk k r) w (M *ᵥ (u + ∑ b, c b • v b)) = 0 := by
  unfold Formalism.QuantumDeterminants.herm at hu hv ⊢
  rw [Matrix.mulVec_add, Matrix.mulVec_sum, star_add, add_dotProduct, hu, zero_add, star_sum, sum_dotProduct]
  refine Finset.sum_eq_zero fun b _ => ?_
  rw [Matrix.mulVec_smul, star_smul, smul_dotProduct, hv b, smul_zero]

/- English proof (translation)
Establish `he : ∀ b : Fin r, herm (Hpk k r) w (M *ᵥ bvec (eI k r b)) = 0`. Introduce `b`. Establish `hb` using `h (Fin.castSucc b)`. Simplify `hb` using `[Formalism.QuantumDeterminants.fvec, b.isLt]`. Distinguish the cases in `ha : a.val < r`.

Establish `hfa : fvec k r z a = bvec (eI k r ⟨a.val, ha⟩)` using `by simp [Formalism.QuantumDeterminants.fvec, ha]`. Rewrite using `[hfa, N_e hn]`. Establish `hc` using `herm_comb w 0 M (fun b => n (eI k r b) (eI k r ⟨a.val, ha⟩)) (fun b => bvec (eI k r b)) (by simp [Formalism.QuantumDeterminants.herm]) he`. Simplify using `using hc`. Establish `hfa : fvec k r z a = z` using `by simp [Formalism.QuantumDeterminants.fvec, ha]`.

Take `⟨c, hc⟩` from `besselUnipotent_mulVec_middle_vec hn hz`. Rewrite using `[hfa, hc]`. Establish `hz'` using `h (Fin.last r)`. Rewrite `hz'` using `[show fvec k r z (Fin.last r) = z by simp [Formalism.QuantumDeterminants.fvec]]`. Conclude with `herm_comb w z M c (fun b => bvec (eI k r b)) hz' he`.
-/
theorem orth_N {n : Mat k r} (hn : n ∈ Nset k r) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z)
    (w : Fin (2 * r + k + 1) → ℂ) (M : Mat k r) (h : ∀ a, herm (Hpk k r) w (M *ᵥ fvec k r z a) = 0)
    (a : Fin (r + 1)) : herm (Hpk k r) w (M *ᵥ (n *ᵥ fvec k r z a)) = 0 := by
  have he : ∀ b : Fin r, herm (Hpk k r) w (M *ᵥ bvec (eI k r b)) = 0 := by
    intro b
    have hb := h (Fin.castSucc b)
    simpa [Formalism.QuantumDeterminants.fvec, b.isLt] using hb
  by_cases ha : a.val < r
  · have hfa : fvec k r z a = bvec (eI k r ⟨a.val, ha⟩) := by simp [Formalism.QuantumDeterminants.fvec, ha]
    rw [hfa, N_e hn]
    have hc := herm_comb w 0 M (fun b => n (eI k r b) (eI k r ⟨a.val, ha⟩)) (fun b => bvec (eI k r b))
      (by simp [Formalism.QuantumDeterminants.herm]) he
    simpa using hc
  · have hfa : fvec k r z a = z := by simp [Formalism.QuantumDeterminants.fvec, ha]
    obtain ⟨c, hc⟩ := besselUnipotent_mulVec_middle_vec hn hz
    rw [hfa, hc]
    have hz' := h (Fin.last r)
    rw [show fvec k r z (Fin.last r) = z by simp [Formalism.QuantumDeterminants.fvec]] at hz'
    exact herm_comb w z M c (fun b => bvec (eI k r b)) hz' he

/- English proof (translation)
Establish `hle : Xsp k r ≤ (Xsp k r).comap (Matrix.toLin' n)`. Unfold `GlobalTheory.Amp.Xsp`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨a, rfl⟩`. Simplify using `only [SetLike.mem_coe, Submodule.mem_comap, Matrix.toLin'_apply]`.

Rewrite using `[N_e hn a]`. Conclude with `Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)`. Simplify `hle hv` using `[Matrix.toLin'_apply]`.
-/
theorem N_X {n : Mat k r} (hn : n ∈ Nset k r) {v : Fin (2 * r + k + 1) → ℂ} (hv : v ∈ Xsp k r) :
    n *ᵥ v ∈ Xsp k r := by
  have hle : Xsp k r ≤ (Xsp k r).comap (Matrix.toLin' n) := by
    unfold GlobalTheory.Amp.Xsp
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, Matrix.toLin'_apply]
    rw [N_e hn a]
    exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
  simpa [Matrix.toLin'_apply] using hle hv

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
private theorem mem_Hcom_iff_herm_fvec_eq_zero {z z' : Fin (2 * r + k + 1) → ℂ} {γ : Mat k r} {w : Fin (2 * r + k + 1) → ℂ} :
    w ∈ Hcom k r z z' γ ↔ ∀ a : Fin (r + 1),
      herm (Hpk k r) w (fvec k r z' a) = 0 ∧ herm (Hpk k r) w (γ⁻¹ *ᵥ fvec k r z a) = 0 := Iff.rfl

/- English proof (translation)
Establish `u₂` using `det_unit h₂.1`. Establish `u₁` using `det_unit h₁.1`. Establish `hi₂ : n₂⁻¹ ∈ Nset k r` using `(nSubgroup k r).2.2 n₂ h₂`. Establish `key : ∀ x, herm (Hpk k r) (n₂ *ᵥ w) x = herm (Hpk k r) w (n₂⁻¹ *ᵥ x)`. Introduce `x`.

Rewrite using `[← herm_mul h₂.1 w (n₂⁻¹ *ᵥ x), Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ u₂, Matrix.one_mulVec]`. Rewrite `hw`, the goal using `[mem_Hcom_iff_herm_fvec_eq_zero]`. Introduce `a`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[key]`.

Establish `h1` using `orth_N hi₂ hz' w 1 (fun b => by simpa using (hw b).1) a`. Simplify using `using h1`. Rewrite using `[key]`. Establish `h3 : ∀ b, herm (Hpk k r) w ((n₂⁻¹ * γ⁻¹ * n₁⁻¹) *ᵥ fvec k r z b) = 0`. Introduce `b`.

Establish `h4` using `(hw b).2`. Simplify using `only [Matrix.mul_inv_rev, Matrix.mul_assoc] at h4 ⊢`. Conclude with `h4`. Establish `h5` using `orth_N h₁ hz w (n₂⁻¹ * γ⁻¹ * n₁⁻¹) h3 a`. Simplify using `only [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ u₁, Matrix.mul_one] at h5 ⊢`.

Conclude with `h5`.
-/
theorem N_H {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z') {γ n₁ n₂ : Mat k r}
    (h₁ : n₁ ∈ Nset k r) (h₂ : n₂ ∈ Nset k r) {w : Fin (2 * r + k + 1) → ℂ}
    (hw : w ∈ Hcom k r z z' (n₁ * γ * n₂)) : n₂ *ᵥ w ∈ Hcom k r z z' γ := by
  have u₂ := det_unit h₂.1
  have u₁ := det_unit h₁.1
  have hi₂ : n₂⁻¹ ∈ Nset k r := (nSubgroup k r).2.2 n₂ h₂
  have key : ∀ x, herm (Hpk k r) (n₂ *ᵥ w) x = herm (Hpk k r) w (n₂⁻¹ *ᵥ x) := by
    intro x
    rw [← herm_mul h₂.1 w (n₂⁻¹ *ᵥ x), Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ u₂, Matrix.one_mulVec]
  rw [mem_Hcom_iff_herm_fvec_eq_zero] at hw ⊢
  intro a
  refine ⟨?_, ?_⟩
  · rw [key]
    have h1 := orth_N hi₂ hz' w 1 (fun b => by simpa using (hw b).1) a
    simpa using h1
  · rw [key]
    have h3 : ∀ b, herm (Hpk k r) w ((n₂⁻¹ * γ⁻¹ * n₁⁻¹) *ᵥ fvec k r z b) = 0 := by
      intro b
      have h4 := (hw b).2
      simp only [Matrix.mul_inv_rev, Matrix.mul_assoc] at h4 ⊢
      exact h4
    have h5 := orth_N h₁ hz w (n₂⁻¹ * γ⁻¹ * n₁⁻¹) h3 a
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ u₁, Matrix.mul_one] at h5 ⊢
    exact h5

/- English proof (translation)
Take `⟨y, hy, x, hx, rfl⟩` from `Submodule.mem_sup.1 hw`. Rewrite using `[Matrix.mulVec_add]`. Conclude with `Submodule.add_mem_sup (N_H hz hz' h₁ h₂ hy) (N_X h₂ hx)`.
-/
theorem N_sup {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z') {γ n₁ n₂ : Mat k r}
    (h₁ : n₁ ∈ Nset k r) (h₂ : n₂ ∈ Nset k r) {w : Fin (2 * r + k + 1) → ℂ}
    (hw : w ∈ Hcom k r z z' (n₁ * γ * n₂) ⊔ Xsp k r) : n₂ *ᵥ w ∈ Hcom k r z z' γ ⊔ Xsp k r := by
  obtain ⟨y, hy, x, hx, rfl⟩ := Submodule.mem_sup.1 hw
  rw [Matrix.mulVec_add]
  exact Submodule.add_mem_sup (N_H hz hz' h₁ h₂ hy) (N_X h₂ hx)

/- English proof (translation)
Simplify using `[GlobalTheory.Amp.Ppos, Matrix.sub_mulVec]`.
-/
theorem mem_Ppos (z z' : Fin (2 * r + k + 1) → ℂ) (γ x : Mat k r) (p : EuclideanSpace ℂ (Fin (2 * r + k + 1))) :
    p ∈ Ppos k r z z' γ x ↔ (Hpk k r - 1) *ᵥ WithLp.ofLp p = 0 ∧
      x *ᵥ WithLp.ofLp p ∈ Hcom k r z z' γ ⊔ Xsp k r := by
  simp [GlobalTheory.Amp.Ppos, Matrix.sub_mulVec]

/- English proof (translation)
Establish `u₁` using `det_unit h₁.1`. Establish `u₂` using `det_unit h₂.1`. Use extensionality with `p`. Rewrite using `[mem_Ppos, mem_Ppos, ← Matrix.mulVec_mulVec]`. Use `and_congr_right fun _ => ⟨fun h => N_sup hz hz' h₁ h₂ h, fun h => ?_⟩` and prove the remaining obligations.

Establish `hi₁` using `(nSubgroup k r).2.2 n₁ h₁`. Establish `hi₂` using `(nSubgroup k r).2.2 n₂ h₂`. Establish `e : n₁⁻¹ * (n₁ * γ * n₂) * n₂⁻¹ = γ`. Simplify using `only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ u₂, Matrix.mul_one]`. Rewrite using `[← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ u₁, Matrix.one_mul]`.

Rewrite `h` using `[← e]`. Establish `h6` using `N_sup hz hz' hi₁ hi₂ h`. Simplify using `only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ u₂, Matrix.one_mul] at h6`. Conclude with `h6`.
-/
theorem Ppos_N {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z') {γ n₁ n₂ : Mat k r}
    (h₁ : n₁ ∈ Nset k r) (h₂ : n₂ ∈ Nset k r) (x : Mat k r) :
    Ppos k r z z' (n₁ * γ * n₂) x = Ppos k r z z' γ (n₂ * x) := by
  have u₁ := det_unit h₁.1
  have u₂ := det_unit h₂.1
  ext p
  rw [mem_Ppos, mem_Ppos, ← Matrix.mulVec_mulVec]
  refine and_congr_right fun _ => ⟨fun h => N_sup hz hz' h₁ h₂ h, fun h => ?_⟩
  have hi₁ := (nSubgroup k r).2.2 n₁ h₁
  have hi₂ := (nSubgroup k r).2.2 n₂ h₂
  have e : n₁⁻¹ * (n₁ * γ * n₂) * n₂⁻¹ = γ := by
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ u₂, Matrix.mul_one]
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ u₁, Matrix.one_mul]
  rw [← e] at h
  have h6 := N_sup hz hz' hi₁ hi₂ h
  simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ u₂, Matrix.one_mul] at h6
  exact h6

/- English proof (translation)
Establish `h1 : (1 : Mat k r) ∈ UWset k r z`. Simplify using `only [Formalism.QuantumDeterminants.UWset, Set.mem_setOf_eq]`. Conclude with `⟨(uHGroup _ (Hpk k r) (isUnit_det_of_mem_UWset k r)).1, fun a => ⟨Matrix.one_mulVec _, Matrix.one_mulVec _⟩, Matrix.one_mulVec _⟩`. Simplify using `only [Formalism.QuantumDeterminants.Sset, Set.mem_setOf_eq]`. Conclude with `⟨1, h1, n, hn, (Matrix.one_mul n).symm⟩`.
-/
theorem N_sub_S (z : Fin (2 * r + k + 1) → ℂ) {n : Mat k r} (hn : n ∈ Nset k r) : n ∈ Sset k r z := by
  have h1 : (1 : Mat k r) ∈ UWset k r z := by
    simp only [Formalism.QuantumDeterminants.UWset, Set.mem_setOf_eq]
    exact ⟨(uHGroup _ (Hpk k r) (isUnit_det_of_mem_UWset k r)).1, fun a => ⟨Matrix.one_mulVec _, Matrix.one_mulVec _⟩,
      Matrix.one_mulVec _⟩
  simp only [Formalism.QuantumDeterminants.Sset, Set.mem_setOf_eq]
  exact ⟨1, h1, n, hn, (Matrix.one_mul n).symm⟩

/- English proof (translation)
Establish `hi₁ : n₁⁻¹ ∈ Nset k r` using `(nSubgroup k r).2.2 n₁ h₁`. Establish `hDr : Dr k r z z' (n₁ * γ * n₂) = Dr k r z z' γ`. Unfold `GlobalTheory.Amp.Dr`. Rewrite using `[dInv k r z z' hz hz' n₁ (N_sub_S z h₁) n₂ (N_sub_S z' h₂)]`. Unfold `GlobalTheory.Amp.Yv`.

Rewrite using `[hDr, Ppos_N hz hz' h₁ h₂ x]`. Use `congr 1`. Establish `hv : (fun a : Fin r => x⁻¹ *ᵥ ((n₁ * γ * n₂)⁻¹ *ᵥ bvec (eI k r a))) = fun a => ∑ b : Fin r, (Matrix.of fun b a : Fin r => n₁⁻¹ (eI k r b) (eI k r a)) b a • ((n₂ * x)⁻¹ *ᵥ (γ⁻¹ *ᵥ bvec (eI k r b)))`. Use function extensionality and compare the values at `a`. Simplify using `only [Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec, N_e hi₁ a, Matrix.mulVec_sum, Matrix.mulVec_smul, Matrix.of_apply]`.

Rewrite using `[hv, gramProj_comb _ _ _ (N_det hi₁)]`.
-/
theorem Yv_N {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z') (γ : Mat k r) {n₁ n₂ : Mat k r}
    (h₁ : n₁ ∈ Nset k r) (h₂ : n₂ ∈ Nset k r) (x : Mat k r) :
    Yv k r z z' (n₁ * γ * n₂) x = Yv k r z z' γ (n₂ * x) := by
  have hi₁ : n₁⁻¹ ∈ Nset k r := (nSubgroup k r).2.2 n₁ h₁
  have hDr : Dr k r z z' (n₁ * γ * n₂) = Dr k r z z' γ := by
    unfold GlobalTheory.Amp.Dr
    rw [dInv k r z z' hz hz' n₁ (N_sub_S z h₁) n₂ (N_sub_S z' h₂)]
  unfold GlobalTheory.Amp.Yv
  rw [hDr, Ppos_N hz hz' h₁ h₂ x]
  congr 1
  have hv : (fun a : Fin r => x⁻¹ *ᵥ ((n₁ * γ * n₂)⁻¹ *ᵥ bvec (eI k r a))) =
      fun a => ∑ b : Fin r, (Matrix.of fun b a : Fin r => n₁⁻¹ (eI k r b) (eI k r a)) b a •
        ((n₂ * x)⁻¹ *ᵥ (γ⁻¹ *ᵥ bvec (eI k r b))) := by
    funext a
    simp only [Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec, N_e hi₁ a, Matrix.mulVec_sum, Matrix.mulVec_smul,
      Matrix.of_apply]
  rw [hv, gramProj_comb _ _ _ (N_det hi₁)]

/- English proof (translation)
Establish `hu : star κ * κ = 1` using `(Matrix.mem_unitaryGroup_iff').1 hκ`. Establish `hu' : κ * star κ = 1` using `(Matrix.mem_unitaryGroup_iff).1 hκ`. Establish `hinv : κ⁻¹ = star κ` using `Matrix.inv_eq_left_inv hu`. Establish `hH : Hpk k r * κ = κ * Hpk k r`. Establish `h0 : κᴴ * Hpk k r * κ = Hpk k r` using `hG`.

Rewrite `h0` using `[← Matrix.star_eq_conjTranspose]`. Combine the equalities or inequalities in the displayed calculation. Establish `hc : (Hpk k r - 1) * κ = κ * (Hpk k r - 1)`. Rewrite using `[Matrix.sub_mul, Matrix.mul_sub, hH, Matrix.one_mul, Matrix.mul_one]`. Establish `hQ : ∀ p : Fin (2 * r + k + 1) → ℂ, WithLp.toLp 2 p ∈ Ppos k r z z' γ (x * κ) ↔ WithLp.toLp 2 (κ *ᵥ p) ∈ Ppos k r z z' γ x`.

Introduce `p`. Rewrite using `[mem_Ppos, mem_Ppos]`. Simplify using `only [WithLp.ofLp_toLp]`. Use `and_congr ?_ (by rw [Matrix.mulVec_mulVec])` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_mulVec, hc, ← Matrix.mulVec_mulVec]`.

Prove the components needed by the constructor for the conclusion. Introduce `h0`. Rewrite using `[h0, Matrix.mulVec_zero]`. Introduce `h0`. Establish `h7` using `congrArg (fun v => star κ *ᵥ v) h0`.

Simplify using `only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at h7`. Rewrite `h7` using `[← Matrix.mul_assoc, hu, Matrix.one_mul]`. Then use the resulting hypothesis. Unfold `GlobalTheory.Amp.Yv`. Use `congr 1`. Rewrite using `[gramProj_unitary (Ppos k r z z' γ x) (Ppos k r z z' γ (x * κ)) _ κ hκ hQ]`.

Use `congr 1`. Use function extensionality and compare the values at `a`. Simplify using `only [Matrix.mul_inv_rev, hinv, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hu', Matrix.one_mul]`.
-/
theorem Yv_K (z z' : Fin (2 * r + k + 1) → ℂ) (γ x : Mat k r) {κ : Mat k r} (hG : κ ∈ GG k r)
    (hκ : κ ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ) :
    Yv k r z z' γ (x * κ) = Yv k r z z' γ x := by
  have hu : star κ * κ = 1 := (Matrix.mem_unitaryGroup_iff').1 hκ
  have hu' : κ * star κ = 1 := (Matrix.mem_unitaryGroup_iff).1 hκ
  have hinv : κ⁻¹ = star κ := Matrix.inv_eq_left_inv hu
  have hH : Hpk k r * κ = κ * Hpk k r := by
    have h0 : κᴴ * Hpk k r * κ = Hpk k r := hG
    rw [← Matrix.star_eq_conjTranspose] at h0
    calc Hpk k r * κ = (κ * star κ) * Hpk k r * κ := by rw [hu', Matrix.one_mul]
      _ = κ * (star κ * Hpk k r * κ) := by simp only [Matrix.mul_assoc]
      _ = κ * Hpk k r := by rw [h0]
  have hc : (Hpk k r - 1) * κ = κ * (Hpk k r - 1) := by
    rw [Matrix.sub_mul, Matrix.mul_sub, hH, Matrix.one_mul, Matrix.mul_one]
  have hQ : ∀ p : Fin (2 * r + k + 1) → ℂ, WithLp.toLp 2 p ∈ Ppos k r z z' γ (x * κ) ↔
      WithLp.toLp 2 (κ *ᵥ p) ∈ Ppos k r z z' γ x := by
    intro p
    rw [mem_Ppos, mem_Ppos]
    simp only [WithLp.ofLp_toLp]
    refine and_congr ?_ (by rw [Matrix.mulVec_mulVec])
    rw [Matrix.mulVec_mulVec, hc, ← Matrix.mulVec_mulVec]
    constructor
    · intro h0
      rw [h0, Matrix.mulVec_zero]
    · intro h0
      have h7 := congrArg (fun v => star κ *ᵥ v) h0
      simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at h7
      rwa [← Matrix.mul_assoc, hu, Matrix.one_mul] at h7
  unfold GlobalTheory.Amp.Yv
  congr 1
  rw [gramProj_unitary (Ppos k r z z' γ x) (Ppos k r z z' γ (x * κ)) _ κ hκ hQ]
  congr 1
  funext a
  simp only [Matrix.mul_inv_rev, hinv, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hu', Matrix.one_mul]

/- English proof (translation)
Establish `hmg : m * γ = γ * ρ`. Rewrite using `[hm]`. Simplify using `only [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ uγ, Matrix.mul_one]`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem inv_mul_mul_eq_of_eq_conj {k r : ℕ} {m γ ρ : Mat k r} (um : IsUnit m.det) (uγ : IsUnit γ.det)
    (hm : m = γ * ρ * γ⁻¹) : m⁻¹ * γ * ρ = γ := by
  have hmg : m * γ = γ * ρ := by
    rw [hm]
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ uγ, Matrix.mul_one]
  calc m⁻¹ * γ * ρ = m⁻¹ * (m * γ) := by rw [hmg, ← Matrix.mul_assoc]
    _ = γ := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ um, Matrix.one_mul]

/- English proof (translation)
Introduce `k r z z' γ hz hz' hγ x _hx`. Use `⟨fun κ hκ => Yv_K z z' γ x hκ.1 hκ.2, fun n₁ h₁ n₂ h₂ => Yv_N hz hz' γ h₁ h₂ x, fun ρ hρ => ?_⟩` and prove the remaining obligations. Establish `hm : γ * ρ * γ⁻¹ ∈ Nset k r` using `hρ.2`. Establish `hmi : (γ * ρ * γ⁻¹)⁻¹ ∈ Nset k r` using `(nSubgroup k r).2.2 _ hm`. Establish `e` using `inv_mul_mul_eq_of_eq_conj (det_unit hm.1) (det_unit hγ) (rfl : γ * ρ * γ⁻¹ = γ * ρ * γ⁻¹)`.

Establish `h8` using `Yv_N hz hz' γ hmi hρ.1 x`. Rewrite `h8` using `[e]`. Conclude with `h8.symm`.
-/
theorem yv_invariant : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (γ : Mat k r), inWb k r z → inWb k r z' → γ ∈ GG k r → ∀ x ∈ GG k r, (∀ κ ∈ (GG k r ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set (Mat k r))), Yv k r z z' γ (x * κ) = Yv k r z z' γ x) ∧ (∀ n₁ ∈ Nset k r, ∀ n₂ ∈ Nset k r, Yv k r z z' (n₁ * γ * n₂) x = Yv k r z z' γ (n₂ * x)) ∧ ∀ ρ ∈ Rset k r γ, Yv k r z z' γ (ρ * x) = Yv k r z z' γ x := by
  intro k r z z' γ hz hz' hγ x _hx
  refine ⟨fun κ hκ => Yv_K z z' γ x hκ.1 hκ.2, fun n₁ h₁ n₂ h₂ => Yv_N hz hz' γ h₁ h₂ x, fun ρ hρ => ?_⟩
  have hm : γ * ρ * γ⁻¹ ∈ Nset k r := hρ.2
  have hmi : (γ * ρ * γ⁻¹)⁻¹ ∈ Nset k r := (nSubgroup k r).2.2 _ hm
  have e := inv_mul_mul_eq_of_eq_conj (det_unit hm.1) (det_unit hγ) (rfl : γ * ρ * γ⁻¹ = γ * ρ * γ⁻¹)
  have h8 := Yv_N hz hz' γ hmi hρ.1 x
  rw [e] at h8
  exact h8.symm

end GlobalTheory.Amp.YInv
