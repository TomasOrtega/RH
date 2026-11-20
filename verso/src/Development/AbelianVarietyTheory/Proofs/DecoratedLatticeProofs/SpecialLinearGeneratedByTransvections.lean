import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.GlGeneratedTransvectionsDiag

noncomputable section
namespace GlobalTheory.GLGen
open Matrix

variable {R : Type} [CommRing R] {n : ℕ}

/- English proof (translation)
Apply the tactic sequence `ext p q; simp only [Matrix.single_apply, Matrix.neg_apply]; split_ifs <;> simp`.
-/
theorem single_neg' (x y : Fin n) (a : R) : single x y (-a) = -single x y a := by
  ext p q; simp only [Matrix.single_apply, Matrix.neg_apply]; split_ifs <;> simp

/- English proof (translation)
Establish `h1 : diagonal a * diagonal b = (1 : Matrix (Fin n) (Fin n) R)`. Rewrite using `[diagonal_mul_diagonal]`. Simplify using `[hab]`. Simplify using `only [transvection, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, h1]`. Use `congr 1`.

Use extensionality with `x y`. Simplify using `only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.single_apply]`. Apply the tactic sequence `split_ifs with h <;> simp_all`.
-/
theorem diag_transv_diag (a b : Fin n → R) (hab : ∀ k, a k * b k = 1) {i j : Fin n} (hij : i ≠ j) (c : R) :
    diagonal a * transvection i j c * diagonal b = transvection i j (a i * c * b j) := by
  have h1 : diagonal a * diagonal b = (1 : Matrix (Fin n) (Fin n) R) := by
    rw [diagonal_mul_diagonal]; simp [hab]
  simp only [transvection, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, h1]
  congr 1
  ext x y
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.single_apply]
  split_ifs with h <;> simp_all

/- English proof (translation)
Establish `z1 : ∀ (a b : R) (x l : Fin n), single x j a * single j l b = single x l (a * b)` using `fun a b x l => single_mul_single_same _ _ _ _ _`. Establish `z2 : ∀ (a b : R) (x l : Fin n), single x i a * single i l b = single x l (a * b)` using `fun a b x l => single_mul_single_same _ _ _ _ _`. Establish `z3 : ∀ (a b : R) (x l : Fin n), single x j a * single i l b = 0` using `fun a b x l => single_mul_single_of_ne a x j i hij.symm b`. Establish `z4 : ∀ (a b : R) (x l : Fin n), single x i a * single j l b = 0` using `fun a b x l => single_mul_single_of_ne a x i j hij b`. Simplify using `only [transvection, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc, z1, z2, z3, z4]`.

Simplify using `only [mul_neg, neg_mul, Units.mul_inv, Units.inv_mul, Units.mul_inv_cancel_left, Units.inv_mul_cancel_left, single_neg', Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, one_mul, mul_one]`. Normalize the expressions using the abelian group laws.
-/
theorem w_eq {i j : Fin n} (hij : i ≠ j) (u : Rˣ) :
    transvection i j (u : R) * transvection j i (-((u⁻¹ : Rˣ) : R)) * transvection i j (u : R) =
      1 + single i j (u : R) + single j i (-((u⁻¹ : Rˣ) : R)) - single i i 1 - single j j 1 := by
  have z1 : ∀ (a b : R) (x l : Fin n), single x j a * single j l b = single x l (a * b) := fun a b x l => single_mul_single_same _ _ _ _ _
  have z2 : ∀ (a b : R) (x l : Fin n), single x i a * single i l b = single x l (a * b) := fun a b x l => single_mul_single_same _ _ _ _ _
  have z3 : ∀ (a b : R) (x l : Fin n), single x j a * single i l b = 0 := fun a b x l => single_mul_single_of_ne a x j i hij.symm b
  have z4 : ∀ (a b : R) (x l : Fin n), single x i a * single j l b = 0 := fun a b x l => single_mul_single_of_ne a x i j hij b
  simp only [transvection, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc, z1, z2, z3, z4]
  simp only [mul_neg, neg_mul, Units.mul_inv, Units.inv_mul, Units.mul_inv_cancel_left, Units.inv_mul_cancel_left, single_neg', Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, one_mul, mul_one]
  abel

/- English proof (translation)
Establish `z1 : ∀ (a b : R) (x l : Fin n), single x j a * single j l b = single x l (a * b)` using `fun a b x l => single_mul_single_same _ _ _ _ _`. Establish `z2 : ∀ (a b : R) (x l : Fin n), single x i a * single i l b = single x l (a * b)` using `fun a b x l => single_mul_single_same _ _ _ _ _`. Establish `z3 : ∀ (a b : R) (x l : Fin n), single x j a * single i l b = 0` using `fun a b x l => single_mul_single_of_ne a x j i hij.symm b`. Establish `z4 : ∀ (a b : R) (x l : Fin n), single x i a * single j l b = 0` using `fun a b x l => single_mul_single_of_ne a x i j hij b`. Simplify using `only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, z1, z2, z3, z4]`.

Use `clear z1 z2 z3 z4`. Use extensionality with `p q`. Simplify using `only [Matrix.add_apply, Matrix.sub_apply, Matrix.single_apply, Matrix.one_apply, Matrix.diagonal_apply]`. Establish `hji : j ≠ i` using `Ne.symm hij`. Distinguish the cases in `hpq : p = q`.

Substitute `hpq` using the available equality. Distinguish the cases in `hpi : p = i`. Substitute `hpi` using the available equality. Simplify using `[hij, hji]`. Distinguish the cases in `hpj : p = j`.

Substitute `hpj` using the available equality. Simplify using `[hij, hji]`. Simplify using `[hpi, hpj, Ne.symm hpi, Ne.symm hpj]`. Apply the tactic sequence `by_cases hpi : p = i <;> by_cases hqi : q = i <;> by_cases hpj : p = j <;> by_cases hqj : q = j <;>`. Simplify using `[eq_comm]`.
-/
theorem ww_eq {i j : Fin n} (hij : i ≠ j) (u : Rˣ) :
    (1 + single i j (u : R) + single j i (-((u⁻¹ : Rˣ) : R)) - single i i 1 - single j j 1) *
      (1 + single i j ((-1 : Rˣ) : R) + single j i (-(((-1 : Rˣ)⁻¹ : Rˣ) : R)) - single i i 1 - single j j 1) =
      diagonal (fun k => if k = i then (u : R) else if k = j then ((u⁻¹ : Rˣ) : R) else 1) := by
  have z1 : ∀ (a b : R) (x l : Fin n), single x j a * single j l b = single x l (a * b) := fun a b x l => single_mul_single_same _ _ _ _ _
  have z2 : ∀ (a b : R) (x l : Fin n), single x i a * single i l b = single x l (a * b) := fun a b x l => single_mul_single_same _ _ _ _ _
  have z3 : ∀ (a b : R) (x l : Fin n), single x j a * single i l b = 0 := fun a b x l => single_mul_single_of_ne a x j i hij.symm b
  have z4 : ∀ (a b : R) (x l : Fin n), single x i a * single j l b = 0 := fun a b x l => single_mul_single_of_ne a x i j hij b
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, z1, z2, z3, z4]
  clear z1 z2 z3 z4
  ext p q
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.single_apply, Matrix.one_apply, Matrix.diagonal_apply]
  have hji : j ≠ i := Ne.symm hij
  by_cases hpq : p = q
  · subst hpq
    by_cases hpi : p = i
    · subst hpi; simp [hij, hji]
    · by_cases hpj : p = j
      · subst hpj; simp [hij, hji]
      · simp [hpi, hpj, Ne.symm hpi, Ne.symm hpj]
  · by_cases hpi : p = i <;> by_cases hqi : q = i <;> by_cases hpj : p = j <;> by_cases hqj : q = j <;>
      simp_all [eq_comm]

def diagU (u : Fin n → Rˣ) : GL (Fin n) R :=
  ⟨diagonal (fun k => (u k : R)), diagonal (fun k => (((u k)⁻¹ : Rˣ) : R)),
    by rw [diagonal_mul_diagonal]; simp, by rw [diagonal_mul_diagonal]; simp⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem diagU_val (u : Fin n → Rˣ) : ((diagU u : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = diagonal (fun k => (u k : R)) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem diagU_inv_val (u : Fin n → Rˣ) :
    (((diagU u)⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = diagonal (fun k => (((u k)⁻¹ : Rˣ) : R)) := rfl

/- English proof (translation)
Use extensionality with `: 1`. Simplify using `only [Units.val_mul, diagU_val, diagonal_mul_diagonal, Pi.mul_apply]`.
-/
theorem diagU_mul (u v : Fin n → Rˣ) : diagU (u * v) = diagU u * diagU v := by
  ext : 1
  simp only [Units.val_mul, diagU_val, diagonal_mul_diagonal, Pi.mul_apply]

/- English proof (translation)
Use extensionality with `: 1`. Simplify using `[diagU_val]`.
-/
theorem diagU_one : diagU (1 : Fin n → Rˣ) = 1 := by
  ext : 1
  simp [diagU_val]

def transvGL {i j : Fin n} (hij : i ≠ j) (c : R) : GL (Fin n) R :=
  ⟨transvection i j c, transvection i j (-c),
    by rw [transvection_mul_transvection_same (h := hij), add_neg_cancel, transvection_zero],
    by rw [transvection_mul_transvection_same (h := hij), neg_add_cancel, transvection_zero]⟩

def transvSet (R : Type) [CommRing R] (n : ℕ) : Set (GL (Fin n) R) :=
  {g | ∃ i j c, i ≠ j ∧ (g : Matrix (Fin n) (Fin n) R) = transvection i j c}

def elem (R : Type) [CommRing R] (n : ℕ) : Subgroup (GL (Fin n) R) := Subgroup.closure (transvSet R n)

/- English proof (translation)
The claim follows from `Subgroup.subset_closure ⟨i, j, c, hij, rfl⟩`.
-/
theorem transvGL_mem {i j : Fin n} (hij : i ≠ j) (c : R) : transvGL hij c ∈ elem R n :=
  Subgroup.subset_closure ⟨i, j, c, hij, rfl⟩

/- English proof (translation)
Establish `hle : elem R n ≤ (elem R n).comap (MulAut.conj (diagU u)).toMonoidHom`. Use `Subgroup.closure_le _ |>.2 ?_` and prove the remaining obligations. Introduce and unpack `g ⟨i, j, c, hij, hg⟩`. Simplify using `only [Subgroup.coe_comap, Set.mem_preimage, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]`. Use `Subgroup.subset_closure ⟨i, j, (u i : R) * c * ((u j)⁻¹ : Rˣ), hij, ?_⟩` and prove the remaining obligations.

Rewrite using `[Units.val_mul, Units.val_mul, hg, diagU_val, diagU_inv_val]`. Conclude with `diag_transv_diag _ _ (fun k => Units.mul_inv (u k)) hij c`. Simplify using `using hle he`.
-/
theorem conj_mem (u : Fin n → Rˣ) {e : GL (Fin n) R} (he : e ∈ elem R n) :
    diagU u * e * (diagU u)⁻¹ ∈ elem R n := by
  have hle : elem R n ≤ (elem R n).comap (MulAut.conj (diagU u)).toMonoidHom := by
    refine Subgroup.closure_le _ |>.2 ?_
    rintro g ⟨i, j, c, hij, hg⟩
    simp only [Subgroup.coe_comap, Set.mem_preimage, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    refine Subgroup.subset_closure ⟨i, j, (u i : R) * c * ((u j)⁻¹ : Rˣ), hij, ?_⟩
    rw [Units.val_mul, Units.val_mul, hg, diagU_val, diagU_inv_val]
    exact diag_transv_diag _ _ (fun k => Units.mul_inv (u k)) hij c
  simpa using hle he

/- English proof (translation)
Establish `e : diagU (fun k => if k = i then u else if k = j then u⁻¹ else 1) = transvGL hij (u : R) * transvGL hij.symm (-((u⁻¹ : Rˣ) : R)) * transvGL hij (u : R) * (transvGL hij ((-1 : Rˣ) : R) * transvGL hij.symm (-(((-1 : Rˣ)⁻¹ : Rˣ) : R)) * transvGL hij ((-1 : Rˣ) : R))`. Use extensionality with `: 1`. Simplify using `only [Units.val_mul, transvGL, diagU_val]`. Rewrite using `[w_eq hij u, w_eq hij (-1), ww_eq hij u]`. Use `congr 1`.

Use function extensionality and compare the values at `k`. Apply the tactic sequence `split_ifs <;> rfl`. Rewrite using `[e]`. Apply the tactic sequence `refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_) (Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_) <;> exact transvGL_mem _ _`.
-/
theorem whitehead_mem {i j : Fin n} (hij : i ≠ j) (u : Rˣ) :
    diagU (fun k => if k = i then u else if k = j then u⁻¹ else 1) ∈ elem R n := by
  have e : diagU (fun k => if k = i then u else if k = j then u⁻¹ else 1) =
      transvGL hij (u : R) * transvGL hij.symm (-((u⁻¹ : Rˣ) : R)) * transvGL hij (u : R) *
      (transvGL hij ((-1 : Rˣ) : R) * transvGL hij.symm (-(((-1 : Rˣ)⁻¹ : Rˣ) : R)) *
        transvGL hij ((-1 : Rˣ) : R)) := by
    ext : 1
    simp only [Units.val_mul, transvGL, diagU_val]
    rw [w_eq hij u, w_eq hij (-1), ww_eq hij u]
    congr 1
    funext k
    split_ifs <;> rfl
  rw [e]
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_)
    (Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_) <;> exact transvGL_mem _ _

/- English proof (translation)
The claim follows from `eq_inv_of_mul_eq_one_left (by rw [← diagU_mul, inv_mul_cancel, diagU_one])`.
-/
theorem diagU_inv (u : Fin n → Rˣ) : diagU u⁻¹ = (diagU u)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← diagU_mul, inv_mul_cancel, diagU_one])

def diagHomU : (Fin n → Rˣ) →* GL (Fin n) R where
  toFun := diagU
  map_one' := diagU_one
  map_mul' := diagU_mul

/- English proof (translation)
Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Establish `: (Pi.mulSingle i a * Pi.mulSingle i a⁻¹ : Fin n → Rˣ) = 1`. Rewrite using `[← Pi.mulSingle_mul]`. Simplify using the standard rewrite rules.

Rewrite using `[this, diagU_one]`. Conclude with `one_mem _`. Establish `hji : j ≠ i` using `fun h => hij h.symm`. Establish `: (Pi.mulSingle i a * Pi.mulSingle j a⁻¹ : Fin n → Rˣ) = fun k => if k = i then a else if k = j then a⁻¹ else 1`. Use function extensionality and compare the values at `k`.

Distinguish the cases in `hki : k = i`. Substitute `hki` using the available equality. Simplify using `[hij]`. Distinguish the cases in `hkj : k = j`. Substitute `hkj` using the available equality.

Simplify using `[hki]`. Simplify using `[hki, hkj]`. Rewrite using `[this]`. Conclude with `whitehead_mem hij a`.
-/
theorem pair_mem_elem (i j : Fin n) (a : Rˣ) :
    diagU (Pi.mulSingle i a * Pi.mulSingle j a⁻¹ : Fin n → Rˣ) ∈ elem R n := by
  by_cases hij : i = j
  · subst hij
    have : (Pi.mulSingle i a * Pi.mulSingle i a⁻¹ : Fin n → Rˣ) = 1 := by
      rw [← Pi.mulSingle_mul]; simp
    rw [this, diagU_one]
    exact one_mem _
  · have hji : j ≠ i := fun h => hij h.symm
    have : (Pi.mulSingle i a * Pi.mulSingle j a⁻¹ : Fin n → Rˣ) =
        fun k => if k = i then a else if k = j then a⁻¹ else 1 := by
      funext k
      by_cases hki : k = i
      · subst hki; simp [hij]
      · by_cases hkj : k = j
        · subst hkj; simp [hki]
        · simp [hki, hkj]
    rw [this]
    exact whitehead_mem hij a

/- English proof (translation)
Break down `Nat.eq_zero_or_pos n with h0 | hpos` into its components or cases. Substitute `h0` using the available equality. Establish `: diagU u = 1` using `Units.ext (Subsingleton.elim _ _)`. Rewrite using `[this]`. Conclude with `one_mem _`.

Set `j : Fin n` to `⟨0, hpos⟩`. Establish `key : u = ∏ k, (Pi.mulSingle k (u k) * Pi.mulSingle j (u k)⁻¹ : Fin n → Rˣ)`. Rewrite using `[Finset.prod_mul_distrib, Finset.univ_prod_mulSingle]`. Establish `: (∏ k, (Pi.mulSingle j (u k)⁻¹ : Fin n → Rˣ)) = 1`. Establish `h` using `map_prod (MonoidHom.mulSingle (fun _ : Fin n => Rˣ) j) (fun k => (u k)⁻¹) Finset.univ`.

Rewrite `h` using `[Finset.prod_inv_distrib, hu, inv_one, map_one]`. Conclude with `h.symm`. Rewrite using `[this, mul_one]`. Establish `: u ∈ (elem R n).comap (diagHomU (R` using `R) (n := n)) := by`. Rewrite using `[key]`.

Conclude with `Subgroup.prod_mem _ (fun k _ => pair_mem_elem k j (u k))`. Conclude with `this`.
-/
theorem diag_mem_of_prod (u : Fin n → Rˣ) (hu : ∏ k, u k = 1) : diagU u ∈ elem R n := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    have : diagU u = 1 := Units.ext (Subsingleton.elim _ _)
    rw [this]
    exact one_mem _
  · let j : Fin n := ⟨0, hpos⟩
    have key : u = ∏ k, (Pi.mulSingle k (u k) * Pi.mulSingle j (u k)⁻¹ : Fin n → Rˣ) := by
      rw [Finset.prod_mul_distrib, Finset.univ_prod_mulSingle]
      have : (∏ k, (Pi.mulSingle j (u k)⁻¹ : Fin n → Rˣ)) = 1 := by
        have h := map_prod (MonoidHom.mulSingle (fun _ : Fin n => Rˣ) j) (fun k => (u k)⁻¹)
          Finset.univ
        rw [Finset.prod_inv_distrib, hu, inv_one, map_one] at h
        exact h.symm
      rw [this, mul_one]
    have : u ∈ (elem R n).comap (diagHomU (R := R) (n := n)) := by
      rw [key]
      exact Subgroup.prod_mem _ (fun k _ => pair_mem_elem k j (u k))
    exact this

/- English proof (translation)
Establish `hle : elem R n ≤ (GeneralLinearGroup.det : GL (Fin n) R →* Rˣ).ker`. Use `Subgroup.closure_le _ |>.2 ?_` and prove the remaining obligations. Introduce and unpack `g ⟨i, j, c, hij, hg⟩`. Rewrite using `[SetLike.mem_coe, MonoidHom.mem_ker]`. Use `ext`.

Rewrite using `[GeneralLinearGroup.val_det_apply, hg, det_transvection_of_ne _ _ hij]`. Both sides reduce to the same expression. Conclude with `hle he`.
-/
theorem det_eq_one_of_mem {e : GL (Fin n) R} (he : e ∈ elem R n) : GeneralLinearGroup.det e = 1 := by
  have hle : elem R n ≤ (GeneralLinearGroup.det : GL (Fin n) R →* Rˣ).ker := by
    refine Subgroup.closure_le _ |>.2 ?_
    rintro g ⟨i, j, c, hij, hg⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    ext
    rw [GeneralLinearGroup.val_det_apply, hg, det_transvection_of_ne _ _ hij]
    rfl
  exact hle he

/- English proof (translation)
Introduce `R _ hsr n H hH a ha`. Establish `hEH : elem R n ≤ H` using `Subgroup.closure_le _ |>.2 (by`. Introduce and unpack `g ⟨i, j, c, hij, hg⟩`. Conclude with `hH i j hij c g hg)`. Establish `hSR : PI.VolSemiDirect.W.Cj.HasStableRangeOne R` using `fun a b x y h => hsr a b ⟨x, y, by rw [← h]; ring⟩`.

Establish `hmem` using `PI.VolSemiDirect.W.Cj.gl_generated_transvections_diag R hSR n a`. Establish `key : ∀ g ∈ Subgroup.closure ({g : GL (Fin n) R | ∃ i j c, i ≠ j ∧ (g : Matrix (Fin n) (Fin n) R) = Matrix.transvection i j c} ∪ {g | ∃ d : Fin n → R, (g : Matrix (Fin n) (Fin n) R) = Matrix.diagonal d}), ∃ u : Fin n → Rˣ, g * diagU u ∈ elem R n`. Introduce `g hg`. Proceed by induction on `hg using Subgroup.closure_induction with`. Consider the case `mem g hg`.

Break down `hg with ⟨i, j, c, hij, hg⟩ | ⟨d, hd⟩` into its components or cases. Conclude with `⟨1, by rw [diagU_one, mul_one]; exact Subgroup.subset_closure ⟨i, j, c, hij, hg⟩⟩`. Establish `hu : ∀ k, IsUnit (d k)` using `fun k => by`. Establish `h : ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) * (g : Matrix (Fin n) (Fin n) R) = 1`. Rewrite using `[← Units.val_mul, inv_mul_cancel, Units.val_one]`.

Establish `h'` using `congrFun (congrFun h k) k`. Rewrite `h'` using `[hd, Matrix.mul_diagonal, one_apply_eq]`. Conclude with `⟨⟨d k, _, by rw [mul_comm]; exact h', h'⟩, rfl⟩`. Use `⟨fun k => (hu k).unit⁻¹, ?_⟩` and prove the remaining obligations. Establish `e : g * diagU (fun k => (hu k).unit⁻¹) = 1`.

Use extensionality with `: 1`. Rewrite using `[Units.val_mul, hd, diagU_val, diagonal_mul_diagonal, Units.val_one, ← diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `k`. Conclude with `(hu k).mul_val_inv`.

Rewrite using `[e]`. Conclude with `Subgroup.one_mem _`. Consider the case `one => exact ⟨1, by rw [diagU_one, mul_one]; exact Subgroup.one_mem _⟩`. Consider the case `mul x y _ _ hx hy`. Take `⟨u, hu⟩` from `hx`.

Take `⟨v, hv⟩` from `hy`. Use `⟨v * u, ?_⟩` and prove the remaining obligations. Establish `h` using `Subgroup.mul_mem _ hu (conj_mem u⁻¹ hv)`. Rewrite `h` using `[diagU_inv, inv_inv]`. Use `h using 1` and compare the differences between its conclusion and the goal.

Rewrite using `[diagU_mul]`. Use `group`. Consider the case `inv x _ hx`. Take `⟨u, hu⟩` from `hx`. Use `⟨u⁻¹, ?_⟩` and prove the remaining obligations.

Establish `h` using `conj_mem u (Subgroup.inv_mem _ hu)`. Rewrite using `[diagU_inv]`. Use `h using 1` and compare the differences between its conclusion and the goal. Use `group`. Take `⟨u, hu⟩` from `key a hmem`.

Establish `h1` using `det_eq_one_of_mem hu`. Rewrite `h1` using `[map_mul, ha, one_mul]`. Establish `hprod : ∏ k, u k = 1`. Establish `h2` using `congrArg Units.val h1`. Rewrite `h2` using `[GeneralLinearGroup.val_det_apply, diagU_val, det_diagonal]`.

Use `ext`. Rewrite using `[Units.coe_prod]`. Simplify using `using h2`. Establish `hd` using `diag_mem_of_prod u hprod`. Establish `e : a = (a * diagU u) * (diagU u)⁻¹` using `by group`.

Rewrite using `[e]`. Conclude with `hEH (Subgroup.mul_mem _ hu (Subgroup.inv_mem _ hd))`.
-/
theorem mem_of_det_eq_one : ∀ (R : Type) [CommRing R], (∀ a b : R, IsCoprime a b → ∃ t : R, IsUnit (a + t * b)) →
    ∀ (n : ℕ) (H : Subgroup (GL (Fin n) R)), (∀ (i j : Fin n), i ≠ j → ∀ (t : R) (u : GL (Fin n) R),
      u.1 = Matrix.transvection i j t → u ∈ H) → ∀ a : GL (Fin n) R, Matrix.GeneralLinearGroup.det a = 1 → a ∈ H := by
  intro R _ hsr n H hH a ha
  have hEH : elem R n ≤ H := Subgroup.closure_le _ |>.2 (by
    rintro g ⟨i, j, c, hij, hg⟩; exact hH i j hij c g hg)
  have hSR : PI.VolSemiDirect.W.Cj.HasStableRangeOne R := fun a b x y h =>
    hsr a b ⟨x, y, by rw [← h]; ring⟩
  have hmem := PI.VolSemiDirect.W.Cj.gl_generated_transvections_diag R hSR n a
  have key : ∀ g ∈ Subgroup.closure ({g : GL (Fin n) R | ∃ i j c, i ≠ j ∧
      (g : Matrix (Fin n) (Fin n) R) = Matrix.transvection i j c} ∪
      {g | ∃ d : Fin n → R, (g : Matrix (Fin n) (Fin n) R) = Matrix.diagonal d}),
      ∃ u : Fin n → Rˣ, g * diagU u ∈ elem R n := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      rcases hg with ⟨i, j, c, hij, hg⟩ | ⟨d, hd⟩
      · exact ⟨1, by rw [diagU_one, mul_one]; exact Subgroup.subset_closure ⟨i, j, c, hij, hg⟩⟩
      · have hu : ∀ k, IsUnit (d k) := fun k => by
          have h : ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) * (g : Matrix (Fin n) (Fin n) R) = 1 := by
            rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
          have h' := congrFun (congrFun h k) k
          rw [hd, Matrix.mul_diagonal, one_apply_eq] at h'
          exact ⟨⟨d k, _, by rw [mul_comm]; exact h', h'⟩, rfl⟩
        refine ⟨fun k => (hu k).unit⁻¹, ?_⟩
        have e : g * diagU (fun k => (hu k).unit⁻¹) = 1 := by
          ext : 1
          rw [Units.val_mul, hd, diagU_val, diagonal_mul_diagonal, Units.val_one, ← diagonal_one]
          congr 1
          funext k
          exact (hu k).mul_val_inv
        rw [e]; exact Subgroup.one_mem _
    | one => exact ⟨1, by rw [diagU_one, mul_one]; exact Subgroup.one_mem _⟩
    | mul x y _ _ hx hy =>
      obtain ⟨u, hu⟩ := hx
      obtain ⟨v, hv⟩ := hy
      refine ⟨v * u, ?_⟩
      have h := Subgroup.mul_mem _ hu (conj_mem u⁻¹ hv)
      rw [diagU_inv, inv_inv] at h
      convert h using 1
      rw [diagU_mul]
      group
    | inv x _ hx =>
      obtain ⟨u, hu⟩ := hx
      refine ⟨u⁻¹, ?_⟩
      have h := conj_mem u (Subgroup.inv_mem _ hu)
      rw [diagU_inv]
      convert h using 1
      group
  obtain ⟨u, hu⟩ := key a hmem
  have h1 := det_eq_one_of_mem hu
  rw [map_mul, ha, one_mul] at h1
  have hprod : ∏ k, u k = 1 := by
    have h2 := congrArg Units.val h1
    rw [GeneralLinearGroup.val_det_apply, diagU_val, det_diagonal] at h2
    ext
    rw [Units.coe_prod]
    simpa using h2
  have hd := diag_mem_of_prod u hprod
  have e : a = (a * diagU u) * (diagU u)⁻¹ := by group
  rw [e]
  exact hEH (Subgroup.mul_mem _ hu (Subgroup.inv_mem _ hd))

end GlobalTheory.GLGen
