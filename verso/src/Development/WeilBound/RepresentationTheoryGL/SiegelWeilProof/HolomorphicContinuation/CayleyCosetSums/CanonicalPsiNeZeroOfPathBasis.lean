import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.FdProps
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegralConjInnerMulInnerOfIsEmptyEquiv
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.DerivProdRangeSubMulProdNeZero
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.HasDerivAtDetOneAdd
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.InverseFirstBlockMulUnipotentDomain

noncomputable section

open MeasureTheory Matrix
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

/- English proof (translation)
Establish `hc : Continuous fun p : Kg × M2 n => ι p.1 * p.2` using `(hι.comp continuous_fst).mul continuous_snd`. Establish `hcl : IsClosed {p : Kg × M2 n | ι p.1 * p.2 ∉ U}` using `(hU.preimage hc).isClosed_compl`. Establish `himg` using `isClosedMap_snd_of_compactSpace (X := Kg) (Y := M2 n) _ hcl`. Establish `heq : {x : M2 n | ∀ k, ι k * x ∈ U} = (Prod.snd '' {p : Kg × M2 n | ι p.1 * p.2 ∉ U})ᶜ`. Use extensionality with `x`.

Simplify using `only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_image, Prod.exists, exists_eq_right, not_exists, not_not]`. Rewrite using `[heq]`. Conclude with `himg.isOpen_compl`.
-/
theorem isOpen_setK {U : Set (M2 n)} (hU : IsOpen U) (Kg : Type) [TopologicalSpace Kg] [CompactSpace Kg]
    (ι : Kg → M2 n) (hι : Continuous ι) : IsOpen {x : M2 n | ∀ k, ι k * x ∈ U} := by
  have hc : Continuous fun p : Kg × M2 n => ι p.1 * p.2 :=
    (hι.comp continuous_fst).mul continuous_snd
  have hcl : IsClosed {p : Kg × M2 n | ι p.1 * p.2 ∉ U} := (hU.preimage hc).isClosed_compl
  have himg := isClosedMap_snd_of_compactSpace (X := Kg) (Y := M2 n) _ hcl
  have heq : {x : M2 n | ∀ k, ι k * x ∈ U} = (Prod.snd '' {p : Kg × M2 n | ι p.1 * p.2 ∉ U})ᶜ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_image, Prod.exists, exists_eq_right, not_exists, not_not]
  rw [heq]
  exact himg.isOpen_compl

/- English proof (translation)
Rewrite using `[← fromBlocks_toBlocks y]`. Use extensionality with `i j`. Simplify using `[Cm, fromBlocks_multiply, u1, toBlocks₂₁, toBlocks₂₂]`.
-/
private theorem u1_eq_toBlocks₂₁_mul_Cm (y : M2 n) : u1 y = toBlocks₂₁ (y * Cm n) := by
  rw [← fromBlocks_toBlocks y]
  ext i j
  simp [Cm, fromBlocks_multiply, u1, toBlocks₂₁, toBlocks₂₂]

/- English proof (translation)
Rewrite using `[ub1]`. Use `conv_rhs => rw [← fromBlocks_toBlocks y⁻¹]`. Simplify using `[fromBlocks_multiply]`.
-/
private theorem ub1_eq_toBlocks₁₁_fromBlocks_mul_inv (y : M2 n) :
    ub1 y = toBlocks₁₁ (fromBlocks 1 (Complex.I • 1) 0 0 * y⁻¹) := by
  rw [ub1]
  conv_rhs => rw [← fromBlocks_toBlocks y⁻¹]
  simp [fromBlocks_multiply]

/- English proof (translation)
Establish `h : fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) (Complex.I • 1) 0 0 * Cm n = fromBlocks ((2 * Complex.I) • 1) 0 0 0`. Simplify using `only [Cm, fromBlocks_multiply]`. Apply the tactic sequence `congr 1 <;> ext i j <;> simp [Matrix.one_apply] <;> split_ifs <;> ring_nf <;> simp`. Rewrite using `[h, fromBlocks_multiply, fromBlocks_multiply]`. Simplify using the standard rewrite rules.
-/
private theorem fromBlocks_I_mul_Cm_mul_fromBlocks_diag (A B : Matrix (Fin n) (Fin n) ℂ) :
    fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) (Complex.I • 1) 0 0 * Cm n * fromBlocks A 0 0 B =
      fromBlocks A 0 0 1 * (fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) (Complex.I • 1) 0 0 * Cm n) := by
  have h : fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) (Complex.I • 1) 0 0 * Cm n =
      fromBlocks ((2 * Complex.I) • 1) 0 0 0 := by
    simp only [Cm, fromBlocks_multiply]
    congr 1 <;> ext i j <;> simp [Matrix.one_apply] <;> split_ifs <;> ring_nf <;> simp
  rw [h, fromBlocks_multiply, fromBlocks_multiply]
  simp

/- English proof (translation)
Establish `hd : ∀ a, P' a a = 0`. Introduce `a`. Assume the negation of the conclusion as `h`. Take `⟨h1, h2⟩` from `hP a a h`. Simplify using `[blkB] at h2`.

Conclude with `h2 h1`. Rewrite using `[Matrix.det_of_upperTriangular]`. Simplify using `[hd]`. Introduce `a b hab`. Establish `hab' : (b : ℕ) < a` using `hab`.

Establish `hne : a ≠ b` using `fun h => by subst h; omega`. Simplify using `only [Matrix.add_apply, Matrix.one_apply, hne, if_false, zero_add]`. Assume the negation of the conclusion as `h`. Take `⟨h1, h2⟩` from `hP a b h`. Simplify using `[blkA, blkB] at h1 h2`.

Use linear arithmetic over natural numbers and integers.
-/
private theorem det_one_add_of_support_blkA_blkB (j : ℕ) (P' : Matrix (Fin n) (Fin n) ℂ)
    (hP : ∀ a b, P' a b ≠ 0 → a ∈ blkA j ∧ b ∈ blkB j) : det (1 + P') = 1 := by
  have hd : ∀ a, P' a a = 0 := by
    intro a
    by_contra h
    obtain ⟨h1, h2⟩ := hP a a h
    simp [blkB] at h2
    exact h2 h1
  rw [Matrix.det_of_upperTriangular]
  · simp [hd]
  · intro a b hab
    have hab' : (b : ℕ) < a := hab
    have hne : a ≠ b := fun h => by subst h; omega
    simp only [Matrix.add_apply, Matrix.one_apply, hne, if_false, zero_add]
    by_contra h
    obtain ⟨h1, h2⟩ := hP a b h
    simp [blkA, blkB] at h1 h2
    omega

/- English proof (translation)
Establish `hd : ∀ a, S' a a = 0`. Introduce `a`. Assume the negation of the conclusion as `h`. Take `⟨h1, h2⟩` from `hS a a h`. Simplify using `[blkB] at h1`.

Conclude with `h1 h2`. Rewrite using `[Matrix.det_of_lowerTriangular]`. Simplify using `[hd]`. Introduce `a b hab`. Establish `hab' : (a : ℕ) < b` using `hab`.

Establish `hne : a ≠ b` using `fun h => by subst h; omega`. Simplify using `only [Matrix.add_apply, Matrix.one_apply, hne, if_false, zero_add]`. Assume the negation of the conclusion as `h`. Take `⟨h1, h2⟩` from `hS a b h`. Simplify using `[blkA, blkB] at h1 h2`.

Use linear arithmetic over natural numbers and integers.
-/
private theorem det_one_add_of_support_blkB_blkA (j : ℕ) (S' : Matrix (Fin n) (Fin n) ℂ)
    (hS : ∀ a b, S' a b ≠ 0 → a ∈ blkB j ∧ b ∈ blkA j) : det (1 + S') = 1 := by
  have hd : ∀ a, S' a a = 0 := by
    intro a
    by_contra h
    obtain ⟨h1, h2⟩ := hS a a h
    simp [blkB] at h1
    exact h1 h2
  rw [Matrix.det_of_lowerTriangular]
  · simp [hd]
  · intro a b hab
    have hab' : (a : ℕ) < b := hab
    have hne : a ≠ b := fun h => by subst h; omega
    simp only [Matrix.add_apply, Matrix.one_apply, hne, if_false, zero_add]
    by_contra h
    obtain ⟨h1, h2⟩ := hS a b h
    simp [blkA, blkB] at h1 h2
    omega

/- English proof (translation)
Establish `hPd : det (1 + P') = 1` using `det_one_add_of_support_blkA_blkB j P' hP`. Establish `hSd : det (1 + S') = 1` using `det_one_add_of_support_blkB_blkA j S' hS`. Establish `hPu : IsUnit (det (1 + P'))` using `by rw [hPd]; exact isUnit_one`. Establish `hSu : IsUnit (det (1 + S'))` using `by rw [hSd]; exact isUnit_one`. Establish `hCi : (Cm n)⁻¹ = Cmi n` using `Matrix.inv_eq_left_inv cmi_mul_cm`.

Establish `hCii : (Cmi n)⁻¹ = Cm n` using `Matrix.inv_eq_right_inv cmi_mul_cm`. Establish `hCC : Cm n * Cmi n = 1` using `mul_eq_one_comm.mp cmi_mul_cm`. Establish `hg : mX (1 + P') 0 0 (1 + S') = Cm n * fromBlocks (1 + P') 0 0 (1 + S') * Cmi n`. Rewrite using `[mX, hCi]`. Establish `hDinv : (fromBlocks (1 + P') 0 0 (1 + S'))⁻¹ = fromBlocks (1 + P')⁻¹ 0 0 (1 + S')⁻¹`.

Apply `Matrix.inv_eq_left_inv` to reduce the goal to its premises. Rewrite using `[fromBlocks_multiply]`. Simplify using `[Matrix.nonsing_inv_mul _ hPu, Matrix.nonsing_inv_mul _ hSu]`. Establish `hu : u1 (x * mX (1 + P') 0 0 (1 + S')) = u1 x * (1 + P')`. Rewrite using `[u1_eq_toBlocks₂₁_mul_Cm, u1_eq_toBlocks₂₁_mul_Cm x, hg]`.

Establish `h : x * (Cm n * fromBlocks (1 + P') 0 0 (1 + S') * Cmi n) * Cm n = (x * Cm n) * fromBlocks (1 + P') 0 0 (1 + S')`. Simplify using `only [Matrix.mul_assoc, cmi_mul_cm, Matrix.mul_one]`. Rewrite using `[h]`. Use `conv_lhs => rw [← fromBlocks_toBlocks (x * Cm n)]`. Rewrite using `[fromBlocks_multiply]`.

Simplify using the standard rewrite rules. Establish `hub : ub1 (x * mX (1 + P') 0 0 (1 + S')) = (1 + P')⁻¹ * ub1 x`. Rewrite using `[ub1_eq_toBlocks₁₁_fromBlocks_mul_inv, ub1_eq_toBlocks₁₁_fromBlocks_mul_inv x, hg, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mul_inv_rev, hCii, hDinv, hCi]`. Establish `h : fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) (Complex.I • 1) 0 0 * (Cm n * (fromBlocks (1 + P')⁻¹ 0 0 (1 + S')⁻¹ * Cmi n) * x⁻¹) = fromBlocks (1 + P')⁻¹ 0 0 1 * (fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) (Complex.I • 1) 0 0 * x⁻¹)`. Establish `h3` using `fromBlocks_I_mul_Cm_mul_fromBlocks_diag (n := n) (1 + P')⁻¹ (1 + S')⁻¹`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = _ := by`. Rewrite using `[h3]`. Simplify using `only [Matrix.mul_assoc, hCC, Matrix.one_mul]`.

Rewrite using `[h]`. Use `conv_lhs => rw [← fromBlocks_toBlocks (fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) (Complex.I • 1) 0 0 * x⁻¹)]`. Rewrite using `[fromBlocks_multiply]`. Simplify using the standard rewrite rules. Unfold `Fd`.

Use `congr 1`. Use function extensionality and compare the values at `z`. Simplify using `only [fz]`. Rewrite using `[hu, hub, det_mul, det_mul, det_mul, hPd, Matrix.det_nonsing_inv, hPd]`. Simplify using the standard rewrite rules.
-/
theorem Fd_kpart (m j : ℕ) (x : M2 n) (hx : x ∈ Dom n)
    (P' S' : Matrix (Fin n) (Fin n) ℂ) (hP : ∀ a b, P' a b ≠ 0 → a ∈ blkA j ∧ b ∈ blkB j)
    (hS : ∀ a b, S' a b ≠ 0 → a ∈ blkB j ∧ b ∈ blkA j) : Fd m (x * mX (1 + P') 0 0 (1 + S')) = Fd m x := by
  have hPd : det (1 + P') = 1 := det_one_add_of_support_blkA_blkB j P' hP
  have hSd : det (1 + S') = 1 := det_one_add_of_support_blkB_blkA j S' hS
  have hPu : IsUnit (det (1 + P')) := by rw [hPd]; exact isUnit_one
  have hSu : IsUnit (det (1 + S')) := by rw [hSd]; exact isUnit_one
  have hCi : (Cm n)⁻¹ = Cmi n := Matrix.inv_eq_left_inv cmi_mul_cm
  have hCii : (Cmi n)⁻¹ = Cm n := Matrix.inv_eq_right_inv cmi_mul_cm
  have hCC : Cm n * Cmi n = 1 := mul_eq_one_comm.mp cmi_mul_cm
  have hg : mX (1 + P') 0 0 (1 + S') = Cm n * fromBlocks (1 + P') 0 0 (1 + S') * Cmi n := by
    rw [mX, hCi]
  have hDinv : (fromBlocks (1 + P') 0 0 (1 + S'))⁻¹ = fromBlocks (1 + P')⁻¹ 0 0 (1 + S')⁻¹ := by
    apply Matrix.inv_eq_left_inv
    rw [fromBlocks_multiply]
    simp [Matrix.nonsing_inv_mul _ hPu, Matrix.nonsing_inv_mul _ hSu]
  have hu : u1 (x * mX (1 + P') 0 0 (1 + S')) = u1 x * (1 + P') := by
    rw [u1_eq_toBlocks₂₁_mul_Cm, u1_eq_toBlocks₂₁_mul_Cm x, hg]
    have h : x * (Cm n * fromBlocks (1 + P') 0 0 (1 + S') * Cmi n) * Cm n =
        (x * Cm n) * fromBlocks (1 + P') 0 0 (1 + S') := by
      simp only [Matrix.mul_assoc, cmi_mul_cm, Matrix.mul_one]
    rw [h]
    conv_lhs => rw [← fromBlocks_toBlocks (x * Cm n)]
    rw [fromBlocks_multiply]
    simp
  have hub : ub1 (x * mX (1 + P') 0 0 (1 + S')) = (1 + P')⁻¹ * ub1 x := by
    rw [ub1_eq_toBlocks₁₁_fromBlocks_mul_inv, ub1_eq_toBlocks₁₁_fromBlocks_mul_inv x, hg, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
      Matrix.mul_inv_rev, hCii, hDinv, hCi]
    have h : fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) (Complex.I • 1) 0 0 *
        (Cm n * (fromBlocks (1 + P')⁻¹ 0 0 (1 + S')⁻¹ * Cmi n) * x⁻¹) =
        fromBlocks (1 + P')⁻¹ 0 0 1 * (fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) (Complex.I • 1) 0 0 * x⁻¹) := by
      have h3 := fromBlocks_I_mul_Cm_mul_fromBlocks_diag (n := n) (1 + P')⁻¹ (1 + S')⁻¹
      calc _ = (fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) (Complex.I • 1) 0 0 * Cm n *
              fromBlocks (1 + P')⁻¹ 0 0 (1 + S')⁻¹) * Cmi n * x⁻¹ := by
            simp only [Matrix.mul_assoc]
        _ = _ := by
            rw [h3]
            simp only [Matrix.mul_assoc, hCC, Matrix.one_mul]
    rw [h]
    conv_lhs => rw [← fromBlocks_toBlocks (fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) (Complex.I • 1) 0 0 * x⁻¹)]
    rw [fromBlocks_multiply]
    simp
  unfold Fd
  congr 1
  funext z
  simp only [fz]
  rw [hu, hub, det_mul, det_mul, det_mul, hPd, Matrix.det_nonsing_inv, hPd]
  simp

/- English proof (translation)
Rewrite using `[← fromBlocks_toBlocks y]`. Use extensionality with `i j`. Simplify using `[Cm, fromBlocks_multiply, u2, toBlocks₂₁, toBlocks₂₂]`.
-/
private theorem u2_eq_toBlocks₂₂_mul_Cm (y : M2 n) : u2 y = toBlocks₂₂ (y * Cm n) := by
  rw [← fromBlocks_toBlocks y]
  ext i j
  simp [Cm, fromBlocks_multiply, u2, toBlocks₂₁, toBlocks₂₂]

/- English proof (translation)
Use `set E : Matrix (Fin n) (Fin n) ℂ := Matrix.single a0 b0 1 with hE`. Take `⟨hdx, hd1, hd2, hdb⟩` from `hx`. Establish `hCi : (Cm n)⁻¹ = Cmi n` using `Matrix.inv_eq_left_inv cmi_mul_cm`. Establish `hCC : Cm n * Cmi n = 1` using `mul_eq_one_comm.mp cmi_mul_cm`. Establish `hline : ∀ t : ℂ, x + t • (x * WD 0 E) = x * mX 1 0 (t • E) 1`.

Introduce `t`. Establish `h : mX 1 0 (t • E) 1 = 1 + t • WD 0 E`. Simplify using `only [mX, WD, hCi]`. Establish `h' : (fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) 0 (t • E) 1 : M2 n) = 1 + t • (fromBlocks 0 0 E 0 : M2 n)`. Rewrite using `[← fromBlocks_one, fromBlocks_smul, fromBlocks_add]`.

Simplify using the standard rewrite rules. Rewrite using `[h', Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hCC, Matrix.mul_smul, Matrix.smul_mul]`. Rewrite using `[h, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]`. Establish `hu1 : ∀ t : ℂ, u1 (x * mX 1 0 (t • E) 1) = u1 x + t • (u2 x * E)`. Introduce `t`.

Rewrite using `[u1_eq_toBlocks₂₁_mul_Cm, u1_eq_toBlocks₂₁_mul_Cm x, u2_eq_toBlocks₂₂_mul_Cm x, mX, hCi]`. Establish `h : x * (Cm n * fromBlocks 1 0 (t • E) 1 * Cmi n) * Cm n = (x * Cm n) * fromBlocks 1 0 (t • E) 1`. Simplify using `only [Matrix.mul_assoc, cmi_mul_cm, Matrix.mul_one]`. Rewrite using `[h]`. Use `conv_lhs => rw [← fromBlocks_toBlocks (x * Cm n)]`.

Rewrite using `[fromBlocks_multiply]`. Simplify using `[Matrix.mul_smul]`. Establish `hub : ∀ t : ℂ, ub1 (x * mX 1 0 (t • E) 1) = ub1 x`. Introduce `t`. Rewrite using `[inverse_first_block_mul_unipotent_domain x ⟨hdx, hd1, hd2, hdb⟩ 0 (t • E) (by simp) (by simp)]`.

Simplify using the standard rewrite rules. Establish `hg : (fun t : ℂ => fV (n` using `n) (m : ℤ) 0 (x + t • (x * WD 0 E))) = fun t : ℂ => (u1 x + t • (u2 x * E)).det ^ ((m : ℤ) - n) * (ub1 x).det ^ (-(n : ℤ)) := by`. Use function extensionality and compare the values at `t`. Rewrite using `[hline, fV, hu1, hub]`. Simplify using the standard rewrite rules.

Establish `hdiff : DifferentiableAt ℂ (fV (n` using `n) (m : ℤ) 0) x := ((contDiffOn_fV (m : ℤ) 0).contDiffAt (isOpen_dom.mem_nhds ⟨hdx, hd1, hd2, hdb⟩)).differentiableAt (by simp)`. Establish `hL` using `((hasDerivAt_id (0 : ℂ)).smul_const (x * WD 0 E)).const_add x`. Simplify using `only [id, one_smul] at hL`. Establish `h1` using `hdiff.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℂ) hL (by simp)`. Establish `hdet` using `hasDerivAt_det_add (u1 x) (u2 x * E) (isUnit_iff_ne_zero.mpr hd1)`.

Establish `h2` using `((hasDerivAt_zpow ((m : ℤ) - n) ((u1 x + (0 : ℂ) • (u2 x * E)).det) (Or.inl (by simpa using hd1))).comp (0 : ℂ) hdet).mul_const ((ub1 x).det ^ (-(n : ℤ)))`. Establish `h1' : HasDerivAt (fun t : ℂ => fV (n` using `n) (m : ℤ) 0 (x + t • (x * WD 0 E))) (fderiv ℂ (fV (n := n) (m : ℤ) 0) x (x * WD 0 E)) 0 := h1`. Rewrite `h1'` using `[hg]`. Rewrite using `[h1'.unique h2]`. Simplify using `only [zero_smul, add_zero]`.

Rewrite using `[← Matrix.mul_assoc, hE, trace_mul_single, fV, zpow_sub_one₀ hd1]`. Simplify using `only [zpow_zero, mul_one, MulOpposite.op_one, one_smul, Int.cast_sub, Int.cast_natCast]`. Clear the denominators using the available nonvanishing facts.
-/
theorem fderiv_fV_R (m : ℕ) (x : M2 n) (hx : x ∈ Dom n) (a0 b0 : Fin n) :
    fderiv ℂ (fV (n := n) (m : ℤ) 0) x (x * WD 0 (Matrix.single a0 b0 1)) =
      ((m : ℂ) - n) * ((u1 x)⁻¹ * u2 x) b0 a0 * fV (m : ℤ) 0 x := by
  set E : Matrix (Fin n) (Fin n) ℂ := Matrix.single a0 b0 1 with hE
  obtain ⟨hdx, hd1, hd2, hdb⟩ := hx
  have hCi : (Cm n)⁻¹ = Cmi n := Matrix.inv_eq_left_inv cmi_mul_cm
  have hCC : Cm n * Cmi n = 1 := mul_eq_one_comm.mp cmi_mul_cm
  have hline : ∀ t : ℂ, x + t • (x * WD 0 E) = x * mX 1 0 (t • E) 1 := by
    intro t
    have h : mX 1 0 (t • E) 1 = 1 + t • WD 0 E := by
      simp only [mX, WD, hCi]
      have h' : (fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) 0 (t • E) 1 : M2 n) =
          1 + t • (fromBlocks 0 0 E 0 : M2 n) := by
        rw [← fromBlocks_one, fromBlocks_smul, fromBlocks_add]
        simp
      rw [h', Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hCC, Matrix.mul_smul, Matrix.smul_mul]
    rw [h, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]
  have hu1 : ∀ t : ℂ, u1 (x * mX 1 0 (t • E) 1) = u1 x + t • (u2 x * E) := by
    intro t
    rw [u1_eq_toBlocks₂₁_mul_Cm, u1_eq_toBlocks₂₁_mul_Cm x, u2_eq_toBlocks₂₂_mul_Cm x, mX, hCi]
    have h : x * (Cm n * fromBlocks 1 0 (t • E) 1 * Cmi n) * Cm n =
        (x * Cm n) * fromBlocks 1 0 (t • E) 1 := by
      simp only [Matrix.mul_assoc, cmi_mul_cm, Matrix.mul_one]
    rw [h]
    conv_lhs => rw [← fromBlocks_toBlocks (x * Cm n)]
    rw [fromBlocks_multiply]
    simp [Matrix.mul_smul]
  have hub : ∀ t : ℂ, ub1 (x * mX 1 0 (t • E) 1) = ub1 x := by
    intro t
    rw [inverse_first_block_mul_unipotent_domain x ⟨hdx, hd1, hd2, hdb⟩ 0 (t • E) (by simp) (by simp)]
    simp
  have hg : (fun t : ℂ => fV (n := n) (m : ℤ) 0 (x + t • (x * WD 0 E))) =
      fun t : ℂ => (u1 x + t • (u2 x * E)).det ^ ((m : ℤ) - n) * (ub1 x).det ^ (-(n : ℤ)) := by
    funext t
    rw [hline, fV, hu1, hub]
    simp
  have hdiff : DifferentiableAt ℂ (fV (n := n) (m : ℤ) 0) x :=
    ((contDiffOn_fV (m : ℤ) 0).contDiffAt (isOpen_dom.mem_nhds ⟨hdx, hd1, hd2, hdb⟩)).differentiableAt
      (by simp)
  have hL := ((hasDerivAt_id (0 : ℂ)).smul_const (x * WD 0 E)).const_add x
  simp only [id, one_smul] at hL
  have h1 := hdiff.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℂ) hL (by simp)
  have hdet := hasDerivAt_det_add (u1 x) (u2 x * E) (isUnit_iff_ne_zero.mpr hd1)
  have h2 := ((hasDerivAt_zpow ((m : ℤ) - n) ((u1 x + (0 : ℂ) • (u2 x * E)).det)
    (Or.inl (by simpa using hd1))).comp (0 : ℂ) hdet).mul_const ((ub1 x).det ^ (-(n : ℤ)))
  have h1' : HasDerivAt (fun t : ℂ => fV (n := n) (m : ℤ) 0 (x + t • (x * WD 0 E)))
      (fderiv ℂ (fV (n := n) (m : ℤ) 0) x (x * WD 0 E)) 0 := h1
  rw [hg] at h1'
  rw [h1'.unique h2]
  simp only [zero_smul, add_zero]
  rw [← Matrix.mul_assoc, hE, trace_mul_single, fV, zpow_sub_one₀ hd1]
  simp only [zpow_zero, mul_one, MulOpposite.op_one, one_smul, Int.cast_sub, Int.cast_natCast]
  field_simp

end PositivityTheory.Rg.Sw.HSt
