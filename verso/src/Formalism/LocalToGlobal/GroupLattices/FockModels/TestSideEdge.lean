import Formalism.LocalToGlobal.GroupLattices.FockModels.ElementaryDivisorBasis
import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.EdgePlane

noncomputable section

namespace Formalism.L2.G.Model

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.G.LatticeSystems Formalism.MainNotions.Pf14

section
variable {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq] {k : ℕ}

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce `x hx`. Establish `h1 : ∀ c, ∃ z : W, algebraMap W Qq z = ∑ i, x i * g i c` using `fun c => hx (fun i => g i c) (Submodule.subset_span ⟨c, rfl⟩)`. Use `choose z hz using h1`. Use `(mem_colSpan _ _).2 ⟨z, ?_⟩` and prove the remaining obligations.

Establish `h2 : (fun c => algebraMap W Qq (z c)) = Matrix.vecMul x g`. Use function extensionality and compare the values at `c`. Rewrite using `[hz c]`. Both sides reduce to the same expression. Rewrite using `[h2, Matrix.mulVec_transpose, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv g hg, Matrix.vecMul_one]`.

Introduce `x hx y hy`. Take `⟨a, rfl⟩` from `(mem_colSpan _ _).1 hx`. Take `⟨b, rfl⟩` from `(mem_colSpan _ _).1 hy`. Use `⟨∑ c, a c * b c, ?_⟩` and prove the remaining obligations. Establish `h1 : ∑ i, ((g⁻¹).transpose.mulVec fun c => algebraMap W Qq (a c)) i * (g.mulVec fun c => algebraMap W Qq (b c)) i = ((g⁻¹).transpose.mulVec fun c => algebraMap W Qq (a c)) ⬝ᵥ (g.mulVec fun c => algebraMap W Qq (b c))` using `rfl`.

Rewrite using `[h1, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul g hg, Matrix.vecMul_one]`. Simplify using `[dotProduct]`.
-/
theorem latDual_colSpan (g : Matrix (Fin k) (Fin k) Qq) (hg : IsUnit g.det) :
    latDual (colSpan W g) = colSpan W (g⁻¹).transpose := by
  apply le_antisymm
  · intro x hx
    have h1 : ∀ c, ∃ z : W, algebraMap W Qq z = ∑ i, x i * g i c :=
      fun c => hx (fun i => g i c) (Submodule.subset_span ⟨c, rfl⟩)
    choose z hz using h1
    refine (mem_colSpan _ _).2 ⟨z, ?_⟩
    have h2 : (fun c => algebraMap W Qq (z c)) = Matrix.vecMul x g := by
      funext c
      rw [hz c]
      rfl
    rw [h2, Matrix.mulVec_transpose, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv g hg, Matrix.vecMul_one]
  · intro x hx y hy
    obtain ⟨a, rfl⟩ := (mem_colSpan _ _).1 hx
    obtain ⟨b, rfl⟩ := (mem_colSpan _ _).1 hy
    refine ⟨∑ c, a c * b c, ?_⟩
    have h1 : ∑ i, ((g⁻¹).transpose.mulVec fun c => algebraMap W Qq (a c)) i *
        (g.mulVec fun c => algebraMap W Qq (b c)) i =
        ((g⁻¹).transpose.mulVec fun c => algebraMap W Qq (a c)) ⬝ᵥ (g.mulVec fun c => algebraMap W Qq (b c)) := rfl
    rw [h1, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul g hg,
      Matrix.vecMul_one]
    simp [dotProduct]

/- English proof (translation)
Rewrite using `[Matrix.det_transpose]`. Conclude with `(Matrix.isUnit_nonsing_inv_det_iff).2 hg`.
-/
theorem det_invT (g : Matrix (Fin k) (Fin k) Qq) (hg : IsUnit g.det) : IsUnit ((g⁻¹).transpose).det := by
  rw [Matrix.det_transpose]
  exact (Matrix.isUnit_nonsing_inv_det_iff).2 hg

/- English proof (translation)
Rewrite using `[← Matrix.transpose_nonsing_inv, Matrix.transpose_transpose, Matrix.nonsing_inv_nonsing_inv g hg]`.
-/
theorem invT_invT (g : Matrix (Fin k) (Fin k) Qq) (hg : IsUnit g.det) :
    (((g⁻¹).transpose)⁻¹).transpose = g := by
  rw [← Matrix.transpose_nonsing_inv, Matrix.transpose_transpose, Matrix.nonsing_inv_nonsing_inv g hg]

/- English proof (translation)
Take `⟨g, hg, rfl⟩` from `hL`. Rewrite using `[latDual_colSpan g hg, latDual_colSpan _ (det_invT g hg), invT_invT g hg]`.
-/
theorem latDual_latDual (L : Submodule W (Fin k → Qq)) (hL : IsLattice W L) : latDual (latDual L) = L := by
  obtain ⟨g, hg, rfl⟩ := hL
  rw [latDual_colSpan g hg, latDual_colSpan _ (det_invT g hg), invT_invT g hg]

def dE (k r : ℕ) (c : Qq) : Matrix (Fin k) (Fin k) Qq := Matrix.diagonal fun a => if a.val < r then c else 1

/- English proof (translation)
Unfold `lb_D dE`. Rewrite using `[Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Use `split_ifs`.

Conclude with `inv_mul_cancel₀ hc`. Simplify using the standard rewrite rules.
-/
theorem lb_D_dE (r : ℕ) (c : Qq) (hc : c ≠ 0) : lb_D k r c * dE k r c = 1 := by
  unfold lb_D dE
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs
  · exact inv_mul_cancel₀ hc
  · simp

/- English proof (translation)
Unfold `lb_D dE`. Rewrite using `[Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Use `split_ifs`.

Conclude with `mul_inv_cancel₀ hc`. Simplify using the standard rewrite rules.
-/
theorem dE_lb_D (r : ℕ) (c : Qq) (hc : c ≠ 0) : dE k r c * lb_D k r c = 1 := by
  unfold lb_D dE
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs
  · exact mul_inv_cancel₀ hc
  · simp

/- English proof (translation)
Establish `h1 : (g * lb_D k r c)⁻¹ = dE k r c * g⁻¹`. Apply `Matrix.inv_eq_right_inv` to reduce the goal to its premises. Rewrite using `[Matrix.mul_assoc, ← Matrix.mul_assoc (lb_D k r c), lb_D_dE r c hc, Matrix.one_mul, Matrix.mul_nonsing_inv g hg]`. Rewrite using `[h1, Matrix.transpose_mul]`. Use `congr 1`.

Conclude with `Matrix.diagonal_transpose _`.
-/
theorem invT_mul_D (g : Matrix (Fin k) (Fin k) Qq) (hg : IsUnit g.det) (r : ℕ) (c : Qq) (hc : c ≠ 0) :
    ((g * lb_D k r c)⁻¹).transpose = (g⁻¹).transpose * dE k r c := by
  have h1 : (g * lb_D k r c)⁻¹ = dE k r c * g⁻¹ := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (lb_D k r c), lb_D_dE r c hc, Matrix.one_mul,
      Matrix.mul_nonsing_inv g hg]
  rw [h1, Matrix.transpose_mul]
  congr 1
  exact Matrix.diagonal_transpose _

/- English proof (translation)
Take `⟨hg, hsrc, htgt⟩` from `h`. Establish `htgt' : e.tgt = colSpan W (g * lb_D k r (p : Qq))` using `htgt`. Establish `hgD : IsUnit (g * lb_D k r (p : Qq)).det`. Rewrite using `[Matrix.det_mul]`. Conclude with `hg.mul (lb_D_det _ _ _ hp)`.

Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← invT_mul_D g hg r _ hp]`. Conclude with `det_invT _ hgD`. Use `show latDual e.tgt = _`. Rewrite using `[htgt', latDual_colSpan _ hgD, invT_mul_D g hg r _ hp]`.

Use `show latDual e.src = colSpan W ((g⁻¹).transpose * dE k r (p : Qq) * lb_D k r (p : Qq))`. Rewrite using `[hsrc, latDual_colSpan g hg, Matrix.mul_assoc, dE_lb_D r _ hp, Matrix.mul_one]`.
-/
theorem dual_edgeBasis (p r : ℕ) (hp : (p : Qq) ≠ 0) (e : Edge W Qq k) (g : Matrix (Fin k) (Fin k) Qq)
    (h : IsEdgeBasis p r e g) : IsEdgeBasis p r e.dual ((g⁻¹).transpose * dE k r (p : Qq)) := by
  obtain ⟨hg, hsrc, htgt⟩ := h
  have htgt' : e.tgt = colSpan W (g * lb_D k r (p : Qq)) := htgt
  have hgD : IsUnit (g * lb_D k r (p : Qq)).det := by
    rw [Matrix.det_mul]; exact hg.mul (lb_D_det _ _ _ hp)
  refine ⟨?_, ?_, ?_⟩
  · rw [← invT_mul_D g hg r _ hp]
    exact det_invT _ hgD
  · show latDual e.tgt = _
    rw [htgt', latDual_colSpan _ hgD, invT_mul_D g hg r _ hp]
  · show latDual e.src = colSpan W ((g⁻¹).transpose * dE k r (p : Qq) * lb_D k r (p : Qq))
    rw [hsrc, latDual_colSpan g hg, Matrix.mul_assoc, dE_lb_D r _ hp, Matrix.mul_one]

end

section
variable {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
  [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}

/- English proof (translation)
The claim follows from `restEdgeBasis (mkG h m r (fun _ _ => 0) (fun _ _ _ _ => le_rfl)) (0 : Fin 1) e he`.
-/
theorem edgeBasis (h : HidaSetting p n' W Qq O Kf ι σ j w) (m r : ℕ) (e : Edge W Qq (m + 1))
    (he : IsEdge p n' r e) : ∃ g : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq, IsEdgeBasis p r e g :=
  restEdgeBasis (mkG h m r (fun _ _ => 0) (fun _ _ _ _ => le_rfl)) (0 : Fin 1) e he

/- English proof (translation)
Introduce `h0`. Establish `h1 : (p : Kf) = 0`. Use `congrArg ι h0` as an intermediate fact. Simplify using `using this`. Rewrite `h1` using `[p_eq h]`.

Conclude with `w_ne h ((pow_eq_zero_iff two_ne_zero).1 h1)`.
-/
theorem pQ_ne (h : HidaSetting p n' W Qq O Kf ι σ j w) : (p : Qq) ≠ 0 := by
  intro h0
  have h1 : (p : Kf) = 0 := by
    have := congrArg ι h0
    simpa using this
  rw [p_eq h] at h1
  exact w_ne h ((pow_eq_zero_iff two_ne_zero).1 h1)

/- English proof (translation)
The claim follows from `h.p_unif.ne_zero`.
-/
theorem pW_ne (h : HidaSetting p n' W Qq O Kf ι σ j w) : (p : W) ≠ 0 := h.p_unif.ne_zero

/- English proof (translation)
Assume the negation of the conclusion as `hr`. Establish `hr' : m + 1 < r` using `Nat.lt_of_not_le hr`. Take `⟨g, hg, hsrc, htgt⟩` from `edgeBasis h m r e he`. Use `h.frac_alt` as an intermediate fact. Establish `hb : IsEdgeBasis p (m + 1) e g`.

Use `⟨hg, hsrc, ?_⟩` and prove the remaining obligations. Rewrite using `[htgt]`. Use `congr 3`. Use function extensionality and compare the values at `c`. Establish `h1 : c.val < r` using `lt_trans c.isLt hr'`.

Simplify using `[h1, c.isLt]`. Establish `he2` using `isEdge_of_basis p n' (m + 1) (pW_ne h) h.res_card le_rfl e g hb`. Establish `h3` using `he.2.2.2.2`. Rewrite `h3` using `[he2.2.2.2.2]`. Establish `h4` using `Nat.pow_right_injective h.prime.two_le h3`.

Establish `h5 : 0 < n'` using `lt_of_lt_of_le two_pos h.two_le`. Establish `h6` using `Nat.eq_of_mul_eq_mul_left h5 h4`. Use linear arithmetic over natural numbers and integers.
-/
theorem edge_r_le (h : HidaSetting p n' W Qq O Kf ι σ j w) (m r : ℕ) (e : Edge W Qq (m + 1))
    (he : IsEdge p n' r e) : r ≤ m + 1 := by
  by_contra hr
  have hr' : m + 1 < r := Nat.lt_of_not_le hr
  obtain ⟨g, hg, hsrc, htgt⟩ := edgeBasis h m r e he
  have := h.frac_alt
  have hb : IsEdgeBasis p (m + 1) e g := by
    refine ⟨hg, hsrc, ?_⟩
    rw [htgt]
    congr 3
    funext c
    have h1 : c.val < r := lt_trans c.isLt hr'
    simp [h1, c.isLt]
  have he2 := isEdge_of_basis p n' (m + 1) (pW_ne h) h.res_card le_rfl e g hb
  have h3 := he.2.2.2.2
  rw [he2.2.2.2.2] at h3
  have h4 := Nat.pow_right_injective h.prime.two_le h3
  have h5 : 0 < n' := lt_of_lt_of_le two_pos h.two_le
  have h6 := Nat.eq_of_mul_eq_mul_left h5 h4
  omega

/- English proof (translation)
Take `⟨g, hg⟩` from `edgeBasis h m r e he`. Use `h.frac_alt` as an intermediate fact. Use `⟨isEdge_of_basis p n' r (pW_ne h) h.res_card (edge_r_le h m r e he) e.dual _ (dual_edgeBasis p r (pQ_ne h) e g hg), ?_⟩` and prove the remaining obligations. Consider the cases of `e with`. Consider the case `mk src tgt => show Edge.mk (latDual (latDual src)) (latDual (latDual tgt)) = Edge.mk src tgt`.

Rewrite using `[latDual_latDual src he.1, latDual_latDual tgt he.2.1]`.
-/
theorem dual_edge (h : HidaSetting p n' W Qq O Kf ι σ j w) (m r : ℕ) (e : Edge W Qq (m + 1))
    (he : IsEdge p n' r e) : IsEdge p n' r e.dual ∧ e.dual.dual = e := by
  obtain ⟨g, hg⟩ := edgeBasis h m r e he
  have := h.frac_alt
  refine ⟨isEdge_of_basis p n' r (pW_ne h) h.res_card (edge_r_le h m r e he) e.dual _
    (dual_edgeBasis p r (pQ_ne h) e g hg), ?_⟩
  cases e with
  | mk src tgt =>
    show Edge.mk (latDual (latDual src)) (latDual (latDual tgt)) = Edge.mk src tgt
    rw [latDual_latDual src he.1, latDual_latDual tgt he.2.1]

end

end Formalism.L2.G.Model
