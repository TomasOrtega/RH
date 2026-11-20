import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.NonvanishingNearMaximumHolds

namespace ReciprocityTheory.ChartRestriction.G.FD.FlagSpanBounds

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

/- English proof (translation)
Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨a, rfl⟩`. Establish `hcol : col (M * N) (Fin.castLE hp a) = ∑ j : Fin r, N j (Fin.castLE hp a) • col M j`. Use function extensionality and compare the values at `i`. Simplify using `only [col, Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`.

Conclude with `Finset.sum_congr rfl (fun j _ => mul_comm _ _)`. Use `show col (M * N) (Fin.castLE hp a) ∈ Submodule.span ℂ (Set.range fun a : Fin p => col M (Fin.castLE hp a))`. Rewrite using `[hcol]`. Use `Submodule.sum_mem _ (fun j _ => ?_)` and prove the remaining obligations. Distinguish the cases in `hj : (j : ℕ) < p`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨j, hj⟩, congrArg (col M) (Fin.ext rfl)⟩)`. Establish `hlt : Fin.castLE hp a < j` using `Fin.lt_iff_val_lt_val.mpr (by show (a : ℕ) < j; omega)`. Establish `h0 : N j (Fin.castLE hp a) = 0` using `hN hlt`. Rewrite using `[h0, zero_smul]`. Conclude with `Submodule.zero_mem _`.
-/
lemma span_le_of_upper (p : ℕ) (hp : p ≤ r) (M N : Matrix (Fin r) (Fin r) ℂ) (hN : N.BlockTriangular id) :
    Submodule.span ℂ (Set.range fun a : Fin p => col (M * N) (Fin.castLE hp a)) ≤
      Submodule.span ℂ (Set.range fun a : Fin p => col M (Fin.castLE hp a)) := by
  rw [Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  have hcol : col (M * N) (Fin.castLE hp a) = ∑ j : Fin r, N j (Fin.castLE hp a) • col M j := by
    funext i
    simp only [col, Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  show col (M * N) (Fin.castLE hp a) ∈ Submodule.span ℂ (Set.range fun a : Fin p => col M (Fin.castLE hp a))
  rw [hcol]
  refine Submodule.sum_mem _ (fun j _ => ?_)
  by_cases hj : (j : ℕ) < p
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨j, hj⟩, congrArg (col M) (Fin.ext rfl)⟩)
  · have hlt : Fin.castLE hp a < j := Fin.lt_iff_val_lt_val.mpr (by show (a : ℕ) < j; omega)
    have h0 : N j (Fin.castLE hp a) = 0 := hN hlt
    rw [h0, zero_smul]
    exact Submodule.zero_mem _

variable (X : Data E r)

/- English proof (translation)
Unfold `Data.SameFlag`. Unfold `Bor at hb`. Rewrite `hb` using `[Set.mem_setOf_eq]`. Introduce `τ`. Take `⟨hdet, htri⟩` from `hb τ`.

Establish `hmul : mat (rmul z b) τ = mat z τ * mat b τ` using `by first`. Consider the case `rfl`. Consider the case `(unfold rmul mat; rfl)`. Consider the case `(ext i j; simp [rmul, mat, Matrix.mul_apply])`. Establish `hT : (mat b τ).BlockTriangular id` using `fun a c h => by first`.

Consider the case `exact htri a c h`. Consider the case `(simp only [mat]; exact htri a c h)`. Use `haveI : Invertible (mat b τ).det := invertibleOfNonzero hdet`. Use `haveI : Invertible (mat b τ) := Matrix.invertibleOfDetInvertible _`. Apply `le_antisymm` to reduce the goal to its premises.

Establish `hinv : mat z τ = mat (rmul z b) τ * (mat b τ)⁻¹`. Rewrite using `[hmul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet), Matrix.mul_one]`. Rewrite using `[hinv]`. Conclude with `span_le_of_upper _ _ _ _ (Matrix.blockTriangular_inv_of_blockTriangular hT)`. Rewrite using `[hmul]`.

Conclude with `span_le_of_upper _ _ _ _ hT`.
-/
lemma sameFlag_rmul (z : Frame X.Ψ r) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) : X.SameFlag z (rmul z b) := by
  unfold Data.SameFlag
  unfold Bor at hb
  rw [Set.mem_setOf_eq] at hb
  intro τ
  obtain ⟨hdet, htri⟩ := hb τ
  have hmul : mat (rmul z b) τ = mat z τ * mat b τ := by
    first
    | rfl
    | (unfold rmul mat; rfl)
    | (ext i j; simp [rmul, mat, Matrix.mul_apply])
  have hT : (mat b τ).BlockTriangular id := fun a c h => by
    first
    | exact htri a c h
    | (simp only [mat]; exact htri a c h)
  haveI : Invertible (mat b τ).det := invertibleOfNonzero hdet
  haveI : Invertible (mat b τ) := Matrix.invertibleOfDetInvertible _
  apply le_antisymm
  · have hinv : mat z τ = mat (rmul z b) τ * (mat b τ)⁻¹ := by
      rw [hmul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet), Matrix.mul_one]
    rw [hinv]
    exact span_le_of_upper _ _ _ _ (Matrix.blockTriangular_inv_of_blockTriangular hT)
  · rw [hmul]
    exact span_le_of_upper _ _ _ _ hT

/- English proof (translation)
Distinguish the cases in `hv : v = 0`. Substitute `hv` using the available equality. Simplify using `[Data.maj, Data.posPart, hermC]`. Conclude with `(X.maj_pos hx τ hv).le`.
-/
lemma maj_nonneg {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (v : Fin r → ℂ) : 0 ≤ X.maj x τ v := by
  by_cases hv : v = 0
  · subst hv
    simp [Data.maj, Data.posPart, hermC]
  · exact (X.maj_pos hx τ hv).le

/- English proof (translation)
Unfold `frameRadius`. Establish `hwr : 1 ≤ w * (r : ℝ)`. Establish `: (1 : ℝ) ≤ r` using `by exact_mod_cast hr`. Use the polynomial consequences of the given equalities and inequalities. Establish `hs : 1 ≤ √(w * r)` using `by first`.

Consider the case `exact Real.one_le_sqrt.mpr hwr`. Consider the case `exact (Real.sqrt_one).symm ▸ Real.sqrt_le_sqrt hwr`. Prove the components needed by the constructor for the conclusion. Apply `div_pos one_pos` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion.

Conclude with `one_div_le_one_div_of_le (by norm_num) (by linarith)`.
-/
lemma rho_pos {w : ℝ} (hw1 : 1 ≤ w) (hr : 0 < r) : 0 < frameRadius w r ∧ frameRadius w r ≤ 1 / 10 := by
  unfold frameRadius
  have hwr : 1 ≤ w * (r : ℝ) := by
    have : (1 : ℝ) ≤ r := by exact_mod_cast hr
    nlinarith
  have hs : 1 ≤ √(w * r) := by
    first
    | exact Real.one_le_sqrt.mpr hwr
    | exact (Real.sqrt_one).symm ▸ Real.sqrt_le_sqrt hwr
  constructor
  · apply div_pos one_pos
    linarith
  · exact one_div_le_one_div_of_le (by norm_num) (by linarith)

end

end ReciprocityTheory.ChartRestriction.G.FD.FlagSpanBounds

namespace ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

/- English proof (translation)
Introduce `r X la P z0 laStar w hP hz0 hmax hpos hw hw1 hr hl0 hl1 hMAX`. Take `⟨b, hb, ho⟩` from `(orthonormalFlagTranslate_holds r X.toData).1 z0 hz0`. Establish `hx0` using `OrthogonalFrameDomain.rmul_mem_dom X.toData hz0 hb`. Establish `hsf : X.SameFlag z0 (rmul z0 b)` using `FlagSpanBounds.sameFlag_rmul X.toData z0 hb`. Take `⟨hρ0, hρ10⟩` from `FlagSpanBounds.rho_pos (r := r) hw1 hr`.

Take `⟨lam, Z, hZ, hlam⟩` from `h41a r X z0 (rmul z0 b) laStar (frameRadius w r) hz0 hx0 ho hsf hl0 hl1 hρ0 (by linarith) hMAX`. Establish `hZρ : X.zN Z ≤ frameRadius w r` using `by linarith`. Use `⟨X.xZ (rmul z0 b) Z, lam, OrthonormalChartBounds.xZ_mem_dom X.toData hx0 ho (by linarith), hlam, nonvanishingNearMaximum_holds r X.toData la P z0 (rmul z0 b) w hP hz0 ho ⟨b, hb, rfl⟩ hmax hpos hw hw1 hr Z hZ, fun τ v => ?_⟩` and prove the remaining obligations. Establish `hm` using `(((h6p1 r X.toData (rmul z0 b) hx0 ho (frameRadius w r) hρ0 hρ10).1 Z hZρ).2.2 τ v).2`. Establish `hmeq` using `((orthonormalFlagTranslate_holds r X.toData).2.2 z0 hz0 _ hx0 hsf).2`.

Rewrite `hm` using `[← hmeq]`. Establish `hnn` using `FlagSpanBounds.maj_nonneg X.toData hz0 τ v`. Establish `hq : (1 + frameRadius w r) / (1 - frameRadius w r) ≤ 2`. Rewrite using `[div_le_iff₀ (by linarith)]`. Combine the linear equalities and inequalities to obtain the conclusion.

Conclude with `hm.trans (mul_le_mul_of_nonneg_right hq hnn)`.
-/
theorem frameAtMaximum_of_lower_bound (h41a : LatticeBoundAtMaximum (E := E)) (h6p1 : OrthonormalChartNormControl (E := E)) :
    FrameAtMaximum (E := E) := by
  intro r X la P z0 laStar w hP hz0 hmax hpos hw hw1 hr hl0 hl1 hMAX
  obtain ⟨b, hb, ho⟩ := (orthonormalFlagTranslate_holds r X.toData).1 z0 hz0
  have hx0 := OrthogonalFrameDomain.rmul_mem_dom X.toData hz0 hb
  have hsf : X.SameFlag z0 (rmul z0 b) := FlagSpanBounds.sameFlag_rmul X.toData z0 hb
  obtain ⟨hρ0, hρ10⟩ := FlagSpanBounds.rho_pos (r := r) hw1 hr
  obtain ⟨lam, Z, hZ, hlam⟩ :=
    h41a r X z0 (rmul z0 b) laStar (frameRadius w r) hz0 hx0 ho hsf hl0 hl1 hρ0 (by linarith) hMAX
  have hZρ : X.zN Z ≤ frameRadius w r := by linarith
  refine ⟨X.xZ (rmul z0 b) Z, lam, OrthonormalChartBounds.xZ_mem_dom X.toData hx0 ho (by linarith), hlam,
    nonvanishingNearMaximum_holds r X.toData la P z0 (rmul z0 b) w hP hz0 ho ⟨b, hb, rfl⟩ hmax hpos hw hw1 hr Z hZ,
    fun τ v => ?_⟩
  have hm := (((h6p1 r X.toData (rmul z0 b) hx0 ho (frameRadius w r) hρ0 hρ10).1 Z hZρ).2.2 τ v).2
  have hmeq := ((orthonormalFlagTranslate_holds r X.toData).2.2 z0 hz0 _ hx0 hsf).2
  rw [← hmeq] at hm
  have hnn := FlagSpanBounds.maj_nonneg X.toData hz0 τ v
  have hq : (1 + frameRadius w r) / (1 - frameRadius w r) ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  exact hm.trans (mul_le_mul_of_nonneg_right hq hnn)

end ReciprocityTheory.ChartRestriction.G.FD
