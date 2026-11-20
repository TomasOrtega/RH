import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.CrossOpEigGap

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section OneB

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M} {lam : Fin n → ℝ}

/- English proof (translation)
Use `haveI : FiniteDimensional ℂ (ncV ε V 1) := finiteDimensional_ncV hV.1 1`. Establish `hstab : ∀ y ∈ ncV ε V 1, crossOp ε E 1 0 y ∈ ncV ε V 1` using `fun y hy => crossOp_mem_ncV hV.2.1 1 0 hy`. Set `T : Module.End ℂ (ncV ε V 1)` to `(crossOp ε E 1 0).restrict hstab`. Establish `hT : T.IsSymmetric` using `fun u v => crossOp_symm hU 1 0 u v`. Establish `htop : (⨆ μ, Module.End.eigenspace T μ) = ⊤` using `Submodule.orthogonal_eq_bot_iff.1 hT.orthogonalComplement_iSup_eigenspaces_eq_bot`.

Establish `hx' : (⟨x, hx⟩ : ncV ε V 1) ∈ ⨆ μ, Module.End.eigenspace T μ`. Rewrite using `[htop]`. Conclude with `Submodule.mem_top`. Use `Submodule.iSup_induction _ (motive := fun y : ncV ε V 1 => ∃ xm ∈ Wm ε E V, ∃ xp ∈ Wp ε E V, (y : Big n 1 M) = xm + xp) hx' ?_ ⟨0, zero_mem _, 0, zero_mem _, by simp⟩ ?_` and prove the remaining obligations. Introduce `μ y hy`.

Distinguish the cases in `hy0 : y = 0`. Conclude with `⟨0, zero_mem _, 0, zero_mem _, by simp [hy0]⟩`. Establish `hTy : T y = μ • y` using `Module.End.mem_eigenspace_iff.1 hy`. Establish `hev : Module.End.HasEigenvalue T μ` using `Module.End.hasEigenvalue_of_hasEigenvector ⟨hy, hy0⟩`. Establish `hμ : ((μ.re : ℝ) : ℂ) = μ` using `Complex.conj_eq_iff_re.1 (hT.conj_eigenvalue_eq_self hev)`.

Establish `hCy : crossOp ε E 1 0 y = ((μ.re : ℝ) : ℂ) • (y : Big n 1 M)`. Rewrite using `[hμ]`. Use `congrArg Subtype.val hTy` as an intermediate fact. Simplify `this` using `[T]`. Establish `hyN : (y : Big n 1 M) ∈ Module.End.eigenspace (crossOp ε E 1 0) ((μ.re : ℝ) : ℂ) ⊓ ncV ε V 1` using `⟨Module.End.mem_eigenspace_iff.2 hCy, y.2⟩`.

Establish `hy0' : (y : Big n 1 M) ≠ 0` using `fun h => hy0 (Subtype.ext h)`. Break down `crossOp_eig_gap hE hU hV hmono hh hbig hyN hy0' with ⟨h1, h2⟩ | ⟨h1, h2⟩` into its components or cases. Use `⟨0, zero_mem _, y, ?_, by simp⟩` and prove the remaining obligations. Unfold `Wp`. Conclude with `Submodule.mem_iSup_of_mem μ.re (Submodule.mem_iSup_of_mem (by linarith) hyN)`.

Use `⟨y, ?_, 0, zero_mem _, by simp⟩` and prove the remaining obligations. Unfold `Wm`. Conclude with `Submodule.mem_iSup_of_mem μ.re (Submodule.mem_iSup_of_mem (by linarith) hyN)`. Introduce and unpack `y z ⟨a, ha, b, hb, hy⟩ ⟨c, hc, d, hd, hz⟩`. Use `⟨a + c, add_mem ha hc, b + d, add_mem hb hd, ?_⟩` and prove the remaining obligations.

Rewrite using `[Submodule.coe_add, hy, hz]`. Normalize the expressions using the abelian group laws.
-/
theorem ncV_one_decomp (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hmono : StrictAnti lam) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hbig : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h) {x : Big n 1 M} (hx : x ∈ ncV ε V 1) :
    ∃ xm ∈ Wm ε E V, ∃ xp ∈ Wp ε E V, x = xm + xp := by
  haveI : FiniteDimensional ℂ (ncV ε V 1) := finiteDimensional_ncV hV.1 1
  have hstab : ∀ y ∈ ncV ε V 1, crossOp ε E 1 0 y ∈ ncV ε V 1 :=
    fun y hy => crossOp_mem_ncV hV.2.1 1 0 hy
  let T : Module.End ℂ (ncV ε V 1) := (crossOp ε E 1 0).restrict hstab
  have hT : T.IsSymmetric := fun u v => crossOp_symm hU 1 0 u v
  have htop : (⨆ μ, Module.End.eigenspace T μ) = ⊤ :=
    Submodule.orthogonal_eq_bot_iff.1 hT.orthogonalComplement_iSup_eigenspaces_eq_bot
  have hx' : (⟨x, hx⟩ : ncV ε V 1) ∈ ⨆ μ, Module.End.eigenspace T μ := by
    rw [htop]; exact Submodule.mem_top
  refine Submodule.iSup_induction _
    (motive := fun y : ncV ε V 1 => ∃ xm ∈ Wm ε E V, ∃ xp ∈ Wp ε E V, (y : Big n 1 M) = xm + xp)
    hx' ?_ ⟨0, zero_mem _, 0, zero_mem _, by simp⟩ ?_
  · intro μ y hy
    by_cases hy0 : y = 0
    · exact ⟨0, zero_mem _, 0, zero_mem _, by simp [hy0]⟩
    have hTy : T y = μ • y := Module.End.mem_eigenspace_iff.1 hy
    have hev : Module.End.HasEigenvalue T μ := Module.End.hasEigenvalue_of_hasEigenvector ⟨hy, hy0⟩
    have hμ : ((μ.re : ℝ) : ℂ) = μ := Complex.conj_eq_iff_re.1 (hT.conj_eigenvalue_eq_self hev)
    have hCy : crossOp ε E 1 0 y = ((μ.re : ℝ) : ℂ) • (y : Big n 1 M) := by
      rw [hμ]
      have := congrArg Subtype.val hTy
      simpa [T] using this
    have hyN : (y : Big n 1 M) ∈ Module.End.eigenspace (crossOp ε E 1 0) ((μ.re : ℝ) : ℂ) ⊓ ncV ε V 1 :=
      ⟨Module.End.mem_eigenspace_iff.2 hCy, y.2⟩
    have hy0' : (y : Big n 1 M) ≠ 0 := fun h => hy0 (Subtype.ext h)
    rcases crossOp_eig_gap hE hU hV hmono hh hbig hyN hy0' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine ⟨0, zero_mem _, y, ?_, by simp⟩
      unfold Wp
      exact Submodule.mem_iSup_of_mem μ.re (Submodule.mem_iSup_of_mem (by linarith) hyN)
    · refine ⟨y, ?_, 0, zero_mem _, by simp⟩
      unfold Wm
      exact Submodule.mem_iSup_of_mem μ.re (Submodule.mem_iSup_of_mem (by linarith) hyN)
  · rintro y z ⟨a, ha, b, hb, hy⟩ ⟨c, hc, d, hd, hz⟩
    refine ⟨a + c, add_mem ha hc, b + d, add_mem hb hd, ?_⟩
    rw [Submodule.coe_add, hy, hz]
    abel

/- English proof (translation)
Establish `hxN` using `Wm_le_ncV hx`. Take `⟨r, s, hrs, hν', hC2⟩` from `crossOp_khw hE hU hV hxN hx0 hν`. Establish `hne : r ≠ s` using `fun h => hrs (h ▸ rfl)`. Break down `lt_or_gt_of_ne hne with hlt | hlt` into its components or cases. It suffices to derive a contradiction.

Establish `hgap` using `(gap_gt hrs hbig).2`. Establish `hcpos` using `crossVal_pos hmono hh hlt hrs`. Rewrite `hcpos` using `[← hν']`. Establish `hCx : crossOp ε E 1 0 x = (((casValK ε ν - n - casValK ε (lowK ε lam)) / 2 : ℝ) : ℂ) • x`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[smul_smul]`. Evaluate the numerical expressions. Use `_ = _ := by rw [hC2, smul_smul]; congr 1; push_cast; ring`. Establish `horth : ∀ y ∈ Wm ε E V, inner ℂ y x = 0`. Introduce `y hy`.

Unfold `Wm at hy`. Use `Submodule.iSup_induction _ (motive := fun y => inner ℂ y x = 0) hy ?_ (inner_zero_left _) (fun a b ha hb => by rw [inner_add_left, ha, hb, add_zero])` and prove the remaining obligations. Introduce `θ y hy`. Use `Submodule.iSup_induction _ (motive := fun y => inner ℂ y x = 0) hy ?_ (inner_zero_left _) (fun a b ha hb => by rw [inner_add_left, ha, hb, add_zero])` and prove the remaining obligations. Introduce `hθ y hy`.

Conclude with `inner_crossOp_eig_eq_zero hU (ne_of_lt (by linarith)) (Module.End.mem_eigenspace_iff.1 hy.1) hCx`. Conclude with `hx0 (inner_self_eq_zero.1 (horth x hx))`. Use `⟨s, r, hlt, fun h => hrs h.symm, ?_⟩` and prove the remaining obligations. Rewrite using `[hν']`. Unfold `root`.

Normalize the expressions using the abelian group laws.
-/
theorem Wm_khw (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hmono : StrictAnti lam) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hbig : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h) {x : Big n 1 M} (hx : x ∈ Wm ε E V) (hx0 : x ≠ 0) {ν : Fin n → ℝ}
    (hν : IsKHWVec ε (bAct E 1) ν x) :
    ∃ a b : Fin n, a < b ∧ ε a ≠ ε b ∧ ν = lowK ε lam - root a b := by
  have hxN := Wm_le_ncV hx
  obtain ⟨r, s, hrs, hν', hC2⟩ := crossOp_khw hE hU hV hxN hx0 hν
  have hne : r ≠ s := fun h => hrs (h ▸ rfl)
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exfalso
    have hgap := (gap_gt hrs hbig).2
    have hcpos := crossVal_pos hmono hh hlt hrs
    rw [← hν'] at hcpos
    have hCx : crossOp ε E 1 0 x =
        (((casValK ε ν - n - casValK ε (lowK ε lam)) / 2 : ℝ) : ℂ) • x := by
      calc crossOp ε E 1 0 x = (1 / 2 : ℂ) • ((2 : ℂ) • crossOp ε E 1 0 x) := by
            rw [smul_smul]; norm_num
        _ = _ := by rw [hC2, smul_smul]; congr 1; push_cast; ring
    have horth : ∀ y ∈ Wm ε E V, inner ℂ y x = 0 := by
      intro y hy
      unfold Wm at hy
      refine Submodule.iSup_induction _ (motive := fun y => inner ℂ y x = 0) hy ?_ (inner_zero_left _)
        (fun a b ha hb => by rw [inner_add_left, ha, hb, add_zero])
      intro θ y hy
      refine Submodule.iSup_induction _ (motive := fun y => inner ℂ y x = 0) hy ?_ (inner_zero_left _)
        (fun a b ha hb => by rw [inner_add_left, ha, hb, add_zero])
      intro hθ y hy
      exact inner_crossOp_eig_eq_zero hU (ne_of_lt (by linarith)) (Module.End.mem_eigenspace_iff.1 hy.1) hCx
    exact hx0 (inner_self_eq_zero.1 (horth x hx))
  · refine ⟨s, r, hlt, fun h => hrs h.symm, ?_⟩
    rw [hν']
    unfold root
    abel

/- English proof (translation)
Establish `key : ∀ s : Finset ℝ, ∀ x ∈ ⨆ θ ∈ s, ⨆ (_ : 0 < θ), Module.End.eigenspace (crossOp ε E 1 0) (θ : ℂ) ⊓ ncV ε V 1, (h - n + 1) * ‖x‖ ^ 2 ≤ RCLike.re (inner ℂ (crossOp ε E 1 0 x) x)`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => intro x hx`. Simplify using `at hx`.

Simplify using `[hx]`. Consider the case `insert a s has ih`. Introduce `x hx`. Rewrite `hx` using `[Finset.iSup_insert, Submodule.mem_sup]`. Take `⟨y, hy, z, hz, rfl⟩` from `hx`.

Distinguish the cases in `ha : 0 < a`. Rewrite `hy` using `[iSup_pos ha]`. Establish `hCy : crossOp ε E 1 0 y = (a : ℂ) • y` using `Module.End.mem_eigenspace_iff.1 hy.1`. Establish `horth : inner ℂ y z = 0`. Establish `hle : (⨆ θ ∈ s, ⨆ (_ : 0 < θ), Module.End.eigenspace (crossOp ε E 1 0) (θ : ℂ) ⊓ ncV ε V 1) ≤ (ℂ ∙ y)ᗮ`.

Use `iSup₂_le (fun θ hθ => iSup_le (fun _ => ?_))` and prove the remaining obligations. Introduce `w hw`. Rewrite using `[Submodule.mem_orthogonal_singleton_iff_inner_right]`. Conclude with `inner_crossOp_eig_eq_zero hU (by rintro rfl; exact has hθ) hCy (Module.End.mem_eigenspace_iff.1 hw.1)`. Conclude with `Submodule.mem_orthogonal_singleton_iff_inner_right.1 (hle hz)`.

Establish `horth' : inner ℂ z y = 0` using `by rw [inner_eq_zero_symm]; exact horth`. Establish `hnorm : ‖y + z‖ ^ 2 = ‖y‖ ^ 2 + ‖z‖ ^ 2`. Use `norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero y z horth` as an intermediate fact. Rewrite using `[sq, sq, sq]`. Conclude with `this`.

Establish `h1 : inner ℂ (crossOp ε E 1 0 z) y = 0`. Rewrite using `[crossOp_symm hU, hCy, inner_smul_right, horth', mul_zero]`. Establish `hre : RCLike.re (inner ℂ (crossOp ε E 1 0 (y + z)) (y + z)) = a * ‖y‖ ^ 2 + RCLike.re (inner ℂ (crossOp ε E 1 0 z) z)`. Rewrite using `[map_add, inner_add_left, inner_add_right, inner_add_right, h1, hCy, inner_smul_left, inner_smul_left, horth, inner_self_eq_norm_sq_to_K]`. Simplify using the standard rewrite rules.

Use `left`. Use `norm_cast`. Establish `hy' : (h - n + 1) * ‖y‖ ^ 2 ≤ a * ‖y‖ ^ 2`. Distinguish the cases in `hy0 : y = 0`. Simplify using `[hy0]`.

Break down `crossOp_eig_gap hE hU hV hmono hh hbig hy hy0 with ⟨-, h2⟩ | ⟨h2, h3⟩` into its components or cases. Conclude with `mul_le_mul_of_nonneg_right h2 (sq_nonneg _)`. It suffices to derive a contradiction. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hnorm, hre]`.

Use polynomial arithmetic with `[ih z hz, hy']`. Rewrite `hy` using `[iSup_neg ha]`. Rewrite using `[(Submodule.mem_bot ℂ).1 hy, zero_add]`. Conclude with `ih z hz`. Unfold `Wp at hx`.

Take `⟨s, hs⟩` from `Submodule.mem_iSup_iff_exists_finset.1 hx`. Use `key s x hs` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem Wp_bound (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hmono : StrictAnti lam) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hbig : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h) {x : Big n 1 M} (hx : x ∈ Wp ε E V) :
    2 * (h - n + 1) * ‖x‖ ^ 2 ≤ 2 * RCLike.re (inner ℂ (crossOp ε E 1 0 x) x) := by
  have key : ∀ s : Finset ℝ, ∀ x ∈ ⨆ θ ∈ s, ⨆ (_ : 0 < θ),
      Module.End.eigenspace (crossOp ε E 1 0) (θ : ℂ) ⊓ ncV ε V 1,
      (h - n + 1) * ‖x‖ ^ 2 ≤ RCLike.re (inner ℂ (crossOp ε E 1 0 x) x) := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro x hx; simp at hx; simp [hx]
    | insert a s has ih =>
      intro x hx
      rw [Finset.iSup_insert, Submodule.mem_sup] at hx
      obtain ⟨y, hy, z, hz, rfl⟩ := hx
      by_cases ha : 0 < a
      · rw [iSup_pos ha] at hy
        have hCy : crossOp ε E 1 0 y = (a : ℂ) • y := Module.End.mem_eigenspace_iff.1 hy.1
        have horth : inner ℂ y z = 0 := by
          have hle : (⨆ θ ∈ s, ⨆ (_ : 0 < θ),
              Module.End.eigenspace (crossOp ε E 1 0) (θ : ℂ) ⊓ ncV ε V 1) ≤ (ℂ ∙ y)ᗮ := by
            refine iSup₂_le (fun θ hθ => iSup_le (fun _ => ?_))
            intro w hw
            rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
            exact inner_crossOp_eig_eq_zero hU (by rintro rfl; exact has hθ) hCy
              (Module.End.mem_eigenspace_iff.1 hw.1)
          exact Submodule.mem_orthogonal_singleton_iff_inner_right.1 (hle hz)
        have horth' : inner ℂ z y = 0 := by rw [inner_eq_zero_symm]; exact horth
        have hnorm : ‖y + z‖ ^ 2 = ‖y‖ ^ 2 + ‖z‖ ^ 2 := by
          have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero y z horth
          rw [sq, sq, sq]; exact this
        have h1 : inner ℂ (crossOp ε E 1 0 z) y = 0 := by
          rw [crossOp_symm hU, hCy, inner_smul_right, horth', mul_zero]
        have hre : RCLike.re (inner ℂ (crossOp ε E 1 0 (y + z)) (y + z)) =
            a * ‖y‖ ^ 2 + RCLike.re (inner ℂ (crossOp ε E 1 0 z) z) := by
          rw [map_add, inner_add_left, inner_add_right, inner_add_right, h1, hCy, inner_smul_left,
            inner_smul_left, horth, inner_self_eq_norm_sq_to_K]
          simp
          left
          norm_cast
        have hy' : (h - n + 1) * ‖y‖ ^ 2 ≤ a * ‖y‖ ^ 2 := by
          by_cases hy0 : y = 0
          · simp [hy0]
          · rcases crossOp_eig_gap hE hU hV hmono hh hbig hy hy0 with ⟨-, h2⟩ | ⟨h2, h3⟩
            · exact mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
            · exfalso; linarith
        rw [hnorm, hre]
        nlinarith [ih z hz, hy']
      · rw [iSup_neg ha] at hy
        rw [(Submodule.mem_bot ℂ).1 hy, zero_add]
        exact ih z hz
  unfold Wp at hx
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.1 hx
  have := key s x hs
  linarith

end OneB

end ReciprocityTheory.ChartRestriction.DS
