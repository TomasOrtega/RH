import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HolDict.TorusLaw

variable {n : ℕ}

def cd (x : Mt n) (v : Fin n → ℂ) : Mt n := x * diagonal v * x⁻¹

/- English proof (translation)
Unfold `ReciprocityTheory.ChartRestriction.G.FD.sgn`. Apply the tactic sequence `split_ifs <;> norm_num`.
-/
lemma sgn_sq (q a : ℕ) : (-((ReciprocityTheory.ChartRestriction.G.FD.sgn q a : ℝ) : ℂ)) * (-((ReciprocityTheory.ChartRestriction.G.FD.sgn q a : ℝ) : ℂ)) = 1 := by
  unfold ReciprocityTheory.ChartRestriction.G.FD.sgn
  split_ifs <;> norm_num

/- English proof (translation)
Rewrite using `[det_diagonal]`. Use `Finset.prod_ne_zero_iff.mpr fun a _ => ?_` and prove the remaining obligations. Introduce `h0`. Establish `h1` using `sgn_sq q (a : ℕ)`. Rewrite `h1` using `[h0, zero_mul]`.

Conclude with `zero_ne_one h1`.
-/
private lemma det_diagonal_neg_sgn_ne_zero (q : ℕ) :
    (diagonal fun a : Fin n => -((ReciprocityTheory.ChartRestriction.G.FD.sgn q (a : ℕ) : ℝ) : ℂ)).det ≠ 0 := by
  rw [det_diagonal]
  refine Finset.prod_ne_zero_iff.mpr fun a _ => ?_
  intro h0
  have h1 := sgn_sq q (a : ℕ)
  rw [h0, zero_mul] at h1
  exact zero_ne_one h1

/- English proof (translation)
Establish `hd` using `det_diagonal_neg_sgn_ne_zero (n := n) q`. Rewrite `hd` using `[← h.2, det_mul, det_mul]`. Use `⟨isUnit_iff_ne_zero.mpr ?_, isUnit_iff_ne_zero.mpr ?_⟩` and prove the remaining obligations. Introduce `h0`. Apply `hd` to reduce the goal to its premises.

Rewrite using `[h0, mul_zero]`. Introduce `h0`. Apply `hd` to reduce the goal to its premises. Rewrite using `[h0, mul_zero, zero_mul]`.
-/
lemma units_of_orth {H x : Mt n} {q : ℕ} (h : OrthFr H q x) : IsUnit x.det ∧ IsUnit H.det := by
  have hd := det_diagonal_neg_sgn_ne_zero (n := n) q
  rw [← h.2, det_mul, det_mul] at hd
  refine ⟨isUnit_iff_ne_zero.mpr ?_, isUnit_iff_ne_zero.mpr ?_⟩
  · intro h0
    apply hd
    rw [h0, mul_zero]
  · intro h0
    apply hd
    rw [h0, mul_zero, zero_mul]

/- English proof (translation)
Unfold `cd`. Establish `hi : x⁻¹ * x = 1` using `nonsing_inv_mul x hx`. Rewrite using `[show v * v' = fun i => v i * v' i from rfl, ← diagonal_mul_diagonal]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc x⁻¹ x, hi, Matrix.one_mul]`.
-/
lemma cd_mul {x : Mt n} (hx : IsUnit x.det) (v v' : Fin n → ℂ) : cd x v * cd x v' = cd x (v * v') := by
  unfold cd
  have hi : x⁻¹ * x = 1 := nonsing_inv_mul x hx
  rw [show v * v' = fun i => v i * v' i from rfl, ← diagonal_mul_diagonal]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc x⁻¹ x, hi, Matrix.one_mul]

/- English proof (translation)
Unfold `cd`. Rewrite using `[diagonal_one, Matrix.mul_one, mul_nonsing_inv x hx]`.
-/
lemma cd_one {x : Mt n} (hx : IsUnit x.det) : cd x (fun _ => 1) = 1 := by
  unfold cd
  rw [diagonal_one, Matrix.mul_one, mul_nonsing_inv x hx]

/- English proof (translation)
Unfold `cd`. Rewrite using `[diagonal_smul, Matrix.mul_smul, Matrix.smul_mul]`.
-/
lemma cd_smul (x : Mt n) (c : ℂ) (v : Fin n → ℂ) : c • cd x v = cd x (c • v) := by
  unfold cd
  rw [diagonal_smul, Matrix.mul_smul, Matrix.smul_mul]

/- English proof (translation)
Unfold `cd`. Rewrite using `[show -v = fun i => -v i from rfl, ← diagonal_neg, Matrix.mul_neg, Matrix.neg_mul]`.
-/
lemma cd_neg (x : Mt n) (v : Fin n → ℂ) : cd x (-v) = -cd x v := by
  unfold cd
  rw [show -v = fun i => -v i from rfl, ← diagonal_neg, Matrix.mul_neg, Matrix.neg_mul]

/- English proof (translation)
Establish `hx : IsUnit x.det` using `(units_of_orth h).1`. Establish `e : (x⁻¹)ᴴ * (xᴴ * H * x) * x⁻¹ = (x⁻¹)ᴴ * (diagonal fun a : Fin n => -((ReciprocityTheory.ChartRestriction.G.FD.sgn q (a : ℕ) : ℝ) : ℂ)) * x⁻¹`. Rewrite using `[h.2]`. Establish `hH : H = (x⁻¹)ᴴ * (diagonal fun a : Fin n => -((ReciprocityTheory.ChartRestriction.G.FD.sgn q (a : ℕ) : ℝ) : ℂ)) * x⁻¹`. Rewrite using `[← e]`.

Establish `h1 : (x⁻¹)ᴴ * xᴴ = 1` using `by rw [← conjTranspose_mul, mul_nonsing_inv x hx, conjTranspose_one]`. Establish `h2 : x * x⁻¹ = 1` using `mul_nonsing_inv x hx`. Combine the equalities or inequalities in the displayed calculation. Establish `e1 : ∀ Z : Mt n, xᴴ * ((x⁻¹)ᴴ * Z) = Z`. Introduce `Z`.

Rewrite using `[← Matrix.mul_assoc, ← conjTranspose_mul, nonsing_inv_mul x hx, conjTranspose_one, Matrix.one_mul]`. Establish `e2 : ∀ Z : Mt n, x⁻¹ * (x * Z) = Z`. Introduce `Z`. Rewrite using `[← Matrix.mul_assoc, nonsing_inv_mul x hx, Matrix.one_mul]`. Rewrite using `[hH]`.

Unfold `cd`. Simplify using `only [conjTranspose_mul, diagonal_conjTranspose, Matrix.mul_assoc, e1, e2]`. Use `congr 1`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, diagonal_mul_diagonal, diagonal_mul_diagonal]`. Use `congr 2`.

Use function extensionality and compare the values at `i`. Conclude with `mul_comm _ _`.
-/
lemma cd_adj {H x : Mt n} {q : ℕ} (h : OrthFr H q x) (v : Fin n → ℂ) :
    (cd x v)ᴴ * H = H * cd x (star v) := by
  have hx : IsUnit x.det := (units_of_orth h).1
  have e : (x⁻¹)ᴴ * (xᴴ * H * x) * x⁻¹ =
      (x⁻¹)ᴴ * (diagonal fun a : Fin n => -((ReciprocityTheory.ChartRestriction.G.FD.sgn q (a : ℕ) : ℝ) : ℂ)) * x⁻¹ := by
    rw [h.2]
  have hH : H = (x⁻¹)ᴴ * (diagonal fun a : Fin n => -((ReciprocityTheory.ChartRestriction.G.FD.sgn q (a : ℕ) : ℝ) : ℂ)) * x⁻¹ := by
    rw [← e]
    have h1 : (x⁻¹)ᴴ * xᴴ = 1 := by rw [← conjTranspose_mul, mul_nonsing_inv x hx, conjTranspose_one]
    have h2 : x * x⁻¹ = 1 := mul_nonsing_inv x hx
    calc H = ((x⁻¹)ᴴ * xᴴ) * H * (x * x⁻¹) := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
      _ = (x⁻¹)ᴴ * (xᴴ * H * x) * x⁻¹ := by simp only [Matrix.mul_assoc]
  have e1 : ∀ Z : Mt n, xᴴ * ((x⁻¹)ᴴ * Z) = Z := by
    intro Z
    rw [← Matrix.mul_assoc, ← conjTranspose_mul, nonsing_inv_mul x hx, conjTranspose_one, Matrix.one_mul]
  have e2 : ∀ Z : Mt n, x⁻¹ * (x * Z) = Z := by
    intro Z
    rw [← Matrix.mul_assoc, nonsing_inv_mul x hx, Matrix.one_mul]
  rw [hH]
  unfold cd
  simp only [conjTranspose_mul, diagonal_conjTranspose, Matrix.mul_assoc, e1, e2]
  congr 1
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 2
  funext i
  exact mul_comm _ _

/- English proof (translation)
Unfold `cd`. Rewrite using `[Matrix.exp_conj x _ ((Matrix.isUnit_iff_isUnit_det x).mpr hx), Matrix.exp_diagonal, Pi.exp_def]`. Simplify using `only [Complex.exp_eq_exp_ℂ]`.
-/
lemma exp_cd {x : Mt n} (hx : IsUnit x.det) (v : Fin n → ℂ) :
    NormedSpace.exp (cd x v) = cd x (fun a => Complex.exp (v a)) := by
  unfold cd
  rw [Matrix.exp_conj x _ ((Matrix.isUnit_iff_isUnit_det x).mpr hx), Matrix.exp_diagonal, Pi.exp_def]
  simp only [Complex.exp_eq_exp_ℂ]

/- English proof (translation)
Establish `hH : IsUnit H.det` using `(units_of_orth h).2`. Unfold `conjH`. Rewrite using `[Matrix.mul_assoc, cd_adj h, ← Matrix.mul_assoc, nonsing_inv_mul H hH, Matrix.one_mul]`.
-/
lemma conjH_cd {H x : Mt n} {q : ℕ} (h : OrthFr H q x) (v : Fin n → ℂ) :
    conjH H (cd x v) = -cd x (star v) := by
  have hH : IsUnit H.det := (units_of_orth h).2
  unfold conjH
  rw [Matrix.mul_assoc, cd_adj h, ← Matrix.mul_assoc, nonsing_inv_mul H hH, Matrix.one_mul]

variable {ι : Type} [Fintype ι] [DecidableEq ι] {Hm : ι → Mt n} {q : ι → ℕ} {x₀ : ι → Mt n} {w : ι → Fin n → ℤ}

omit [Fintype ι] [DecidableEq ι] in
/- English proof (translation)
Use function extensionality and compare the values at `τ`. Establish `hx` using `(units_of_orth (h τ)).1`. Use `show cd (x₀ τ) (fun a => Complex.exp ((((s + s') τ a : ℝ) : ℂ) * Complex.I)) = cd (x₀ τ) (fun a => Complex.exp (((s τ a : ℝ) : ℂ) * Complex.I)) * cd (x₀ τ) (fun a => Complex.exp (((s' τ a : ℝ) : ℂ) * Complex.I))`. Rewrite using `[cd_mul hx]`. Use `congr 1`.

Use function extensionality and compare the values at `a`. Simplify using `only [Pi.add_apply, Pi.mul_apply, Complex.ofReal_add, add_mul, Complex.exp_add]`.
-/
lemma torEl_add (h : ∀ τ, OrthFr (Hm τ) (q τ) (x₀ τ)) (s s' : ι → Fin n → ℝ) :
    torEl x₀ (s + s') = torEl x₀ s * torEl x₀ s' := by
  funext τ
  have hx := (units_of_orth (h τ)).1
  show cd (x₀ τ) (fun a => Complex.exp ((((s + s') τ a : ℝ) : ℂ) * Complex.I)) =
    cd (x₀ τ) (fun a => Complex.exp (((s τ a : ℝ) : ℂ) * Complex.I)) *
      cd (x₀ τ) (fun a => Complex.exp (((s' τ a : ℝ) : ℂ) * Complex.I))
  rw [cd_mul hx]
  congr 1
  funext a
  simp only [Pi.add_apply, Pi.mul_apply, Complex.ofReal_add, add_mul, Complex.exp_add]

omit [Fintype ι] [DecidableEq ι] in
/- English proof (translation)
Use function extensionality and compare the values at `τ`. Establish `hx` using `(units_of_orth (h τ)).1`. Use `show cd (x₀ τ) (fun a => Complex.exp ((((0 : ι → Fin n → ℝ) τ a : ℝ) : ℂ) * Complex.I)) = 1`. Simplify using `only [Pi.zero_apply, Complex.ofReal_zero, zero_mul, Complex.exp_zero]`. Conclude with `cd_one hx`.
-/
lemma torEl_zero (h : ∀ τ, OrthFr (Hm τ) (q τ) (x₀ τ)) : torEl x₀ 0 = 1 := by
  funext τ
  have hx := (units_of_orth (h τ)).1
  show cd (x₀ τ) (fun a => Complex.exp ((((0 : ι → Fin n → ℝ) τ a : ℝ) : ℂ) * Complex.I)) = 1
  simp only [Pi.zero_apply, Complex.ofReal_zero, zero_mul, Complex.exp_zero]
  exact cd_one hx

omit [Fintype ι] [DecidableEq ι] in
/- English proof (translation)
Unfold `UG`. Rewrite using `[Set.mem_ofPred_eq]`. Introduce `τ`. Establish `hx` using `(units_of_orth (h τ)).1`. Establish `ht : (torEl x₀ s τ)ᴴ * Hm τ * torEl x₀ s τ = Hm τ` using `by show (cd (x₀ τ) (fun a => Complex.exp (((s τ a : ℝ) : ℂ) * Complex.I)))ᴴ * Hm τ * cd (x₀ τ) (fun a => Complex.exp (((s τ a : ℝ) : ℂ) * Complex.I)) = Hm τ`.

Rewrite using `[cd_adj (h τ), Matrix.mul_assoc, cd_mul hx]`. Establish `hs1 : (star fun a => Complex.exp (((s τ a : ℝ) : ℂ) * Complex.I)) * (fun a => Complex.exp (((s τ a : ℝ) : ℂ) * Complex.I)) = fun _ => 1`. Use function extensionality and compare the values at `a`. Use `show (starRingEnd ℂ) (Complex.exp (((s τ a : ℝ) : ℂ) * Complex.I)) * Complex.exp (((s τ a : ℝ) : ℂ) * Complex.I) = 1`. Rewrite using `[← Complex.exp_conj, ← Complex.exp_add, map_mul, Complex.conj_ofReal, Complex.conj_I]`.

Simplify using the standard rewrite rules. Rewrite using `[hs1, cd_one hx, Matrix.mul_one]`. Establish `hu' : (u τ)ᴴ * Hm τ * u τ = Hm τ` using `hu τ`. Use `show (u τ * torEl x₀ s τ)ᴴ * Hm τ * (u τ * torEl x₀ s τ) = Hm τ`. Rewrite using `[conjTranspose_mul]`.

Combine the equalities or inequalities in the displayed calculation.
-/
lemma mul_torEl_mem (h : ∀ τ, OrthFr (Hm τ) (q τ) (x₀ τ)) (s : ι → Fin n → ℝ) {u : ι → Mt n} (hu : u ∈ UG Hm) :
    u * torEl x₀ s ∈ UG Hm := by
  unfold UG
  rw [Set.mem_ofPred_eq]
  intro τ
  have hx := (units_of_orth (h τ)).1
  have ht : (torEl x₀ s τ)ᴴ * Hm τ * torEl x₀ s τ = Hm τ := by
    show (cd (x₀ τ) (fun a => Complex.exp (((s τ a : ℝ) : ℂ) * Complex.I)))ᴴ * Hm τ *
      cd (x₀ τ) (fun a => Complex.exp (((s τ a : ℝ) : ℂ) * Complex.I)) = Hm τ
    rw [cd_adj (h τ), Matrix.mul_assoc, cd_mul hx]
    have hs1 : (star fun a => Complex.exp (((s τ a : ℝ) : ℂ) * Complex.I)) *
        (fun a => Complex.exp (((s τ a : ℝ) : ℂ) * Complex.I)) = fun _ => 1 := by
      funext a
      show (starRingEnd ℂ) (Complex.exp (((s τ a : ℝ) : ℂ) * Complex.I)) *
        Complex.exp (((s τ a : ℝ) : ℂ) * Complex.I) = 1
      rw [← Complex.exp_conj, ← Complex.exp_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
      simp
    rw [hs1, cd_one hx, Matrix.mul_one]
  have hu' : (u τ)ᴴ * Hm τ * u τ = Hm τ := hu τ
  show (u τ * torEl x₀ s τ)ᴴ * Hm τ * (u τ * torEl x₀ s τ) = Hm τ
  rw [conjTranspose_mul]
  calc _ = (torEl x₀ s τ)ᴴ * ((u τ)ᴴ * Hm τ * u τ) * torEl x₀ s τ := by simp only [Matrix.mul_assoc]
    _ = Hm τ := by rw [hu', ht]

omit [DecidableEq ι] in
/- English proof (translation)
Unfold `torCh`. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun a _ => ?_` and prove the remaining obligations.

Rewrite using `[Pi.add_apply, Pi.add_apply, Complex.ofReal_add, add_mul, Complex.exp_add, mul_zpow]`.
-/
lemma torCh_add (s s' : ι → Fin n → ℝ) : torCh w (s + s') = torCh w s * torCh w s' := by
  unfold torCh
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [Pi.add_apply, Pi.add_apply, Complex.ofReal_add, add_mul, Complex.exp_add, mul_zpow]

/- English proof (translation)
Unfold `torCh`. Establish `h1 : ∀ σ ∈ (Finset.univ : Finset ι), σ ≠ τ → (∏ b, Complex.exp ((((Pi.single τ (Pi.single a t) : ι → Fin n → ℝ) σ b : ℝ) : ℂ) * Complex.I) ^ w σ b) = 1`. Introduce `σ _ hσ`. Simplify using `[Pi.single_eq_of_ne hσ]`. Rewrite using `[Finset.prod_eq_single τ h1 (fun h => absurd (Finset.mem_univ τ) h)]`.

Establish `h2 : ∀ b ∈ (Finset.univ : Finset (Fin n)), b ≠ a → Complex.exp ((((Pi.single τ (Pi.single a t) : ι → Fin n → ℝ) τ b : ℝ) : ℂ) * Complex.I) ^ w τ b = 1`. Introduce `b _ hb`. Simplify using `[Pi.single_eq_of_ne hb]`. Rewrite using `[Finset.prod_eq_single a h2 (fun h => absurd (Finset.mem_univ a) h)]`. Simplify using `only [Pi.single_eq_same]`.

Rewrite using `[← Complex.exp_int_mul]`.
-/
lemma torCh_single (τ : ι) (a : Fin n) (t : ℝ) :
    torCh w (Pi.single τ (Pi.single a t)) = Complex.exp ((w τ a : ℂ) * ((t : ℂ) * Complex.I)) := by
  unfold torCh
  have h1 : ∀ σ ∈ (Finset.univ : Finset ι), σ ≠ τ →
      (∏ b, Complex.exp ((((Pi.single τ (Pi.single a t) : ι → Fin n → ℝ) σ b : ℝ) : ℂ) * Complex.I) ^ w σ b) = 1 := by
    intro σ _ hσ
    simp [Pi.single_eq_of_ne hσ]
  rw [Finset.prod_eq_single τ h1 (fun h => absurd (Finset.mem_univ τ) h)]
  have h2 : ∀ b ∈ (Finset.univ : Finset (Fin n)), b ≠ a →
      Complex.exp ((((Pi.single τ (Pi.single a t) : ι → Fin n → ℝ) τ b : ℝ) : ℂ) * Complex.I) ^ w τ b = 1 := by
    intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  rw [Finset.prod_eq_single a h2 (fun h => absurd (Finset.mem_univ a) h)]
  simp only [Pi.single_eq_same]
  rw [← Complex.exp_int_mul]

omit [Fintype ι] in
/- English proof (translation)
Establish `hx : IsUnit (x₀ τ).det` using `(units_of_orth (h τ)).1`. Establish `hsm : t • cd (x₀ τ) (Pi.single a (-Complex.I)) = cd (x₀ τ) ((t : ℂ) • Pi.single a (-Complex.I))`. Rewrite using `[← cd_smul]`. Use extensionality with `i j`. Simplify using `[Complex.real_smul]`.

Rewrite using `[hsm, exp_cd hx]`. Use function extensionality and compare the values at `σ`. Distinguish the cases in `hσ : σ = τ`. Rewrite using `[hσ, Pi.mulSingle_eq_same] show _ = cd (x₀ τ) (fun b => Complex.exp ((((Pi.single τ (Pi.single a (-t)) : ι → Fin n → ℝ) τ b : ℝ) : ℂ) * Complex.I))`. Use `congr 1`.

Use function extensionality and compare the values at `b`. Distinguish the cases in `hb : b = a`. Rewrite using `[hb]`. Simplify using `only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, Complex.ofReal_neg]`. Put the polynomial expressions in normal form.

Simplify using `[Pi.single_eq_of_ne hb]`. Rewrite using `[Pi.mulSingle_eq_of_ne hσ]`. Establish `hxσ : IsUnit (x₀ σ).det` using `(units_of_orth (h σ)).1`. Use `show (1 : Mt n) = cd (x₀ σ) (fun b => Complex.exp ((((Pi.single τ (Pi.single a (-t)) : ι → Fin n → ℝ) σ b : ℝ) : ℂ) * Complex.I))`. Simplify using `only [Pi.single_eq_of_ne hσ, Pi.zero_apply, Complex.ofReal_zero, zero_mul, Complex.exp_zero]`.

Conclude with `(cd_one hxσ).symm`.
-/
lemma oneP_eq (h : ∀ τ, OrthFr (Hm τ) (q τ) (x₀ τ)) (τ : ι) (a : Fin n) (t : ℝ) :
    (Pi.mulSingle τ (NormedSpace.exp (t • cd (x₀ τ) (Pi.single a (-Complex.I)))) : ι → Mt n) =
      torEl x₀ (Pi.single τ (Pi.single a (-t))) := by
  have hx : IsUnit (x₀ τ).det := (units_of_orth (h τ)).1
  have hsm : t • cd (x₀ τ) (Pi.single a (-Complex.I)) =
      cd (x₀ τ) ((t : ℂ) • Pi.single a (-Complex.I)) := by
    rw [← cd_smul]
    ext i j
    simp [Complex.real_smul]
  rw [hsm, exp_cd hx]
  funext σ
  by_cases hσ : σ = τ
  · rw [hσ, Pi.mulSingle_eq_same]
    show _ = cd (x₀ τ) (fun b => Complex.exp ((((Pi.single τ (Pi.single a (-t)) : ι → Fin n → ℝ) τ b : ℝ) : ℂ) * Complex.I))
    congr 1
    funext b
    by_cases hb : b = a
    · rw [hb]
      simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, Complex.ofReal_neg]
      ring_nf
    · simp [Pi.single_eq_of_ne hb]
  · rw [Pi.mulSingle_eq_of_ne hσ]
    have hxσ : IsUnit (x₀ σ).det := (units_of_orth (h σ)).1
    show (1 : Mt n) = cd (x₀ σ) (fun b => Complex.exp ((((Pi.single τ (Pi.single a (-t)) : ι → Fin n → ℝ) σ b : ℝ) : ℂ) * Complex.I))
    simp only [Pi.single_eq_of_ne hσ, Pi.zero_apply, Complex.ofReal_zero, zero_mul, Complex.exp_zero]
    exact (cd_one hxσ).symm

/- English proof (translation)
Unfold `der`. Simplify using `[NormedSpace.exp_zero]`.
-/
private lemma der_zero' (τ : ι) (f : (ι → Mt n) → ℂ) (u : ι → Mt n) : der τ (0 : Mt n) f u = 0 := by
  unfold der
  simp [NormedSpace.exp_zero]

/- English proof (translation)
Take `⟨S, hSdef⟩ : ∃ S : ℝ → ι → Mt n, S = fun r => torEl x₀ (Pi.single τ (Pi.single a r))` from `⟨_, rfl⟩`. Establish `hS_add : ∀ r r', S (r + r') = S r * S r'`. Introduce `r r'`. Rewrite using `[hSdef]`. Simplify using `only [Pi.single_add]`.

Conclude with `torEl_add h _ _`. Establish `hS0 : S 0 = 1`. Rewrite using `[hSdef]`. Simplify using `only [Pi.single_zero]`. Conclude with `torEl_zero h`.

Establish `hS_mem : ∀ v ∈ UG Hm, ∀ r, v * S r ∈ UG Hm`. Introduce `v hv r`. Rewrite using `[hSdef]`. Conclude with `mul_torEl_mem h _ hv`. Take `⟨Y, hY⟩ : ∃ Y : Mt n, Y = cd (x₀ τ) (Pi.single a (-Complex.I))` from `⟨_, rfl⟩`.

Establish `hexp : ∀ r : ℝ, (Pi.mulSingle τ (NormedSpace.exp (r • Y)) : ι → Mt n) = S (-r)`. Introduce `r`. Rewrite using `[hSdef, hY]`. Conclude with `oneP_eq h τ a r`. Establish `hYlie : Y ∈ lieH (Hm τ)` using `by show Yᴴ * Hm τ + Hm τ * Y = 0`.

Establish `hst : star (Pi.single a (-Complex.I) : Fin n → ℂ) = -Pi.single a (-Complex.I)`. Use function extensionality and compare the values at `b`. Distinguish the cases in `hb : b = a`. Rewrite using `[hb]`. Simplify using `[Complex.conj_I]`.

Simplify using `[Pi.single_eq_of_ne hb]`. Rewrite using `[hY, cd_adj (h τ), hst, cd_neg, Matrix.mul_neg, neg_add_cancel]`. Establish `hZ : x₀ τ * Matrix.single a a (1 : ℂ) * (x₀ τ)⁻¹ = cd (x₀ τ) (Pi.single a 1)`. Unfold `cd`. Rewrite using `[Matrix.diagonal_single]`.

Establish `hconj : conjH (Hm τ) (cd (x₀ τ) (Pi.single a 1)) = -cd (x₀ τ) (Pi.single a 1)`. Rewrite using `[conjH_cd (h τ)]`. Use `congr 2`. Use function extensionality and compare the values at `b`. Distinguish the cases in `hb : b = a`.

Rewrite using `[hb]`. Simplify using the standard rewrite rules. Simplify using `[Pi.single_eq_of_ne hb]`. Establish `hcoef : (1 / (2 * Complex.I)) • (cd (x₀ τ) (Pi.single a 1) - -cd (x₀ τ) (Pi.single a 1)) = Y`. Establish `hI : (1 / (2 * Complex.I)) * 2 = -Complex.I`.

Rewrite using `[one_div, mul_inv, mul_comm (2 : ℂ)⁻¹, mul_assoc, inv_mul_cancel₀ two_ne_zero, mul_one, Complex.inv_I]`. Rewrite using `[sub_neg_eq_add, ← two_smul ℂ, smul_smul, hI, hY, cd_smul]`. Use `congr 1`. Use function extensionality and compare the values at `b`. Distinguish the cases in `hb : b = a`.

Rewrite using `[hb]`. Simplify using the standard rewrite rules. Simplify using `[Pi.single_eq_of_ne hb]`. Establish `hd : ∀ v ∈ UG Hm, Complex.I * der τ Y f v = (w τ a : ℂ) * f v`. Introduce `v hv`.

Establish `hkv` using `hk τ a a le_rfl v hv`. Rewrite `hkv` using `[if_pos rfl, hZ]`. Unfold `derC at hkv`. Rewrite `hkv` using `[hconj, add_neg_cancel, smul_zero, der_zero', zero_add, hcoef]`. Conclude with `hkv`.

Establish `hψ : ∀ v ∈ UG Hm, HasDerivAt (fun r : ℝ => f (v * S r)) (Complex.I * (w τ a : ℂ) * f v) 0`. Introduce `v hv`. Establish `hsm` using `hs 1 (fun _ => τ) (fun _ => Y) (fun _ => hYlie) v hv`. Establish `hneg : (fun r : ℝ => f (v * S (-r))) = (fun t : Fin 1 → ℝ => f (v * (List.ofFn fun i => (Pi.mulSingle ((fun _ : Fin 1 => τ) i) (NormedSpace.exp (t i • (fun _ : Fin 1 => Y) i)) : ι → Mt n)).prod)) ∘ (fun r : ℝ => fun _ : Fin 1 => r)`. Use function extensionality and compare the values at `r`.

Simplify using `[Function.comp, List.ofFn_succ, hexp]`. Establish `hdn : Differentiable ℝ (fun r : ℝ => f (v * S (-r)))`. Rewrite using `[hneg]`. Conclude with `(hsm.differentiable (by simp)).comp (differentiable_pi.2 fun _ => differentiable_id)`. Establish `hdiff : Differentiable ℝ (fun r : ℝ => f (v * S r))`.

Establish `h3 : (fun r : ℝ => f (v * S r)) = (fun r : ℝ => f (v * S (-r))) ∘ Neg.neg`. Use function extensionality and compare the values at `r`. Simplify using `only [Function.comp, neg_neg]`. Rewrite using `[h3]`. Conclude with `hdn.comp differentiable_neg`.

Establish `hder : deriv (fun r : ℝ => f (v * S r)) 0 = Complex.I * (w τ a : ℂ) * f v`. Establish `h1` using `hd v hv`. Establish `h2 : der τ Y f v = -deriv (fun r : ℝ => f (v * S r)) 0`. Unfold `der`. Simplify using `only [hexp]`.

Establish `h4` using `deriv_comp_neg (fun r : ℝ => f (v * S r)) 0`. Simplify using `only [neg_zero] at h4`. Conclude with `h4`. Rewrite `h1` using `[h2]`. Take the linear combination `Complex.I * h1 + deriv (fun r : ℝ => f (v * S r)) 0 * Complex.I_sq`.

Rewrite using `[← hder]`. Conclude with `(hdiff 0).hasDerivAt`. Establish `hφ : ∀ r : ℝ, HasDerivAt (fun r : ℝ => f (u * S r)) (Complex.I * (w τ a : ℂ) * f (u * S r)) r`. Introduce `r`. Establish `h1` using `hψ (u * S r) (hS_mem u hu r)`.

Establish `h3 : HasDerivAt (fun x : ℝ => f (u * S r * S (x - r))) (Complex.I * (w τ a : ℂ) * f (u * S r)) r` using `HasDerivAt.comp_sub_const (f := fun r' : ℝ => f (u * S r * S r')) r r (by rw [sub_self]; exact h1)`. Establish `h2 : (fun x : ℝ => f (u * S r * S (x - r))) = fun x : ℝ => f (u * S x)`. Use function extensionality and compare the values at `x`. Rewrite using `[mul_assoc, ← hS_add, show r + (x - r) = x by ring]`. Rewrite `h3` using `[h2]`.

Conclude with `h3`. Establish `hg : ∀ r : ℝ, HasDerivAt (fun r : ℝ => Complex.exp (-(Complex.I * (w τ a : ℂ) * r)) * f (u * S r)) 0 r`. Introduce `r`. Establish `he : HasDerivAt (fun r : ℝ => Complex.exp (-(Complex.I * (w τ a : ℂ) * r))) (Complex.exp (-(Complex.I * (w τ a : ℂ) * r)) * (-(Complex.I * (w τ a : ℂ) * ((1 : ℝ) : ℂ)))) r` using `(((hasDerivAt_id r).ofReal_comp).const_mul (Complex.I * (w τ a : ℂ))).neg.cexp`. Use `(he.mul (hφ r)).congr_deriv ?_` and prove the remaining obligations.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hdg : Differentiable ℝ (fun r : ℝ => Complex.exp (-(Complex.I * (w τ a : ℂ) * r)) * f (u * S r))` using `fun x => (hg x).differentiableAt`. Establish `hdg' : ∀ x, deriv (fun r : ℝ => Complex.exp (-(Complex.I * (w τ a : ℂ) * r)) * f (u * S r)) x = 0` using `fun x => (hg x).deriv`. Establish `hgc : Complex.exp (-(Complex.I * (w τ a : ℂ) * t)) * f (u * S t) = f u`.

Use `(is_const_of_deriv_eq_zero hdg hdg' t 0).trans ?_` and prove the remaining obligations. Simplify using `[hS0]`. Establish `hfin : torEl x₀ (Pi.single τ (Pi.single a t)) = S t` using `by rw [hSdef]`. Rewrite using `[hfin, torCh_single]`. Establish `hinv : Complex.exp ((w τ a : ℂ) * ((t : ℂ) * Complex.I)) * Complex.exp (-(Complex.I * (w τ a : ℂ) * t)) = 1`.

Rewrite using `[← Complex.exp_add, show (w τ a : ℂ) * ((t : ℂ) * Complex.I) + -(Complex.I * (w τ a : ℂ) * t) = 0 by ring, Complex.exp_zero]`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma law_single (h : ∀ τ, OrthFr (Hm τ) (q τ) (x₀ τ)) {f : (ι → Mt n) → ℂ} (hs : SmFn Hm f) (hk : KilledFn Hm x₀ w f)
    (τ : ι) (a : Fin n) (t : ℝ) {u : ι → Mt n} (hu : u ∈ UG Hm) :
    f (u * torEl x₀ (Pi.single τ (Pi.single a t))) = torCh w (Pi.single τ (Pi.single a t)) * f u := by
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ → ι → Mt n, S = fun r => torEl x₀ (Pi.single τ (Pi.single a r)) := ⟨_, rfl⟩
  have hS_add : ∀ r r', S (r + r') = S r * S r' := by
    intro r r'
    rw [hSdef]
    simp only [Pi.single_add]
    exact torEl_add h _ _
  have hS0 : S 0 = 1 := by
    rw [hSdef]
    simp only [Pi.single_zero]
    exact torEl_zero h
  have hS_mem : ∀ v ∈ UG Hm, ∀ r, v * S r ∈ UG Hm := by
    intro v hv r
    rw [hSdef]
    exact mul_torEl_mem h _ hv
  obtain ⟨Y, hY⟩ : ∃ Y : Mt n, Y = cd (x₀ τ) (Pi.single a (-Complex.I)) := ⟨_, rfl⟩
  have hexp : ∀ r : ℝ, (Pi.mulSingle τ (NormedSpace.exp (r • Y)) : ι → Mt n) = S (-r) := by
    intro r
    rw [hSdef, hY]
    exact oneP_eq h τ a r
  have hYlie : Y ∈ lieH (Hm τ) := by
    show Yᴴ * Hm τ + Hm τ * Y = 0
    have hst : star (Pi.single a (-Complex.I) : Fin n → ℂ) = -Pi.single a (-Complex.I) := by
      funext b
      by_cases hb : b = a
      · rw [hb]
        simp [Complex.conj_I]
      · simp [Pi.single_eq_of_ne hb]
    rw [hY, cd_adj (h τ), hst, cd_neg, Matrix.mul_neg, neg_add_cancel]
  have hZ : x₀ τ * Matrix.single a a (1 : ℂ) * (x₀ τ)⁻¹ = cd (x₀ τ) (Pi.single a 1) := by
    unfold cd
    rw [Matrix.diagonal_single]
  have hconj : conjH (Hm τ) (cd (x₀ τ) (Pi.single a 1)) = -cd (x₀ τ) (Pi.single a 1) := by
    rw [conjH_cd (h τ)]
    congr 2
    funext b
    by_cases hb : b = a
    · rw [hb]
      simp
    · simp [Pi.single_eq_of_ne hb]
  have hcoef : (1 / (2 * Complex.I)) • (cd (x₀ τ) (Pi.single a 1) - -cd (x₀ τ) (Pi.single a 1)) = Y := by
    have hI : (1 / (2 * Complex.I)) * 2 = -Complex.I := by
      rw [one_div, mul_inv, mul_comm (2 : ℂ)⁻¹, mul_assoc, inv_mul_cancel₀ two_ne_zero, mul_one, Complex.inv_I]
    rw [sub_neg_eq_add, ← two_smul ℂ, smul_smul, hI, hY, cd_smul]
    congr 1
    funext b
    by_cases hb : b = a
    · rw [hb]
      simp
    · simp [Pi.single_eq_of_ne hb]
  have hd : ∀ v ∈ UG Hm, Complex.I * der τ Y f v = (w τ a : ℂ) * f v := by
    intro v hv
    have hkv := hk τ a a le_rfl v hv
    rw [if_pos rfl, hZ] at hkv
    unfold derC at hkv
    rw [hconj, add_neg_cancel, smul_zero, der_zero', zero_add, hcoef] at hkv
    exact hkv
  have hψ : ∀ v ∈ UG Hm,
      HasDerivAt (fun r : ℝ => f (v * S r)) (Complex.I * (w τ a : ℂ) * f v) 0 := by
    intro v hv
    have hsm := hs 1 (fun _ => τ) (fun _ => Y) (fun _ => hYlie) v hv
    have hneg : (fun r : ℝ => f (v * S (-r))) =
        (fun t : Fin 1 → ℝ => f (v * (List.ofFn fun i =>
          (Pi.mulSingle ((fun _ : Fin 1 => τ) i) (NormedSpace.exp (t i • (fun _ : Fin 1 => Y) i)) : ι → Mt n)).prod)) ∘
          (fun r : ℝ => fun _ : Fin 1 => r) := by
      funext r
      simp [Function.comp, List.ofFn_succ, hexp]
    have hdn : Differentiable ℝ (fun r : ℝ => f (v * S (-r))) := by
      rw [hneg]
      exact (hsm.differentiable (by simp)).comp (differentiable_pi.2 fun _ => differentiable_id)
    have hdiff : Differentiable ℝ (fun r : ℝ => f (v * S r)) := by
      have h3 : (fun r : ℝ => f (v * S r)) = (fun r : ℝ => f (v * S (-r))) ∘ Neg.neg := by
        funext r
        simp only [Function.comp, neg_neg]
      rw [h3]
      exact hdn.comp differentiable_neg
    have hder : deriv (fun r : ℝ => f (v * S r)) 0 = Complex.I * (w τ a : ℂ) * f v := by
      have h1 := hd v hv
      have h2 : der τ Y f v = -deriv (fun r : ℝ => f (v * S r)) 0 := by
        unfold der
        simp only [hexp]
        have h4 := deriv_comp_neg (fun r : ℝ => f (v * S r)) 0
        simp only [neg_zero] at h4
        exact h4
      rw [h2] at h1
      linear_combination Complex.I * h1 + deriv (fun r : ℝ => f (v * S r)) 0 * Complex.I_sq
    rw [← hder]
    exact (hdiff 0).hasDerivAt
  have hφ : ∀ r : ℝ, HasDerivAt (fun r : ℝ => f (u * S r)) (Complex.I * (w τ a : ℂ) * f (u * S r)) r := by
    intro r
    have h1 := hψ (u * S r) (hS_mem u hu r)
    have h3 : HasDerivAt (fun x : ℝ => f (u * S r * S (x - r))) (Complex.I * (w τ a : ℂ) * f (u * S r)) r :=
      HasDerivAt.comp_sub_const (f := fun r' : ℝ => f (u * S r * S r')) r r (by rw [sub_self]; exact h1)
    have h2 : (fun x : ℝ => f (u * S r * S (x - r))) = fun x : ℝ => f (u * S x) := by
      funext x
      rw [mul_assoc, ← hS_add, show r + (x - r) = x by ring]
    rw [h2] at h3
    exact h3
  have hg : ∀ r : ℝ, HasDerivAt (fun r : ℝ => Complex.exp (-(Complex.I * (w τ a : ℂ) * r)) * f (u * S r)) 0 r := by
    intro r
    have he : HasDerivAt (fun r : ℝ => Complex.exp (-(Complex.I * (w τ a : ℂ) * r)))
        (Complex.exp (-(Complex.I * (w τ a : ℂ) * r)) * (-(Complex.I * (w τ a : ℂ) * ((1 : ℝ) : ℂ)))) r :=
      (((hasDerivAt_id r).ofReal_comp).const_mul (Complex.I * (w τ a : ℂ))).neg.cexp
    refine (he.mul (hφ r)).congr_deriv ?_
    push_cast
    ring
  have hdg : Differentiable ℝ (fun r : ℝ => Complex.exp (-(Complex.I * (w τ a : ℂ) * r)) * f (u * S r)) :=
    fun x => (hg x).differentiableAt
  have hdg' : ∀ x, deriv (fun r : ℝ => Complex.exp (-(Complex.I * (w τ a : ℂ) * r)) * f (u * S r)) x = 0 :=
    fun x => (hg x).deriv
  have hgc : Complex.exp (-(Complex.I * (w τ a : ℂ) * t)) * f (u * S t) = f u := by
    refine (is_const_of_deriv_eq_zero hdg hdg' t 0).trans ?_
    simp [hS0]
  have hfin : torEl x₀ (Pi.single τ (Pi.single a t)) = S t := by rw [hSdef]
  rw [hfin, torCh_single]
  have hinv : Complex.exp ((w τ a : ℂ) * ((t : ℂ) * Complex.I)) * Complex.exp (-(Complex.I * (w τ a : ℂ) * t)) = 1 := by
    rw [← Complex.exp_add, show (w τ a : ℂ) * ((t : ℂ) * Complex.I) + -(Complex.I * (w τ a : ℂ) * t) = 0 by ring,
      Complex.exp_zero]
  calc f (u * S t) = Complex.exp ((w τ a : ℂ) * ((t : ℂ) * Complex.I)) *
        (Complex.exp (-(Complex.I * (w τ a : ℂ) * t)) * f (u * S t)) := by rw [← mul_assoc, hinv, one_mul]
    _ = _ := by rw [hgc]

end GlobalTheory.HolDict.TorusLaw

namespace GlobalTheory.HolDict

open TorusLaw in

/- English proof (translation)
Introduce `n ι _ _ Hm q x₀ w h f hs hk u hu s`. Establish `key : ∀ S : Finset (ι × Fin n), ∀ v ∈ UG Hm, f (v * torEl x₀ (fun τ a => if (τ, a) ∈ S then s τ a else 0)) = torCh w (fun τ a => if (τ, a) ∈ S then s τ a else 0) * f v`. Introduce `S`. Use `Finset.induction_on S ?_ ?_` and prove the remaining obligations. Introduce `v _`.

Establish `h0 : (fun τ a => if ((τ, a) : ι × Fin n) ∈ (∅ : Finset (ι × Fin n)) then s τ a else 0) = (0 : ι → Fin n → ℝ)`. Use function extensionality and compare the values at `τ a`. Simplify using the standard rewrite rules. Establish `hc0 : torCh w (0 : ι → Fin n → ℝ) = 1`. Simplify using `[torCh]`.

Rewrite using `[h0, torEl_zero h, mul_one, hc0, one_mul]`. Introduce `p S hp ih v hv`. Establish `hps : ∀ (τ : ι) (a : Fin n), (Pi.single p.1 (Pi.single p.2 (s p.1 p.2)) : ι → Fin n → ℝ) τ a = if (τ, a) = p then s τ a else 0`. Introduce `τ a`. Break down `p with ⟨τ0, a0⟩` into its components or cases.

Apply the tactic sequence `by_cases e1 : τ = τ0 <;> by_cases e2 : a = a0 <;> simp [e1, e2]`. Establish `hsplit : (fun τ a => if (τ, a) ∈ insert p S then s τ a else 0) = Pi.single p.1 (Pi.single p.2 (s p.1 p.2)) + (fun τ a => if (τ, a) ∈ S then s τ a else 0)`. Use function extensionality and compare the values at `τ a`. Rewrite using `[Pi.add_apply, Pi.add_apply, hps]`. Distinguish the cases in `e : (τ, a) = p`.

Substitute `e` using the available equality. Simplify using `[hp]`. Simplify using `[e]`. Rewrite using `[hsplit, torEl_add h, ← mul_assoc, ih _ (mul_torEl_mem h _ hv), law_single h hs hk p.1 p.2 (s p.1 p.2) hv, torCh_add]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hfull : (fun τ a => if ((τ, a) : ι × Fin n) ∈ (Finset.univ : Finset (ι × Fin n)) then s τ a else 0) = s`. Use function extensionality and compare the values at `τ a`. Simplify using the standard rewrite rules. Use `key Finset.univ u hu` as an intermediate fact. Rewrite `this` using `[hfull]`. Then use the resulting hypothesis.
-/
theorem torus_law_of_killed : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (Hm : ι → Mt n) (q : ι → ℕ) (x₀ : ι → Mt n) (w : ι → Fin n → ℤ), (∀ τ, OrthFr (Hm τ) (q τ) (x₀ τ)) → ∀ f, SmFn Hm f → KilledFn Hm x₀ w f → ∀ u ∈ UG Hm, ∀ s, f (u * torEl x₀ s) = torCh w s * f u := by
  intro n ι _ _ Hm q x₀ w h f hs hk u hu s
  have key : ∀ S : Finset (ι × Fin n), ∀ v ∈ UG Hm,
      f (v * torEl x₀ (fun τ a => if (τ, a) ∈ S then s τ a else 0)) =
        torCh w (fun τ a => if (τ, a) ∈ S then s τ a else 0) * f v := by
    intro S
    refine Finset.induction_on S ?_ ?_
    · intro v _
      have h0 : (fun τ a => if ((τ, a) : ι × Fin n) ∈ (∅ : Finset (ι × Fin n)) then s τ a else 0) =
          (0 : ι → Fin n → ℝ) := by
        funext τ a
        simp
      have hc0 : torCh w (0 : ι → Fin n → ℝ) = 1 := by
        simp [torCh]
      rw [h0, torEl_zero h, mul_one, hc0, one_mul]
    · intro p S hp ih v hv
      have hps : ∀ (τ : ι) (a : Fin n), (Pi.single p.1 (Pi.single p.2 (s p.1 p.2)) : ι → Fin n → ℝ) τ a =
          if (τ, a) = p then s τ a else 0 := by
        intro τ a
        rcases p with ⟨τ0, a0⟩
        by_cases e1 : τ = τ0 <;> by_cases e2 : a = a0 <;> simp [e1, e2]
      have hsplit : (fun τ a => if (τ, a) ∈ insert p S then s τ a else 0) =
          Pi.single p.1 (Pi.single p.2 (s p.1 p.2)) + (fun τ a => if (τ, a) ∈ S then s τ a else 0) := by
        funext τ a
        rw [Pi.add_apply, Pi.add_apply, hps]
        by_cases e : (τ, a) = p
        · subst e
          simp [hp]
        · simp [e]
      rw [hsplit, torEl_add h, ← mul_assoc, ih _ (mul_torEl_mem h _ hv),
        law_single h hs hk p.1 p.2 (s p.1 p.2) hv, torCh_add]
      ring
  have hfull : (fun τ a => if ((τ, a) : ι × Fin n) ∈ (Finset.univ : Finset (ι × Fin n)) then s τ a else 0) = s := by
    funext τ a
    simp
  have := key Finset.univ u hu
  rwa [hfull] at this

end GlobalTheory.HolDict
