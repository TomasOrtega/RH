import Mathlib
import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.EquivariantSections.EquivSection

noncomputable section

open Matrix ReciprocityTheory.ChartRestriction.DS.S7

namespace GlobalTheory.CompanionTheory.HolOm

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

/- English proof (translation)
Distinguish the cases in `h : j ≤ n`. Establish `: (lead j : Matrix (Fin n) (Fin n) ℂ → ℂ) = fun z => (z.submatrix (Fin.castLE h) (Fin.castLE h)).det`. Use function extensionality and compare the values at `z`. Simplify using `[lead, h]`. Rewrite using `[this]`.

Simplify using `only [Matrix.det_apply]`. Use `ContDiff.sum fun σ _ => ?_` and prove the remaining obligations. Use `ContDiff.const_smul _ ?_` and prove the remaining obligations. Use `contDiff_prod fun i _ => ?_` and prove the remaining obligations. Conclude with `contDiff_apply_apply ℂ ℂ _ _`.

Establish `: (lead j : Matrix (Fin n) (Fin n) ℂ → ℂ) = fun _ => 0`. Use function extensionality and compare the values at `z`. Simplify using `[lead, h]`. Rewrite using `[this]`. Conclude with `contDiff_const`.
-/
theorem contDiff_lead (j : ℕ) : ContDiff ℂ ⊤ (lead j : Matrix (Fin n) (Fin n) ℂ → ℂ) := by
  by_cases h : j ≤ n
  · have : (lead j : Matrix (Fin n) (Fin n) ℂ → ℂ) =
        fun z => (z.submatrix (Fin.castLE h) (Fin.castLE h)).det := by
      funext z; simp [lead, h]
    rw [this]
    simp only [Matrix.det_apply]
    refine ContDiff.sum fun σ _ => ?_
    refine ContDiff.const_smul _ ?_
    refine contDiff_prod fun i _ => ?_
    exact contDiff_apply_apply ℂ ℂ _ _
  · have : (lead j : Matrix (Fin n) (Fin n) ℂ → ℂ) = fun _ => 0 := by
      funext z; simp [lead, h]
    rw [this]
    exact contDiff_const

/- English proof (translation)
Establish `: OmegaSet n = ⋂ i : Fin n, {z | lead ((i : ℕ) + 1) z ≠ 0}`. Use extensionality with `z`. Simplify using `[OmegaSet]`. Rewrite using `[this]`. Conclude with `isOpen_iInter_of_finite fun i => isOpen_ne_fun (contDiff_lead _).continuous continuous_const`.
-/
theorem isOpen_OmegaSet (n : ℕ) : IsOpen (OmegaSet n) := by
  have : OmegaSet n = ⋂ i : Fin n, {z | lead ((i : ℕ) + 1) z ≠ 0} := by
    ext z; simp [OmegaSet]
  rw [this]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_ne_fun (contDiff_lead _).continuous continuous_const

open PositivityTheory.RgDs.K

def mulL (Y : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℂ Y)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mulL_apply (Y z : Matrix (Fin n) (Fin n) ℂ) : mulL Y z = Y * z := rfl

/- English proof (translation)
The claim follows from `if_pos hz`.
-/
theorem lop_on {Y : Matrix (Fin n) (Fin n) ℂ} {F : Matrix (Fin n) (Fin n) ℂ → ℂ}
    {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ OmegaSet n) : lop Y F z = -(fderiv ℂ F z (Y * z)) :=
  if_pos hz

/- English proof (translation)
The claim follows from `if_neg hz`.
-/
theorem lop_off {Y : Matrix (Fin n) (Fin n) ℂ} {F : Matrix (Fin n) (Fin n) ℂ → ℂ}
    {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∉ OmegaSet n) : lop Y F z = 0 :=
  if_neg hz

/- English proof (translation)
The claim follows from `(hF.fderiv_of_isOpen (isOpen_OmegaSet n) (by simp)).clm_apply (mulL Y).contDiff.contDiffOn`.
-/
theorem contDiffOn_dir (Y : Matrix (Fin n) (Fin n) ℂ) {F : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hF : ContDiffOn ℂ ⊤ F (OmegaSet n)) :
    ContDiffOn ℂ ⊤ (fun z => fderiv ℂ F z (mulL Y z)) (OmegaSet n) :=
  (hF.fderiv_of_isOpen (isOpen_OmegaSet n) (by simp)).clm_apply (mulL Y).contDiff.contDiffOn

/- English proof (translation)
Use `⟨?_, fun z hz => lop_off hz⟩` and prove the remaining obligations. Conclude with `(contDiffOn_dir Y hF.1).neg.congr fun z hz => lop_on hz`.
-/
theorem lop_mem {Y : Matrix (Fin n) (Fin n) ℂ} {F : Matrix (Fin n) (Fin n) ℂ → ℂ} (hF : F ∈ OmF n) :
    lop Y F ∈ OmF n := by
  refine ⟨?_, fun z hz => lop_off hz⟩
  exact (contDiffOn_dir Y hF.1).neg.congr fun z hz => lop_on hz

/- English proof (translation)
Establish `hU` using `(isOpen_OmegaSet n).mem_nhds hz`. Establish `hc : ContDiffAt ℂ ⊤ F z` using `hF.contDiffAt hU`. Establish `hd : DifferentiableAt ℂ (fderiv ℂ F) z` using `(hc.fderiv_right (m := ⊤) (by simp)).differentiableAt (by simp)`. Establish `H` using `hd.hasFDerivAt.clm_apply (mulL Y).hasFDerivAt`. Establish `He : lop Y F =ᶠ[nhds z] fun w => -(fderiv ℂ F w (mulL Y w))` using `by filter_upwards [hU] with w hw using lop_on hw`.

Establish `H2` using `H.neg.congr_of_eventuallyEq He`. Establish `h3 : fderiv ℂ (lop Y F) z = _` using `H2.fderiv`. Rewrite using `[lop_on hz, h3]`. Use `show -(-(fderiv ℂ F z (mulL Y (X * z)) + fderiv ℂ (fderiv ℂ F) z (X * z) (mulL Y z))) = _`. Rewrite using `[neg_neg, mulL_apply, mulL_apply, add_comm]`.
-/
theorem lop_lop {X Y : Matrix (Fin n) (Fin n) ℂ} {F : Matrix (Fin n) (Fin n) ℂ → ℂ}
    {z : Matrix (Fin n) (Fin n) ℂ} (hF : ContDiffOn ℂ ⊤ F (OmegaSet n)) (hz : z ∈ OmegaSet n) :
    lop X (lop Y F) z = fderiv ℂ (fderiv ℂ F) z (X * z) (Y * z) + fderiv ℂ F z (Y * (X * z)) := by
  have hU := (isOpen_OmegaSet n).mem_nhds hz
  have hc : ContDiffAt ℂ ⊤ F z := hF.contDiffAt hU
  have hd : DifferentiableAt ℂ (fderiv ℂ F) z :=
    (hc.fderiv_right (m := ⊤) (by simp)).differentiableAt (by simp)
  have H := hd.hasFDerivAt.clm_apply (mulL Y).hasFDerivAt
  have He : lop Y F =ᶠ[nhds z] fun w => -(fderiv ℂ F w (mulL Y w)) := by
    filter_upwards [hU] with w hw using lop_on hw
  have H2 := H.neg.congr_of_eventuallyEq He
  have h3 : fderiv ℂ (lop Y F) z = _ := H2.fderiv
  rw [lop_on hz, h3]
  show -(-(fderiv ℂ F z (mulL Y (X * z)) + fderiv ℂ (fderiv ℂ F) z (X * z) (mulL Y z))) = _
  rw [neg_neg, mulL_apply, mulL_apply, add_comm]

/- English proof (translation)
Use `split_ifs with h`. Substitute `h` using the available equality. Simplify using `[Matrix.single_mul_single_same]`. Simplify using `[Matrix.single_mul_single_of_ne _ _ _ _ h]`.
-/
theorem single_mul_single_eq (a b c d : Fin n) :
    (Matrix.single a b (1 : ℂ)) * Matrix.single c d 1 =
      if b = c then Matrix.single a d 1 else 0 := by
  split_ifs with h
  · subst h; simp [Matrix.single_mul_single_same]
  · simp [Matrix.single_mul_single_of_ne _ _ _ _ h]

/- English proof (translation)
Use function extensionality and compare the values at `z`. Distinguish the cases in `hz : z ∈ OmegaSet n`. Establish `hc : ContDiffAt ℂ ⊤ F z` using `hF.1.contDiffAt ((isOpen_OmegaSet n).mem_nhds hz)`. Establish `hs : IsSymmSndFDerivAt ℂ F z` using `hc.isSymmSndFDerivAt (by simp)`. Establish `hs' : fderiv ℂ (fderiv ℂ F) z (Matrix.single c d 1 * z) (Matrix.single a b 1 * z) = fderiv ℂ (fderiv ℂ F) z (Matrix.single a b 1 * z) (Matrix.single c d 1 * z)` using `hs.eq _ _`.

Simplify using `only [Pi.sub_apply]`. Rewrite using `[lop_lop hF.1 hz, lop_lop hF.1 hz, hs', ← Matrix.mul_assoc, ← Matrix.mul_assoc, single_mul_single_eq, single_mul_single_eq]`. Apply the tactic sequence `by_cases hbc : b = c <;> by_cases hda : d = a <;> simp [hbc, hda, lop_on hz]`. Apply the tactic sequence `all_goals ring`. Apply the tactic sequence `simp only [Pi.sub_apply, lop_off hz] split_ifs <;> simp [lop_off hz]`.
-/
theorem lop_rel {F : Matrix (Fin n) (Fin n) ℂ → ℂ} (a b c d : Fin n) (hF : F ∈ OmF n) :
    lop (Matrix.single a b 1) (lop (Matrix.single c d 1) F) -
        lop (Matrix.single c d 1) (lop (Matrix.single a b 1) F) =
      (if b = c then lop (Matrix.single a d 1) F else 0) -
        (if d = a then lop (Matrix.single c b 1) F else 0) := by
  funext z
  by_cases hz : z ∈ OmegaSet n
  · have hc : ContDiffAt ℂ ⊤ F z := hF.1.contDiffAt ((isOpen_OmegaSet n).mem_nhds hz)
    have hs : IsSymmSndFDerivAt ℂ F z := hc.isSymmSndFDerivAt (by simp)
    have hs' : fderiv ℂ (fderiv ℂ F) z (Matrix.single c d 1 * z) (Matrix.single a b 1 * z) =
        fderiv ℂ (fderiv ℂ F) z (Matrix.single a b 1 * z) (Matrix.single c d 1 * z) := hs.eq _ _
    simp only [Pi.sub_apply]
    rw [lop_lop hF.1 hz, lop_lop hF.1 hz, hs', ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, single_mul_single_eq, single_mul_single_eq]
    by_cases hbc : b = c <;> by_cases hda : d = a <;> simp [hbc, hda, lop_on hz]
    all_goals ring
  · simp only [Pi.sub_apply, lop_off hz]
    split_ifs <;> simp [lop_off hz]

/- English proof (translation)
Distinguish the cases in `h : r = a`. Substitute `h` using the available equality. Simplify using `[Matrix.single_mul_apply_same]`. Simplify using `[h, Matrix.single_mul_apply_of_ne _ _ _ _ _ h]`.
-/
theorem single_mul_apply' (a b r c : Fin n) (z : Matrix (Fin n) (Fin n) ℂ) :
    (Matrix.single a b (1 : ℂ) * z) r c = if r = a then z b c else 0 := by
  by_cases h : r = a
  · subst h; simp [Matrix.single_mul_apply_same]
  · simp [h, Matrix.single_mul_apply_of_ne _ _ _ _ _ h]

/- English proof (translation)
Simplify using `only [lead, hj, dite_true]`. Establish `key : (z + s • (Matrix.single a a 1 * z)).submatrix (Fin.castLE hj) (Fin.castLE hj) = Matrix.diagonal (fun r : Fin j => if Fin.castLE hj r = a then 1 + s else 1) * z.submatrix (Fin.castLE hj) (Fin.castLE hj)`. Use extensionality with `r c`. Rewrite using `[Matrix.diagonal_mul]`. Simplify using `only [Matrix.submatrix_apply, Matrix.add_apply, Matrix.smul_apply, single_mul_apply', smul_eq_mul]`.

Use `split_ifs with h`. Rewrite using `[h]`. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules. Rewrite using `[key, Matrix.det_mul, Matrix.det_diagonal]`.

Use `congr 1`. Distinguish the cases in `h : (a : ℕ) < j`. Rewrite using `[if_pos h, Finset.prod_eq_single (⟨a, h⟩ : Fin j)]`. Simplify using `[Fin.ext_iff]`. Introduce `r _ hr`.

Rewrite using `[if_neg]`. Introduce `e`. Apply `hr` to reduce the goal to its premises. Use `ext`. Simplify `congrArg Fin.val e` using `[Fin.ext_iff]`.

Simplify using the standard rewrite rules. Rewrite using `[if_neg h]`. Apply `Finset.prod_eq_one` to reduce the goal to its premises. Introduce `r _`. Rewrite using `[if_neg]`.

Introduce `e`. Apply `h` to reduce the goal to its premises. Establish `h1` using `r.isLt`. Establish `h2 : (r : ℕ) = a` using `by simpa using congrArg Fin.val e`. Use linear arithmetic over natural numbers and integers.
-/
theorem lead_scale (a : Fin n) (s : ℂ) (z : Matrix (Fin n) (Fin n) ℂ) {j : ℕ} (hj : j ≤ n) :
    lead j (z + s • (Matrix.single a a 1 * z)) = (if (a : ℕ) < j then 1 + s else 1) * lead j z := by
  simp only [lead, hj, dite_true]
  have key : (z + s • (Matrix.single a a 1 * z)).submatrix (Fin.castLE hj) (Fin.castLE hj) =
      Matrix.diagonal (fun r : Fin j => if Fin.castLE hj r = a then 1 + s else 1) *
        z.submatrix (Fin.castLE hj) (Fin.castLE hj) := by
    ext r c
    rw [Matrix.diagonal_mul]
    simp only [Matrix.submatrix_apply, Matrix.add_apply, Matrix.smul_apply, single_mul_apply',
      smul_eq_mul]
    split_ifs with h
    · rw [h]; ring
    · simp
  rw [key, Matrix.det_mul, Matrix.det_diagonal]
  congr 1
  by_cases h : (a : ℕ) < j
  · rw [if_pos h, Finset.prod_eq_single (⟨a, h⟩ : Fin j)]
    · simp [Fin.ext_iff]
    · intro r _ hr
      rw [if_neg]
      intro e
      apply hr
      ext
      simpa [Fin.ext_iff] using congrArg Fin.val e
    · simp
  · rw [if_neg h]
    apply Finset.prod_eq_one
    intro r _
    rw [if_neg]
    intro e
    apply h
    have h1 := r.isLt
    have h2 : (r : ℕ) = a := by simpa using congrArg Fin.val e
    omega

/- English proof (translation)
Distinguish the cases in `hj : j ≤ n`. Simplify using `only [lead, hj, dite_true]`. Distinguish the cases in `h : (a : ℕ) < j`. Establish `hb : (b : ℕ) < j` using `lt_trans (Fin.lt_def.1 hab) h`. Establish `hne : (⟨a, h⟩ : Fin j) ≠ ⟨b, hb⟩`.

Introduce `e`. Establish `: (a : ℕ) = b` using `Fin.mk.inj_iff.1 e`. Conclude with `absurd (Fin.lt_def.1 hab) (by omega)`. Establish `key : (z + s • (Matrix.single a b 1 * z)).submatrix (Fin.castLE hj) (Fin.castLE hj) = Matrix.updateRow (z.submatrix (Fin.castLE hj) (Fin.castLE hj)) ⟨a, h⟩ ((z.submatrix (Fin.castLE hj) (Fin.castLE hj)) ⟨a, h⟩ + s • (z.submatrix (Fin.castLE hj) (Fin.castLE hj)) ⟨b, hb⟩)`. Use extensionality with `r c`.

Distinguish the cases in `hr : r = ⟨a, h⟩`. Substitute `hr` using the available equality. Simplify using `[Matrix.updateRow_self, single_mul_apply', Fin.ext_iff]`. Establish `h3 : Fin.castLE hj r ≠ a`. Introduce `e`.

Apply `hr` to reduce the goal to its premises. Use `ext`. Simplify using `using congrArg Fin.val e`. Simplify using `[Matrix.updateRow_ne hr, single_mul_apply', h3]`. Rewrite using `[key]`.

Conclude with `Matrix.det_updateRow_add_smul_self _ hne s`. Use `congr 1`. Use extensionality with `r c`. Establish `h3 : Fin.castLE hj r ≠ a`. Introduce `e`.

Establish `h1` using `r.isLt`. Establish `h2 : (r : ℕ) = a` using `by simpa using congrArg Fin.val e`. Use linear arithmetic over natural numbers and integers. Simplify using `[single_mul_apply', h3]`. Simplify using `[lead, hj]`.
-/
theorem lead_rowop {a b : Fin n} (hab : b < a) (s : ℂ) (z : Matrix (Fin n) (Fin n) ℂ) (j : ℕ) :
    lead j (z + s • (Matrix.single a b 1 * z)) = lead j z := by
  by_cases hj : j ≤ n
  · simp only [lead, hj, dite_true]
    by_cases h : (a : ℕ) < j
    · have hb : (b : ℕ) < j := lt_trans (Fin.lt_def.1 hab) h
      have hne : (⟨a, h⟩ : Fin j) ≠ ⟨b, hb⟩ := by
        intro e
        have : (a : ℕ) = b := Fin.mk.inj_iff.1 e
        exact absurd (Fin.lt_def.1 hab) (by omega)
      have key : (z + s • (Matrix.single a b 1 * z)).submatrix (Fin.castLE hj) (Fin.castLE hj) =
          Matrix.updateRow (z.submatrix (Fin.castLE hj) (Fin.castLE hj)) ⟨a, h⟩
            ((z.submatrix (Fin.castLE hj) (Fin.castLE hj)) ⟨a, h⟩ +
              s • (z.submatrix (Fin.castLE hj) (Fin.castLE hj)) ⟨b, hb⟩) := by
        ext r c
        by_cases hr : r = ⟨a, h⟩
        · subst hr
          simp [Matrix.updateRow_self, single_mul_apply', Fin.ext_iff]
        · have h3 : Fin.castLE hj r ≠ a := by
            intro e
            apply hr
            ext
            simpa using congrArg Fin.val e
          simp [Matrix.updateRow_ne hr, single_mul_apply', h3]
      rw [key]
      exact Matrix.det_updateRow_add_smul_self _ hne s
    · congr 1
      ext r c
      have h3 : Fin.castLE hj r ≠ a := by
        intro e
        have h1 := r.isLt
        have h2 : (r : ℕ) = a := by simpa using congrArg Fin.val e
        omega
      simp [single_mul_apply', h3]
  · simp [lead, hj]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, zpow_add₀ hu]`.
-/
theorem prod_zpow_eq {ι : Type*} (s : Finset ι) (f : ι → ℤ) {u : ℂ} (hu : u ≠ 0) :
    ∏ i ∈ s, u ^ f i = u ^ ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, zpow_add₀ hu]

/- English proof (translation)
Use `set m : ℕ → ℤ := fun i => if h : i < n then μ ⟨i, h⟩ else 0 with hmdef`. Establish `hm : ∀ i : Fin n, (if a ≤ i then -(μ i - muNext μ i) else 0) = (fun i : ℕ => if (a : ℕ) ≤ i then m (i + 1) - m i else 0) (i : ℕ)`. Introduce `i`. Simplify using `only [hmdef, muNext, Fin.le_def, i.isLt, dite_true, Fin.eta]`. Apply the tactic sequence `split_ifs <;> ring`.

Repeatedly rewrite using `[hm]`. Rewrite using `[Fin.sum_univ_eq_sum_range (fun i : ℕ => if (a : ℕ) ≤ i then m (i + 1) - m i else 0) n]`. Establish `key : ∀ N, (a : ℕ) ≤ N → ∑ i ∈ Finset.range N, (if (a : ℕ) ≤ i then m (i + 1) - m i else 0) = m N - m a`. Introduce `N hN`. Proceed by induction on `N, hN using Nat.le_induction with`.

Consider the case `base`. Rewrite using `[sub_self]`. Use `Finset.sum_eq_zero fun i hi => if_neg ?_` and prove the remaining obligations. Use `Finset.mem_range.1 hi` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Consider the case `succ N hN ih => rw [Finset.sum_range_succ, ih, if_pos hN]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key n a.isLt.le]`. Simplify using `[hmdef]`.
-/
theorem sum_tele (μ : Fin n → ℤ) (a : Fin n) :
    ∑ i : Fin n, (if a ≤ i then -(μ i - muNext μ i) else 0) = -μ a := by
  set m : ℕ → ℤ := fun i => if h : i < n then μ ⟨i, h⟩ else 0 with hmdef
  have hm : ∀ i : Fin n, (if a ≤ i then -(μ i - muNext μ i) else 0) =
      (fun i : ℕ => if (a : ℕ) ≤ i then m (i + 1) - m i else 0) (i : ℕ) := by
    intro i
    simp only [hmdef, muNext, Fin.le_def, i.isLt, dite_true, Fin.eta]
    split_ifs <;> ring
  simp_rw [hm]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => if (a : ℕ) ≤ i then m (i + 1) - m i else 0) n]
  have key : ∀ N, (a : ℕ) ≤ N →
      ∑ i ∈ Finset.range N, (if (a : ℕ) ≤ i then m (i + 1) - m i else 0) = m N - m a := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base =>
      rw [sub_self]
      refine Finset.sum_eq_zero fun i hi => if_neg ?_
      have := Finset.mem_range.1 hi
      omega
    | succ N hN ih => rw [Finset.sum_range_succ, ih, if_pos hN]; ring
  rw [key n a.isLt.le]
  simp [hmdef]

/- English proof (translation)
Unfold `PhiM`. Establish `key : ∀ i : Fin n, lead ((i : ℕ) + 1) (z + s • (Matrix.single a a 1 * z)) ^ (-(μ i - muNext μ i)) = (1 + s) ^ (if a ≤ i then -(μ i - muNext μ i) else 0) * lead ((i : ℕ) + 1) z ^ (-(μ i - muNext μ i))`. Introduce `i`. Rewrite using `[lead_scale a s z (i.isLt : (i : ℕ) + 1 ≤ n)]`. Distinguish the cases in `h : a ≤ i`.

Establish `h' : (a : ℕ) < (i : ℕ) + 1` using `Nat.lt_succ_of_le (Fin.le_def.1 h)`. Rewrite using `[if_pos h', if_pos h, mul_zpow]`. Establish `h' : ¬ (a : ℕ) < (i : ℕ) + 1` using `fun e => h (Fin.le_def.2 (Nat.le_of_lt_succ e))`. Rewrite using `[if_neg h', if_neg h]`. Simplify using the standard rewrite rules.

Repeatedly rewrite using `[key]`. Rewrite using `[Finset.prod_mul_distrib, prod_zpow_eq _ _ hs, sum_tele]`.
-/
theorem PhiM_scale (μ : Fin n → ℤ) (a : Fin n) {s : ℂ} (z : Matrix (Fin n) (Fin n) ℂ) (hs : 1 + s ≠ 0) :
    PhiM μ (z + s • (Matrix.single a a 1 * z)) = (1 + s) ^ (-μ a) * PhiM μ z := by
  unfold PhiM
  have key : ∀ i : Fin n, lead ((i : ℕ) + 1) (z + s • (Matrix.single a a 1 * z)) ^ (-(μ i - muNext μ i)) =
      (1 + s) ^ (if a ≤ i then -(μ i - muNext μ i) else 0) * lead ((i : ℕ) + 1) z ^ (-(μ i - muNext μ i)) := by
    intro i
    rw [lead_scale a s z (i.isLt : (i : ℕ) + 1 ≤ n)]
    by_cases h : a ≤ i
    · have h' : (a : ℕ) < (i : ℕ) + 1 := Nat.lt_succ_of_le (Fin.le_def.1 h)
      rw [if_pos h', if_pos h, mul_zpow]
    · have h' : ¬ (a : ℕ) < (i : ℕ) + 1 := fun e => h (Fin.le_def.2 (Nat.le_of_lt_succ e))
      rw [if_neg h', if_neg h]
      simp
  simp_rw [key]
  rw [Finset.prod_mul_distrib, prod_zpow_eq _ _ hs, sum_tele]

/- English proof (translation)
Simplify using `only [PhiM, lead_rowop hab]`.
-/
theorem PhiM_rowop (μ : Fin n → ℤ) {a b : Fin n} (hab : b < a) (s : ℂ) (z : Matrix (Fin n) (Fin n) ℂ) :
    PhiM μ (z + s • (Matrix.single a b 1 * z)) = PhiM μ z := by
  simp only [PhiM, lead_rowop hab]

/- English proof (translation)
The claim follows from `Set.indicator_of_mem hz _`.
-/
theorem PhiO_on {μ : Fin n → ℤ} {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ OmegaSet n) :
    PhiO μ z = PhiM μ z :=
  Set.indicator_of_mem hz _

/- English proof (translation)
The claim follows from `Set.indicator_of_notMem hz _`.
-/
theorem PhiO_off {μ : Fin n → ℤ} {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∉ OmegaSet n) :
    PhiO μ z = 0 :=
  Set.indicator_of_notMem hz _

/- English proof (translation)
Establish `hl : ContDiffAt ℂ ⊤ (lead j : Matrix (Fin n) (Fin n) ℂ → ℂ) z` using `(contDiff_lead j).contDiffAt`. Take `⟨m, rfl | rfl⟩` from `k.eq_nat_or_neg`. Simplify `hl.pow m` using `only [zpow_natCast]`. Simplify using `only [_root_.zpow_neg, zpow_natCast]`. Conclude with `(hl.pow m).inv (pow_ne_zero _ h)`.
-/
theorem contDiffAt_lead_zpow (j : ℕ) (k : ℤ) {z : Matrix (Fin n) (Fin n) ℂ} (h : lead j z ≠ 0) :
    ContDiffAt ℂ ⊤ (fun z : Matrix (Fin n) (Fin n) ℂ => lead j z ^ k) z := by
  have hl : ContDiffAt ℂ ⊤ (lead j : Matrix (Fin n) (Fin n) ℂ → ℂ) z := (contDiff_lead j).contDiffAt
  obtain ⟨m, rfl | rfl⟩ := k.eq_nat_or_neg
  · simpa only [zpow_natCast] using hl.pow m
  · simp only [_root_.zpow_neg, zpow_natCast]
    exact (hl.pow m).inv (pow_ne_zero _ h)

/- English proof (translation)
Introduce `z hz`. Establish `h : ContDiffAt ℂ ⊤ (PhiM μ) z`. Establish `: PhiM μ = fun z => ∏ i : Fin n, lead ((i : ℕ) + 1) z ^ (-(μ i - muNext μ i))` using `rfl`. Rewrite using `[this]`. Use `contDiffAt_prod fun i _ => ?_` and prove the remaining obligations.

Conclude with `contDiffAt_lead_zpow _ _ (hz i)`. Conclude with `h.contDiffWithinAt`.
-/
theorem contDiffOn_PhiM (μ : Fin n → ℤ) : ContDiffOn ℂ ⊤ (PhiM μ) (OmegaSet n) := by
  intro z hz
  have h : ContDiffAt ℂ ⊤ (PhiM μ) z := by
    have : PhiM μ = fun z => ∏ i : Fin n, lead ((i : ℕ) + 1) z ^ (-(μ i - muNext μ i)) := rfl
    rw [this]
    refine contDiffAt_prod fun i _ => ?_
    exact contDiffAt_lead_zpow _ _ (hz i)
  exact h.contDiffWithinAt

/- English proof (translation)
Assemble the required witnesses or components as `⟨(contDiffOn_PhiM μ).congr fun _ hz => PhiO_on hz, fun _ hz => PhiO_off hz⟩`.
-/
theorem PhiO_mem (μ : Fin n → ℤ) : PhiO μ ∈ OmF n :=
  ⟨(contDiffOn_PhiM μ).congr fun _ hz => PhiO_on hz, fun _ hz => PhiO_off hz⟩

/- English proof (translation)
Establish `h1 : HasDerivAt (fun s : ℂ => F (z + s • v)) (fderiv ℂ F z v) 0` using `hF.hasFDerivAt.hasLineDerivAt v`. Conclude with `h1.unique (hg.congr_of_eventuallyEq he)`.
-/
theorem fderiv_dir_eq {F : Matrix (Fin n) (Fin n) ℂ → ℂ} {z v : Matrix (Fin n) (Fin n) ℂ}
    {g : ℂ → ℂ} {c : ℂ} (hF : DifferentiableAt ℂ F z) (hg : HasDerivAt g c 0)
    (he : ∀ᶠ s in nhds (0 : ℂ), F (z + s • v) = g s) : fderiv ℂ F z v = c := by
  have h1 : HasDerivAt (fun s : ℂ => F (z + s • v)) (fderiv ℂ F z v) 0 :=
    hF.hasFDerivAt.hasLineDerivAt v
  exact h1.unique (hg.congr_of_eventuallyEq he)

/- English proof (translation)
The claim follows from `((PhiO_mem μ).1.contDiffAt ((isOpen_OmegaSet n).mem_nhds hz)).differentiableAt (by simp)`.
-/
theorem PhiO_differentiableAt (μ : Fin n → ℤ) {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ OmegaSet n) :
    DifferentiableAt ℂ (PhiO μ) z :=
  ((PhiO_mem μ).1.contDiffAt ((isOpen_OmegaSet n).mem_nhds hz)).differentiableAt (by simp)

/- English proof (translation)
Use function extensionality and compare the values at `z`. Distinguish the cases in `hz : z ∈ OmegaSet n`. Establish `hg : HasDerivAt (fun s : ℂ => (1 + s) ^ (-μ a) * PhiM μ z) (-(μ a : ℂ) * PhiM μ z) 0`. Establish `h0` using `hasDerivAt_zpow (𝕜 := ℂ) (-μ a) (1 + 0) (Or.inl (by simp))`. Establish `h1` using `(h0.comp_const_add 1 0).mul_const (PhiM μ z)`.

Simplify using `using h1`. Establish `he : ∀ᶠ s in nhds (0 : ℂ), PhiO μ (z + s • (Matrix.single a a 1 * z)) = (1 + s) ^ (-μ a) * PhiM μ z`. Establish `h1 : ∀ᶠ s in nhds (0 : ℂ), 1 + s ≠ 0`. Establish `hc : ContinuousAt (fun s : ℂ => 1 + s) 0` using `by fun_prop`. Conclude with `hc.eventually_ne (by simp)`.

Use `filter_upwards [h1] with s hs`. Establish `hmem : z + s • (Matrix.single a a 1 * z) ∈ OmegaSet n`. Introduce `i`. Rewrite using `[lead_scale a s z (i.isLt : (i : ℕ) + 1 ≤ n)]`. Apply the tactic sequence `exact mul_ne_zero (by split_ifs <;> simp [hs]) (hz i)`.

Rewrite using `[PhiO_on hmem, PhiM_scale μ a z hs]`. Rewrite using `[lop_on hz, fderiv_dir_eq (PhiO_differentiableAt μ hz) hg he, Pi.smul_apply, PhiO_on hz]`. Simplify using the standard rewrite rules. Simplify using `[lop_off hz, PhiO_off hz]`.
-/
theorem PhiO_weight (μ : Fin n → ℤ) (a : Fin n) :
    lop (Matrix.single a a 1) (PhiO μ) = ((μ a : ℤ) : ℂ) • PhiO μ := by
  funext z
  by_cases hz : z ∈ OmegaSet n
  · have hg : HasDerivAt (fun s : ℂ => (1 + s) ^ (-μ a) * PhiM μ z)
        (-(μ a : ℂ) * PhiM μ z) 0 := by
      have h0 := hasDerivAt_zpow (𝕜 := ℂ) (-μ a) (1 + 0) (Or.inl (by simp))
      have h1 := (h0.comp_const_add 1 0).mul_const (PhiM μ z)
      simpa using h1
    have he : ∀ᶠ s in nhds (0 : ℂ), PhiO μ (z + s • (Matrix.single a a 1 * z)) =
        (1 + s) ^ (-μ a) * PhiM μ z := by
      have h1 : ∀ᶠ s in nhds (0 : ℂ), 1 + s ≠ 0 := by
        have hc : ContinuousAt (fun s : ℂ => 1 + s) 0 := by fun_prop
        exact hc.eventually_ne (by simp)
      filter_upwards [h1] with s hs
      have hmem : z + s • (Matrix.single a a 1 * z) ∈ OmegaSet n := by
        intro i
        rw [lead_scale a s z (i.isLt : (i : ℕ) + 1 ≤ n)]
        exact mul_ne_zero (by split_ifs <;> simp [hs]) (hz i)
      rw [PhiO_on hmem, PhiM_scale μ a z hs]
    rw [lop_on hz, fderiv_dir_eq (PhiO_differentiableAt μ hz) hg he, Pi.smul_apply, PhiO_on hz]
    simp
  · simp [lop_off hz, PhiO_off hz]

/- English proof (translation)
Use function extensionality and compare the values at `z`. Distinguish the cases in `hz : z ∈ OmegaSet n`. Establish `he : ∀ᶠ s in nhds (0 : ℂ), PhiO μ (z + s • (Matrix.single a b 1 * z)) = (fun _ : ℂ => PhiM μ z) s`. Use `Filter.Eventually.of_forall fun s => ?_` and prove the remaining obligations. Establish `hmem : z + s • (Matrix.single a b 1 * z) ∈ OmegaSet n`.

Introduce `i`. Rewrite using `[lead_rowop hab]`. Conclude with `hz i`. Rewrite using `[PhiO_on hmem, PhiM_rowop μ hab]`. Rewrite using `[lop_on hz, fderiv_dir_eq (PhiO_differentiableAt μ hz) (hasDerivAt_const _ _) he]`.

Simplify using the standard rewrite rules. Simplify using `[lop_off hz]`.
-/
theorem PhiO_lower (μ : Fin n → ℤ) {a b : Fin n} (hab : b < a) :
    lop (Matrix.single a b 1) (PhiO μ) = 0 := by
  funext z
  by_cases hz : z ∈ OmegaSet n
  · have he : ∀ᶠ s in nhds (0 : ℂ), PhiO μ (z + s • (Matrix.single a b 1 * z)) =
        (fun _ : ℂ => PhiM μ z) s := by
      refine Filter.Eventually.of_forall fun s => ?_
      have hmem : z + s • (Matrix.single a b 1 * z) ∈ OmegaSet n := by
        intro i
        rw [lead_rowop hab]
        exact hz i
      rw [PhiO_on hmem, PhiM_rowop μ hab]
    rw [lop_on hz, fderiv_dir_eq (PhiO_differentiableAt μ hz) (hasDerivAt_const _ _) he]
    simp
  · simp [lop_off hz]

end GlobalTheory.CompanionTheory.HolOm

/- English proof (translation)
Introduce `_ μ` and use `⟨fun _ _ hF => GlobalTheory.CompanionTheory.HolOm.lop_mem hF, fun _ a b c d hF => GlobalTheory.CompanionTheory.HolOm.lop_rel a b c d hF, GlobalTheory.CompanionTheory.HolOm.PhiO_mem μ, GlobalTheory.CompanionTheory.HolOm.PhiO_weight μ, fun _ _ hab => GlobalTheory.CompanionTheory.Ho …`.
-/
theorem GlobalTheory.CompanionTheory.HolOm.holFacts : PositivityTheory.RgDs.K.HolFacts := fun _ μ =>
  ⟨fun _ _ hF => GlobalTheory.CompanionTheory.HolOm.lop_mem hF, fun _ a b c d hF => GlobalTheory.CompanionTheory.HolOm.lop_rel a b c d hF,
    GlobalTheory.CompanionTheory.HolOm.PhiO_mem μ, GlobalTheory.CompanionTheory.HolOm.PhiO_weight μ, fun _ _ hab => GlobalTheory.CompanionTheory.HolOm.PhiO_lower μ hab⟩
