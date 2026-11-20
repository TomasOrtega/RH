import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HasStepCharts
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SelM

noncomputable section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW.GrChart

variable {N m : ℕ}

/- English proof (translation)
Use `choose σ₀ hσ₀ using fun i => Set.mem_range.mp (h (Set.mem_range_self i))`. Establish `hinj : Function.Injective σ₀` using `fun a b hab => hφ (by rw [← hσ₀ a, ← hσ₀ b, hab])`. Use `⟨Equiv.ofBijective σ₀ (Finite.injective_iff_bijective.mp hinj), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Conclude with `(hσ₀ i).symm`.
-/
theorem exists_perm_of_range (φ g : Fin m → Fin N) (hφ : Function.Injective φ)
    (h : Set.range φ ⊆ Set.range g) : ∃ σ : Equiv.Perm (Fin m), φ = g ∘ σ := by
  choose σ₀ hσ₀ using fun i => Set.mem_range.mp (h (Set.mem_range_self i))
  have hinj : Function.Injective σ₀ := fun a b hab => hφ (by rw [← hσ₀ a, ← hσ₀ b, hab])
  refine ⟨Equiv.ofBijective σ₀ (Finite.injective_iff_bijective.mp hinj), ?_⟩
  funext i
  exact (hσ₀ i).symm

/- English proof (translation)
Establish `hT : (Finset.univ.image φ).card = S.card`. Rewrite using `[Finset.card_image_of_injective _ hφ, Finset.card_univ, Fintype.card_fin]`. Take `⟨σ, hσ⟩` from `exists_perm_of_range φ ((Finset.univ.image φ).orderEmbOfFin hT) hφ (by`. Rewrite using `[Finset.range_orderEmbOfFin]`. Introduce and unpack `_ ⟨i, rfl⟩`.

Use the proof step `simp)`. Use `⟨((Equiv.Perm.sign σ : ℤ) : ℂ), fun h => ?_⟩` and prove the remaining obligations. Rewrite using `[minorIJ, dif_pos hT]`. Establish `key : h.submatrix φ (S.orderEmbOfFin rfl) = (h.submatrix ((Finset.univ.image φ).orderEmbOfFin hT) (S.orderEmbOfFin rfl)).submatrix σ id`. Use extensionality with `x t`.

Simplify using `only [Matrix.submatrix_apply, id]`. Rewrite using `[congrFun hσ x]`. Both sides reduce to the same expression. Rewrite using `[key, Matrix.det_permute]`.
-/
theorem exists_sign (S : Finset (Fin N)) (φ : Fin S.card → Fin N) (hφ : Function.Injective φ) :
    ∃ ε : ℂ, ∀ h : Matrix (Fin N) (Fin N) ℂ,
      (h.submatrix φ (S.orderEmbOfFin rfl)).det = ε * minorIJ h (Finset.univ.image φ) S := by
  have hT : (Finset.univ.image φ).card = S.card := by
    rw [Finset.card_image_of_injective _ hφ, Finset.card_univ, Fintype.card_fin]
  obtain ⟨σ, hσ⟩ := exists_perm_of_range φ ((Finset.univ.image φ).orderEmbOfFin hT) hφ (by
    rw [Finset.range_orderEmbOfFin]
    rintro _ ⟨i, rfl⟩
    simp)
  refine ⟨((Equiv.Perm.sign σ : ℤ) : ℂ), fun h => ?_⟩
  rw [minorIJ, dif_pos hT]
  have key : h.submatrix φ (S.orderEmbOfFin rfl) =
      (h.submatrix ((Finset.univ.image φ).orderEmbOfFin hT) (S.orderEmbOfFin rfl)).submatrix σ id := by
    ext x t
    simp only [Matrix.submatrix_apply, id]
    rw [congrFun hσ x]
    rfl
  rw [key, Matrix.det_permute]

/- English proof (translation)
Set `f' : Fin m ↪ {x // x ∈ A}` to `⟨fun s => ⟨f s, hfA s⟩, fun a b hab => hf (congrArg Subtype.val hab)⟩`. Set `e' : Fin m ↪ {x // x ∈ A}` to `⟨fun s => ⟨e s, heA s⟩, fun a b hab => he (congrArg Subtype.val hab)⟩`. Set `q : Set.range f' ≃ Set.range e'` to `f'.toEquivRange.symm.trans e'.toEquivRange`. Use `⟨Equiv.Perm.ofSubtype (Equiv.extendSubtype q), fun s => ?_, fun c hc => ?_, fun c hc => ?_⟩` and prove the remaining obligations. Rewrite using `[Equiv.Perm.ofSubtype_apply_of_mem _ (hfA s)]`.

Establish `hx : (⟨f s, hfA s⟩ : {x // x ∈ A}) = f' s` using `rfl`. Rewrite using `[hx, Equiv.extendSubtype_apply_of_mem q (f' s) (Set.mem_range_self s)]`. Simplify using `[q, Function.Embedding.toEquivRange_symm_apply_self, e']`. Both sides reduce to the same expression. Conclude with `Equiv.Perm.ofSubtype_apply_of_not_mem _ hc`.

Rewrite using `[Equiv.Perm.ofSubtype_apply_of_mem _ hc]`. Conclude with `Subtype.property _`.
-/
theorem exists_perm_ext (A : Finset (Fin N)) (f e : Fin m → Fin N) (hf : Function.Injective f)
    (he : Function.Injective e) (hfA : ∀ s, f s ∈ A) (heA : ∀ s, e s ∈ A) :
    ∃ π : Equiv.Perm (Fin N), (∀ s, π (f s) = e s) ∧ (∀ c, c ∉ A → π c = c) ∧ ∀ c ∈ A, π c ∈ A := by
  let f' : Fin m ↪ {x // x ∈ A} := ⟨fun s => ⟨f s, hfA s⟩, fun a b hab => hf (congrArg Subtype.val hab)⟩
  let e' : Fin m ↪ {x // x ∈ A} := ⟨fun s => ⟨e s, heA s⟩, fun a b hab => he (congrArg Subtype.val hab)⟩
  let q : Set.range f' ≃ Set.range e' := f'.toEquivRange.symm.trans e'.toEquivRange
  refine ⟨Equiv.Perm.ofSubtype (Equiv.extendSubtype q), fun s => ?_, fun c hc => ?_, fun c hc => ?_⟩
  · rw [Equiv.Perm.ofSubtype_apply_of_mem _ (hfA s)]
    have hx : (⟨f s, hfA s⟩ : {x // x ∈ A}) = f' s := rfl
    rw [hx, Equiv.extendSubtype_apply_of_mem q (f' s) (Set.mem_range_self s)]
    simp [q, Function.Embedding.toEquivRange_symm_apply_self, e']
    rfl
  · exact Equiv.Perm.ofSubtype_apply_of_not_mem _ hc
  · rw [Equiv.Perm.ofSubtype_apply_of_mem _ hc]
    exact Subtype.property _

/- English proof (translation)
Establish `hA : A₀.updateRow s b = ((A₀ᵀ).updateCol s b)ᵀ`. Rewrite using `[← Matrix.updateRow_transpose, Matrix.transpose_transpose]`. Rewrite using `[hA, Matrix.det_transpose, ← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec, ← Matrix.adjugate_transpose]`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]`. Conclude with `Finset.sum_congr rfl fun t _ => mul_comm _ _`.
-/
theorem sum_mul_adjugate (A₀ : Matrix (Fin m) (Fin m) ℂ) (b : Fin m → ℂ) (s : Fin m) :
    ∑ t, b t * A₀.adjugate t s = (A₀.updateRow s b).det := by
  have hA : A₀.updateRow s b = ((A₀ᵀ).updateCol s b)ᵀ := by
    rw [← Matrix.updateRow_transpose, Matrix.transpose_transpose]
  rw [hA, Matrix.det_transpose, ← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec,
    ← Matrix.adjugate_transpose]
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  exact Finset.sum_congr rfl fun t _ => mul_comm _ _

def rowsOf (e : Fin m → Fin N) (r : Fin N) (s : Fin m) : Finset (Fin N) :=
  Finset.univ.image (Function.update e s r)

def coefM (R : Finset (Fin N)) (e : Fin m → Fin N) (ε : Fin N → Fin m → ℂ) (I : Finset (Fin N)) :
    Matrix (Fin N) (Fin N) ℂ :=
  fun r c => if r ∈ R then ∑ s, if c = e s ∧ rowsOf e r s = I then ε r s else 0 else 0

def movM (R : Finset (Fin N)) (e : Fin m → Fin N) (ε : Fin N → Fin m → ℂ) (u : Finset (Fin N) → ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  fun r c => if r ∈ R then ∑ s, if c = e s then ε r s * u (rowsOf e r s) else 0 else 0

/- English proof (translation)
Use extensionality with `r c`. Simplify using `only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, coefM, movM]`. Distinguish the cases in `hr : r ∈ R`. Simplify using `only [if_pos hr]`. Repeatedly rewrite using `[Finset.mul_sum]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Distinguish the cases in `hc : c = e s`. Simplify using `[hc, mul_comm]`. Simplify using `[hc]`.

Simplify using `[hr]`.
-/
theorem sum_smul_coefM (R : Finset (Fin N)) (e : Fin m → Fin N) (ε : Fin N → Fin m → ℂ)
    (u : Finset (Fin N) → ℂ) : ∑ I, u I • coefM R e ε I = movM R e ε u := by
  ext r c
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, coefM, movM]
  by_cases hr : r ∈ R
  · simp only [if_pos hr]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    by_cases hc : c = e s
    · simp [hc, mul_comm]
    · simp [hc]
  · simp [hr]

/- English proof (translation)
Simplify using `[movM, hc]`.
-/
theorem movM_of_not_range (R : Finset (Fin N)) (e : Fin m → Fin N) (ε : Fin N → Fin m → ℂ)
    (u : Finset (Fin N) → ℂ) (r c : Fin N) (hc : ∀ s, c ≠ e s) : movM R e ε u r c = 0 := by
  simp [movM, hc]

/- English proof (translation)
Simplify using `[movM, hr]`.
-/
theorem movM_of_not_mem (R : Finset (Fin N)) (e : Fin m → Fin N) (ε : Fin N → Fin m → ℂ)
    (u : Finset (Fin N) → ℂ) (r c : Fin N) (hr : r ∉ R) : movM R e ε u r c = 0 := by
  simp [movM, hr]

/- English proof (translation)
Simplify using `[movM, hr, he.eq_iff]`.
-/
theorem movM_apply (R : Finset (Fin N)) {e : Fin m → Fin N} (he : Function.Injective e)
    (ε : Fin N → Fin m → ℂ) (u : Finset (Fin N) → ℂ) {r : Fin N} (hr : r ∈ R) (s : Fin m) :
    movM R e ε u r (e s) = ε r s * u (rowsOf e r s) := by
  simp [movM, hr, he.eq_iff]

/- English proof (translation)
Use extensionality with `r c`. Rewrite using `[Matrix.mul_apply, Matrix.zero_apply]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `x _`. Distinguish the cases in `hx : x ∈ R`.

Rewrite using `[movM_of_not_range R e ε u r x (fun s => hR x hx s), zero_mul]`. Rewrite using `[movM_of_not_mem R e ε u x c hx, mul_zero]`.
-/
theorem movM_sq (R : Finset (Fin N)) (e : Fin m → Fin N) (ε : Fin N → Fin m → ℂ)
    (u : Finset (Fin N) → ℂ) (hR : ∀ r ∈ R, ∀ s, r ≠ e s) : movM R e ε u * movM R e ε u = 0 := by
  ext r c
  rw [Matrix.mul_apply, Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro x _
  by_cases hx : x ∈ R
  · rw [movM_of_not_range R e ε u r x (fun s => hR x hx s), zero_mul]
  · rw [movM_of_not_mem R e ε u x c hx, mul_zero]

/- English proof (translation)
Establish `h2` using `movM_sq R e ε u hR`. Establish `hinv : (1 + movM R e ε u) * (1 - movM R e ε u) = 1`. Rewrite using `[add_mul, one_mul, mul_sub, mul_one, h2, sub_zero, sub_add_cancel]`. Introduce `h0`. Establish `hd` using `congrArg Matrix.det hinv`.

Rewrite `hd` using `[Matrix.det_mul, h0, zero_mul, Matrix.det_one]`. Conclude with `zero_ne_one hd`.
-/
theorem det_one_add_movM_ne (R : Finset (Fin N)) (e : Fin m → Fin N) (ε : Fin N → Fin m → ℂ)
    (u : Finset (Fin N) → ℂ) (hR : ∀ r ∈ R, ∀ s, r ≠ e s) : (1 + movM R e ε u).det ≠ 0 := by
  have h2 := movM_sq R e ε u hR
  have hinv : (1 + movM R e ε u) * (1 - movM R e ε u) = 1 := by
    rw [add_mul, one_mul, mul_sub, mul_one, h2, sub_zero, sub_add_cancel]
  intro h0
  have hd := congrArg Matrix.det hinv
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at hd
  exact zero_ne_one hd

/- English proof (translation)
Rewrite using `[← sum_smul_coefM]`. Use extensionality with `r c`. Simplify using `only [grMat, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.submatrix_apply, id_eq, smul_eq_mul]`. Both sides reduce to the same expression.
-/
private theorem core_lemma (R : Finset (Fin N)) (e : Fin m → Fin N) (ε : Fin N → Fin m → ℂ)
    (π : Equiv.Perm (Fin N)) (I₀ : Finset (Fin N)) (w : Finset (Fin N) → ℂ) :
    grMat ((1 : Matrix (Fin N) (Fin N) ℂ).submatrix id π.symm)
      (fun I => (coefM R e ε I).submatrix id π.symm) I₀ w =
      (1 + movM R e ε (fun I => w I / w I₀)).submatrix id π.symm := by
  rw [← sum_smul_coefM]
  ext r c
  simp only [grMat, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.submatrix_apply, id_eq, smul_eq_mul]
  rfl

/- English proof (translation)
Use `set e : Fin S.card → Fin N := ⇑(I₀.orderEmbOfFin hc) with he_def`. Use `set f : Fin S.card → Fin N := ⇑(S.orderEmbOfFin rfl) with hf_def`. Establish `he : Function.Injective e` using `(I₀.orderEmbOfFin hc).injective`. Establish `hf : Function.Injective f` using `(S.orderEmbOfFin rfl).injective`. Establish `heI : ∀ s, e s ∈ I₀` using `fun s => Finset.orderEmbOfFin_mem I₀ hc s`.

Establish `hfS : ∀ s, f s ∈ S` using `fun s => Finset.orderEmbOfFin_mem S rfl s`. Establish `heA : ∀ s, e s ∈ A` using `fun s => hI (heI s)`. Establish `hfA : ∀ s, f s ∈ A` using `fun s => hS (hfS s)`. Take `⟨π, hπ, hπout, hπA⟩` from `exists_perm_ext A e f he hf heA hfA`. Use `set R : Finset (Fin N) := A \ I₀ with hR_def`.

Establish `hR : ∀ r ∈ R, ∀ s, r ≠ e s`. Introduce `r hr s hrs`. Conclude with `(Finset.mem_sdiff.mp hr).2 (by rw [hrs]; exact heI s)`. Establish `hupd : ∀ r ∈ R, ∀ s, Function.Injective (Function.update e s r)`. Introduce `r hr s x y hxy`.

Establish `hrI : r ∉ I₀` using `(Finset.mem_sdiff.mp hr).2`. Simplify using `only [Function.update_apply] at hxy`. Use `split_ifs at hxy with hx hy hy`. Rewrite using `[hx, hy]`. Conclude with `absurd (show r ∈ I₀ by rw [hxy]; exact heI y) hrI`.

Conclude with `absurd (show r ∈ I₀ by rw [← hxy]; exact heI x) hrI`. Conclude with `he hxy`. Establish `hex : ∀ (r : Fin N) (s : Fin S.card), ∃ c : ℂ, r ∈ R → ∀ h : Matrix (Fin N) (Fin N) ℂ, (h.submatrix (Function.update e s r) (S.orderEmbOfFin rfl)).det = c * minorIJ h (rowsOf e r s) S`. Introduce `r s`. Distinguish the cases in `hr : r ∈ R`.

Take `⟨c, hc'⟩` from `exists_sign S (Function.update e s r) (hupd r hr s)`. Conclude with `⟨c, fun _ => hc'⟩`. Conclude with `⟨0, fun h => absurd h hr⟩`. Use `choose ε hε using hex`. Use `⟨(1 : Matrix (Fin N) (Fin N) ℂ).submatrix id π.symm, fun I => (coefM R e ε I).submatrix id π.symm, ?_⟩` and prove the remaining obligations.

Introduce `h a w hbd ha hw hw0`. Establish `hG` using `core_lemma R e ε π I₀ w`. Use `set u : Finset (Fin N) → ℂ := fun I => w I / w I₀ with hu_def`. Rewrite using `[hG]`. Establish `hGe : ∀ r c, ((1 + movM R e ε u).submatrix id π.symm) r c = (1 + movM R e ε u) r (π.symm c)` using `fun r c => rfl`.

Establish `hw0' : w I₀ = a * (h.submatrix e f).det`. Rewrite using `[hw I₀ hc hI, minorIJ, dif_pos hc]`. Establish `hD : (h.submatrix e f).det ≠ 0`. Introduce `h0`. Apply `hw0` to reduce the goal to its premises.

Rewrite using `[hw0', h0, mul_zero]`. Establish `hX : ∀ r s, (1 + movM R e ε u) r (e s) = ((h.submatrix id f) * (h.submatrix e f)⁻¹) r s`. Introduce `r s`. Rewrite using `[Matrix.add_apply]`. Distinguish the cases in `hrA : r ∈ A`.

Distinguish the cases in `hrI : r ∈ I₀`. Choose the witnesses or unpack the hypotheses as in `⟨s', rfl⟩ : ∃ s', e s' = r := by`. Establish `hmem : r ∈ Set.range e`. Rewrite using `[he_def, Finset.range_orderEmbOfFin]`. Conclude with `hrI`.

Conclude with `hmem`. Rewrite using `[movM_of_not_mem R e ε u _ _ (fun h' => (Finset.mem_sdiff.mp h').2 hrI), add_zero]`. Establish `hre : ((h.submatrix id f) * (h.submatrix e f)⁻¹) (e s') s = ((h.submatrix e f) * (h.submatrix e f)⁻¹) s' s` using `rfl`. Rewrite using `[hre, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hD)]`. Simplify using `[Matrix.one_apply, he.eq_iff]`.

Establish `hrR : r ∈ R` using `Finset.mem_sdiff.mpr ⟨hrA, hrI⟩`. Rewrite using `[Matrix.one_apply_ne (hR r hrR s), zero_add, movM_apply R he ε u hrR s]`. Establish `hupdrow : (h.submatrix e f).updateRow s (fun t => h r (f t)) = h.submatrix (Function.update e s r) f`. Use extensionality with `x t`. Distinguish the cases in `hx : x = s`.

Substitute `hx` using the available equality. Simplify using `[Matrix.updateRow_apply]`. Simplify using `[Matrix.updateRow_apply, Function.update_apply, hx]`. Establish `hprod : ((h.submatrix id f) * (h.submatrix e f)⁻¹) r s = Ring.inverse (h.submatrix e f).det * (h.submatrix (Function.update e s r) f).det`. Rewrite using `[Matrix.mul_apply, Matrix.inv_def, ← hupdrow, ← sum_mul_adjugate, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Simplify using `only [Matrix.smul_apply, smul_eq_mul, Matrix.submatrix_apply, id]`. Expand and normalize the polynomial expressions, which then agree. Establish `hcard : (rowsOf e r s).card = S.card`. Rewrite using `[rowsOf, Finset.card_image_of_injective _ (hupd r hrR s), Finset.card_univ, Fintype.card_fin]`.

Establish `hsub : rowsOf e r s ⊆ A`. Introduce `x hx`. Simplify using `only [rowsOf, Finset.mem_image, Finset.mem_univ, true_and] at hx`. Take `⟨y, rfl⟩` from `hx`. Rewrite using `[Function.update_apply]`.

Use `split_ifs`. Conclude with `hrA`. Conclude with `heA y`. Rewrite using `[hprod, hε r s hrR h, Ring.inverse_eq_inv, hu_def]`. Simplify using `only`.

Rewrite using `[hw _ hcard hsub, hw0']`. Clear the denominators using the available nonvanishing facts. Rewrite using `[Matrix.one_apply_ne (fun hre => hrA (by rw [hre]; exact heA s)), movM_of_not_mem R e ε u r _ (fun h' => hrA (Finset.mem_sdiff.mp h').1), add_zero, Matrix.mul_apply]`. Use `symm`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises.

Introduce `t _`. Simplify using `only [Matrix.submatrix_apply, id]`. Rewrite using `[hbd r (f t) (fun hh => hout (f t) (hfA t) r hrA hh.symm), zero_mul]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x y hxy`.

Rewrite using `[hGe, Matrix.add_apply]`. Establish `h1 : (1 : Matrix (Fin N) (Fin N) ℂ) x (π.symm y) = 0`. Apply `Matrix.one_apply_ne` to reduce the goal to its premises. Introduce `hx`. Establish `hy : π x = y` using `by rw [hx, Equiv.apply_symm_apply]`.

Apply `hxy` to reduce the goal to its premises. Distinguish the cases in `hxA : x ∈ A`. Rewrite using `[← hy]`. Conclude with `hin x hxA (π x) (hπA x hxA)`. Rewrite `hy` using `[hπout x hxA]`.

Rewrite using `[hy]`. Establish `h2 : movM R e ε u x (π.symm y) = 0`. Distinguish the cases in `hxR : x ∈ R`. Apply `movM_of_not_range` to reduce the goal to its premises. Introduce `s hs`.

Apply `hxy` to reduce the goal to its premises. Establish `hyf : y = f s` using `by rw [← hπ s, ← hs, Equiv.apply_symm_apply]`. Rewrite using `[hyf]`. Conclude with `hin x (Finset.mem_sdiff.mp hxR).1 (f s) (hfA s)`. Conclude with `movM_of_not_mem R e ε u x _ hxR`.

Rewrite using `[h1, h2, add_zero]`. Rewrite using `[← Matrix.det_transpose, Matrix.transpose_submatrix, Matrix.det_permute, Matrix.det_transpose]`. Use `mul_ne_zero ?_ (det_one_add_movM_ne R e ε u hR)` and prove the remaining obligations. Apply the tactic sequence `rcases Int.units_eq_one_or (Equiv.Perm.sign π.symm) with hs | hs <;> rw [hs] <;> norm_num`. Introduce `I`.

Distinguish the cases in `hIc : I.card = S.card`. Simplify using `only [minorIJ, dif_pos hIc]`. Rewrite using `[← hf_def]`. Establish `hsub : ((1 + movM R e ε u).submatrix id π.symm).submatrix (I.orderEmbOfFin hIc) f = (h.submatrix (I.orderEmbOfFin hIc) f) * (h.submatrix e f)⁻¹`. Use extensionality with `x s`.

Establish `h1 : π.symm (f s) = e s` using `by rw [← hπ s, Equiv.symm_apply_apply]`. Rewrite using `[Matrix.submatrix_apply, hGe, h1, hX]`. Simplify using `only [Matrix.mul_apply, Matrix.submatrix_apply, id]`. Rewrite using `[hsub, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv, hw0']`. Clear the denominators using the available nonvanishing facts.

Simplify using `only [minorIJ, dif_neg hIc]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem core (j : ℕ) (A S I₀ : Finset (Fin N)) (hS : S ⊆ A) (hI : I₀ ⊆ A) (hc : I₀.card = S.card)
    (hin : ∀ a ∈ A, ∀ b ∈ A, ((a : ℕ) < N - j ↔ (b : ℕ) < N - j))
    (hout : ∀ a ∈ A, ∀ b, b ∉ A → ¬ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)) :
    ∃ (C : Matrix (Fin N) (Fin N) ℂ) (B : Finset (Fin N) → Matrix (Fin N) (Fin N) ℂ),
      ∀ (h : Matrix (Fin N) (Fin N) ℂ) (a : ℂ) (w : Finset (Fin N) → ℂ), IsBlockDiag j h → a ≠ 0 →
        (∀ I, I.card = S.card → I ⊆ A → w I = a * minorIJ h I S) → w I₀ ≠ 0 →
        IsBlockDiag j (grMat C B I₀ w) ∧ (grMat C B I₀ w).det ≠ 0 ∧
          ∀ I, minorIJ (grMat C B I₀ w) I S * w I₀ = a * minorIJ h I S := by
  set e : Fin S.card → Fin N := ⇑(I₀.orderEmbOfFin hc) with he_def
  set f : Fin S.card → Fin N := ⇑(S.orderEmbOfFin rfl) with hf_def
  have he : Function.Injective e := (I₀.orderEmbOfFin hc).injective
  have hf : Function.Injective f := (S.orderEmbOfFin rfl).injective
  have heI : ∀ s, e s ∈ I₀ := fun s => Finset.orderEmbOfFin_mem I₀ hc s
  have hfS : ∀ s, f s ∈ S := fun s => Finset.orderEmbOfFin_mem S rfl s
  have heA : ∀ s, e s ∈ A := fun s => hI (heI s)
  have hfA : ∀ s, f s ∈ A := fun s => hS (hfS s)
  obtain ⟨π, hπ, hπout, hπA⟩ := exists_perm_ext A e f he hf heA hfA
  set R : Finset (Fin N) := A \ I₀ with hR_def
  have hR : ∀ r ∈ R, ∀ s, r ≠ e s := by
    intro r hr s hrs
    exact (Finset.mem_sdiff.mp hr).2 (by rw [hrs]; exact heI s)
  have hupd : ∀ r ∈ R, ∀ s, Function.Injective (Function.update e s r) := by
    intro r hr s x y hxy
    have hrI : r ∉ I₀ := (Finset.mem_sdiff.mp hr).2
    simp only [Function.update_apply] at hxy
    split_ifs at hxy with hx hy hy
    · rw [hx, hy]
    · exact absurd (show r ∈ I₀ by rw [hxy]; exact heI y) hrI
    · exact absurd (show r ∈ I₀ by rw [← hxy]; exact heI x) hrI
    · exact he hxy
  have hex : ∀ (r : Fin N) (s : Fin S.card), ∃ c : ℂ, r ∈ R → ∀ h : Matrix (Fin N) (Fin N) ℂ,
      (h.submatrix (Function.update e s r) (S.orderEmbOfFin rfl)).det = c * minorIJ h (rowsOf e r s) S := by
    intro r s
    by_cases hr : r ∈ R
    · obtain ⟨c, hc'⟩ := exists_sign S (Function.update e s r) (hupd r hr s)
      exact ⟨c, fun _ => hc'⟩
    · exact ⟨0, fun h => absurd h hr⟩
  choose ε hε using hex
  refine ⟨(1 : Matrix (Fin N) (Fin N) ℂ).submatrix id π.symm, fun I => (coefM R e ε I).submatrix id π.symm, ?_⟩
  intro h a w hbd ha hw hw0
  have hG := core_lemma R e ε π I₀ w
  set u : Finset (Fin N) → ℂ := fun I => w I / w I₀ with hu_def
  rw [hG]
  have hGe : ∀ r c, ((1 + movM R e ε u).submatrix id π.symm) r c = (1 + movM R e ε u) r (π.symm c) :=
    fun r c => rfl
  have hw0' : w I₀ = a * (h.submatrix e f).det := by
    rw [hw I₀ hc hI, minorIJ, dif_pos hc]
  have hD : (h.submatrix e f).det ≠ 0 := by
    intro h0
    apply hw0
    rw [hw0', h0, mul_zero]
  have hX : ∀ r s, (1 + movM R e ε u) r (e s) = ((h.submatrix id f) * (h.submatrix e f)⁻¹) r s := by
    intro r s
    rw [Matrix.add_apply]
    by_cases hrA : r ∈ A
    · by_cases hrI : r ∈ I₀
      · obtain ⟨s', rfl⟩ : ∃ s', e s' = r := by
          have hmem : r ∈ Set.range e := by
            rw [he_def, Finset.range_orderEmbOfFin]
            exact hrI
          exact hmem
        rw [movM_of_not_mem R e ε u _ _ (fun h' => (Finset.mem_sdiff.mp h').2 hrI), add_zero]
        have hre : ((h.submatrix id f) * (h.submatrix e f)⁻¹) (e s') s =
            ((h.submatrix e f) * (h.submatrix e f)⁻¹) s' s := rfl
        rw [hre, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hD)]
        simp [Matrix.one_apply, he.eq_iff]
      · have hrR : r ∈ R := Finset.mem_sdiff.mpr ⟨hrA, hrI⟩
        rw [Matrix.one_apply_ne (hR r hrR s), zero_add, movM_apply R he ε u hrR s]
        have hupdrow : (h.submatrix e f).updateRow s (fun t => h r (f t)) =
            h.submatrix (Function.update e s r) f := by
          ext x t
          by_cases hx : x = s
          · subst hx
            simp [Matrix.updateRow_apply]
          · simp [Matrix.updateRow_apply, Function.update_apply, hx]
        have hprod : ((h.submatrix id f) * (h.submatrix e f)⁻¹) r s =
            Ring.inverse (h.submatrix e f).det * (h.submatrix (Function.update e s r) f).det := by
          rw [Matrix.mul_apply, Matrix.inv_def, ← hupdrow, ← sum_mul_adjugate, Finset.mul_sum]
          refine Finset.sum_congr rfl fun t _ => ?_
          simp only [Matrix.smul_apply, smul_eq_mul, Matrix.submatrix_apply, id]
          ring
        have hcard : (rowsOf e r s).card = S.card := by
          rw [rowsOf, Finset.card_image_of_injective _ (hupd r hrR s), Finset.card_univ, Fintype.card_fin]
        have hsub : rowsOf e r s ⊆ A := by
          intro x hx
          simp only [rowsOf, Finset.mem_image, Finset.mem_univ, true_and] at hx
          obtain ⟨y, rfl⟩ := hx
          rw [Function.update_apply]
          split_ifs
          · exact hrA
          · exact heA y
        rw [hprod, hε r s hrR h, Ring.inverse_eq_inv, hu_def]
        dsimp only
        rw [hw _ hcard hsub, hw0']
        field_simp
    · rw [Matrix.one_apply_ne (fun hre => hrA (by rw [hre]; exact heA s)),
        movM_of_not_mem R e ε u r _ (fun h' => hrA (Finset.mem_sdiff.mp h').1), add_zero,
        Matrix.mul_apply]
      symm
      apply Finset.sum_eq_zero
      intro t _
      simp only [Matrix.submatrix_apply, id]
      rw [hbd r (f t) (fun hh => hout (f t) (hfA t) r hrA hh.symm), zero_mul]
  refine ⟨?_, ?_, ?_⟩
  · intro x y hxy
    rw [hGe, Matrix.add_apply]
    have h1 : (1 : Matrix (Fin N) (Fin N) ℂ) x (π.symm y) = 0 := by
      apply Matrix.one_apply_ne
      intro hx
      have hy : π x = y := by rw [hx, Equiv.apply_symm_apply]
      apply hxy
      by_cases hxA : x ∈ A
      · rw [← hy]
        exact hin x hxA (π x) (hπA x hxA)
      · rw [hπout x hxA] at hy
        rw [hy]
    have h2 : movM R e ε u x (π.symm y) = 0 := by
      by_cases hxR : x ∈ R
      · apply movM_of_not_range
        intro s hs
        apply hxy
        have hyf : y = f s := by rw [← hπ s, ← hs, Equiv.apply_symm_apply]
        rw [hyf]
        exact hin x (Finset.mem_sdiff.mp hxR).1 (f s) (hfA s)
      · exact movM_of_not_mem R e ε u x _ hxR
    rw [h1, h2, add_zero]
  · rw [← Matrix.det_transpose, Matrix.transpose_submatrix, Matrix.det_permute, Matrix.det_transpose]
    refine mul_ne_zero ?_ (det_one_add_movM_ne R e ε u hR)
    rcases Int.units_eq_one_or (Equiv.Perm.sign π.symm) with hs | hs <;> rw [hs] <;> norm_num
  · intro I
    by_cases hIc : I.card = S.card
    · simp only [minorIJ, dif_pos hIc]
      rw [← hf_def]
      have hsub : ((1 + movM R e ε u).submatrix id π.symm).submatrix (I.orderEmbOfFin hIc) f =
          (h.submatrix (I.orderEmbOfFin hIc) f) * (h.submatrix e f)⁻¹ := by
        ext x s
        have h1 : π.symm (f s) = e s := by rw [← hπ s, Equiv.symm_apply_apply]
        rw [Matrix.submatrix_apply, hGe, h1, hX]
        simp only [Matrix.mul_apply, Matrix.submatrix_apply, id]
      rw [hsub, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv, hw0']
      field_simp
    · simp only [minorIJ, dif_neg hIc]
      ring

/- English proof (translation)
Introduce `N j i I₀ _ hI₀`. Establish `hI : I₀.card = (stepCols N j i).card ∧ I₀ ⊆ (if (i : ℕ) + 1 ≤ j then wIdx N j else omIdx N j)` using `hI₀`. Establish `hlt` using `i.isLt`. Distinguish the cases in `hij : (i : ℕ) + 1 ≤ j`. Rewrite `hI` using `[if_pos hij]`.

Establish `hS : stepCols N j i ⊆ wIdx N j`. Introduce `a ha`. Simplify using `only [stepCols, wIdx, if_pos hij, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢`. Conclude with `ha.1`. Establish `hin : ∀ a ∈ wIdx N j, ∀ b ∈ wIdx N j, ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)`.

Introduce `a ha b hb`. Simplify using `only [wIdx, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb`. Use linear arithmetic over natural numbers and integers. Establish `hout : ∀ a ∈ wIdx N j, ∀ b, b ∉ wIdx N j → ¬ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)`. Introduce `a ha b hb`.

Simplify using `only [wIdx, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb`. Use linear arithmetic over natural numbers and integers. Take `⟨C, B, hCB⟩` from `core j (wIdx N j) (stepCols N j i) I₀ hS hI.2 hI.1 hin hout`. Use `⟨C, B, ?_⟩` and prove the remaining obligations. Introduce `h a w hbd _ ha hw hw0`.

Use `hCB h a w hbd ha (fun I hc hsub => hw I ?_) hw0` and prove the remaining obligations. Use `show I.card = (stepCols N j i).card ∧ I ⊆ (if (i : ℕ) + 1 ≤ j then wIdx N j else omIdx N j)`. Rewrite using `[if_pos hij]`. Conclude with `⟨hc, hsub⟩`. Rewrite `hI` using `[if_neg hij]`.

Establish `hS : stepCols N j i ⊆ omIdx N j`. Introduce `a ha`. Simplify using `only [stepCols, omIdx, if_neg hij, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢`. Use linear arithmetic over natural numbers and integers. Establish `hin : ∀ a ∈ omIdx N j, ∀ b ∈ omIdx N j, ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)`.

Introduce `a ha b hb`. Simplify using `only [omIdx, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb`. Use linear arithmetic over natural numbers and integers. Establish `hout : ∀ a ∈ omIdx N j, ∀ b, b ∉ omIdx N j → ¬ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)`. Introduce `a ha b hb`.

Simplify using `only [omIdx, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb`. Use linear arithmetic over natural numbers and integers. Take `⟨C, B, hCB⟩` from `core j (omIdx N j) (stepCols N j i) I₀ hS hI.2 hI.1 hin hout`. Use `⟨C, B, ?_⟩` and prove the remaining obligations. Introduce `h a w hbd _ ha hw hw0`.

Use `hCB h a w hbd ha (fun I hc hsub => hw I ?_) hw0` and prove the remaining obligations. Use `show I.card = (stepCols N j i).card ∧ I ⊆ (if (i : ℕ) + 1 ≤ j then wIdx N j else omIdx N j)`. Rewrite using `[if_neg hij]`. Conclude with `⟨hc, hsub⟩`.
-/
theorem exists_isGrChart : ∀ (N j : ℕ) (i : Fin N) (I₀ : Finset (Fin N)), j ≤ N → IsStepRows N j i I₀ →
    ∃ C B, IsGrChart N j i I₀ C B := by
  intro N j i I₀ _ hI₀
  have hI : I₀.card = (stepCols N j i).card ∧
      I₀ ⊆ (if (i : ℕ) + 1 ≤ j then wIdx N j else omIdx N j) := hI₀
  have hlt := i.isLt
  by_cases hij : (i : ℕ) + 1 ≤ j
  · rw [if_pos hij] at hI
    have hS : stepCols N j i ⊆ wIdx N j := by
      intro a ha
      simp only [stepCols, wIdx, if_pos hij, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      exact ha.1
    have hin : ∀ a ∈ wIdx N j, ∀ b ∈ wIdx N j, ((a : ℕ) < N - j ↔ (b : ℕ) < N - j) := by
      intro a ha b hb
      simp only [wIdx, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      omega
    have hout : ∀ a ∈ wIdx N j, ∀ b, b ∉ wIdx N j → ¬ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j) := by
      intro a ha b hb
      simp only [wIdx, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      omega
    obtain ⟨C, B, hCB⟩ := core j (wIdx N j) (stepCols N j i) I₀ hS hI.2 hI.1 hin hout
    refine ⟨C, B, ?_⟩
    intro h a w hbd _ ha hw hw0
    refine hCB h a w hbd ha (fun I hc hsub => hw I ?_) hw0
    show I.card = (stepCols N j i).card ∧ I ⊆ (if (i : ℕ) + 1 ≤ j then wIdx N j else omIdx N j)
    rw [if_pos hij]
    exact ⟨hc, hsub⟩
  · rw [if_neg hij] at hI
    have hS : stepCols N j i ⊆ omIdx N j := by
      intro a ha
      simp only [stepCols, omIdx, if_neg hij, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      omega
    have hin : ∀ a ∈ omIdx N j, ∀ b ∈ omIdx N j, ((a : ℕ) < N - j ↔ (b : ℕ) < N - j) := by
      intro a ha b hb
      simp only [omIdx, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      omega
    have hout : ∀ a ∈ omIdx N j, ∀ b, b ∉ omIdx N j → ¬ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j) := by
      intro a ha b hb
      simp only [omIdx, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      omega
    obtain ⟨C, B, hCB⟩ := core j (omIdx N j) (stepCols N j i) I₀ hS hI.2 hI.1 hin hout
    refine ⟨C, B, ?_⟩
    intro h a w hbd _ ha hw hw0
    refine hCB h a w hbd ha (fun I hc hsub => hw I ?_) hw0
    show I.card = (stepCols N j i).card ∧ I ⊆ (if (i : ℕ) + 1 ≤ j then wIdx N j else omIdx N j)
    rw [if_neg hij]
    exact ⟨hc, hsub⟩

end GlobalTheory.CompanionTheory.Ar.PB.StepW.GrChart
