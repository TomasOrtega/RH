import ReciprocityTheory.AnalyticForms.RegularLocalRings.WChartsA

namespace ReciprocityTheory.AnForm.R

open MvPolynomial AlgebraicGeometry CategoryTheory

noncomputable section

def fracR {R : Type} [CommRing R] {m : ℕ} (g : Fin m → R) (i k : Fin m) : FinalTheorems.reesChart g i :=
  ⟨IsLocalization.mk' (Localization.Away (g i)) (g k)
    (⟨g i, Submonoid.mem_powers _⟩ : Submonoid.powers (g i)), Algebra.subset_adjoin ⟨k, rfl⟩⟩

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `IsLocalization.mk'_self' (Localization.Away (g i))`.
-/
theorem fracR_self {R : Type} [CommRing R] {m : ℕ} (g : Fin m → R) (i : Fin m) : fracR g i i = 1 := by
  apply Subtype.ext
  exact IsLocalization.mk'_self' (Localization.Away (g i))

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `(IsLocalization.mk'_spec (Localization.Away (g i)) (g k) (⟨g i, Submonoid.mem_powers _⟩ : Submonoid.powers (g i))).symm`.
-/
theorem algebraMap_reesChart_eq {R : Type} [CommRing R] {m : ℕ} (g : Fin m → R) (i k : Fin m) :
    algebraMap R (FinalTheorems.reesChart g i) (g k) = fracR g i k * algebraMap R (FinalTheorems.reesChart g i) (g i) := by
  apply Subtype.ext
  exact (IsLocalization.mk'_spec (Localization.Away (g i)) (g k)
    (⟨g i, Submonoid.mem_powers _⟩ : Submonoid.powers (g i))).symm

/- English proof (translation)
Establish `hu : IsUnit (algebraMap R (Localization.Away (g i)) (g i))` using `IsLocalization.Away.algebraMap_isUnit (g i)`. Establish `key : ∀ x : FinalTheorems.reesChart g i, x * algebraMap R _ (g i) = 0 → x = 0`. Introduce `x hx`. Establish `h1 : (x : Localization.Away (g i)) * algebraMap R _ (g i) = 0` using `congrArg Subtype.val hx`. Conclude with `Subtype.ext (hu.mul_left_eq_zero.mp h1)`.

Conclude with `mem_nonZeroDivisors_iff.mpr ⟨fun x hx => key x (by rwa [mul_comm] at hx), key⟩`.
-/
theorem algebraMap_reesChart_mem_nonZeroDivisors {R : Type} [CommRing R] {m : ℕ} (g : Fin m → R)
    (i : Fin m) : algebraMap R (FinalTheorems.reesChart g i) (g i) ∈ nonZeroDivisors (FinalTheorems.reesChart g i) := by
  have hu : IsUnit (algebraMap R (Localization.Away (g i)) (g i)) :=
    IsLocalization.Away.algebraMap_isUnit (g i)
  have key : ∀ x : FinalTheorems.reesChart g i, x * algebraMap R _ (g i) = 0 → x = 0 := by
    intro x hx
    have h1 : (x : Localization.Away (g i)) * algebraMap R _ (g i) = 0 := congrArg Subtype.val hx
    exact Subtype.ext (hu.mul_left_eq_zero.mp h1)
  exact mem_nonZeroDivisors_iff.mpr ⟨fun x hx => key x (by rwa [mul_comm] at hx), key⟩

/- English proof (translation)
Establish `h` using `IsAffineOpen.SpecMap_appLE_fromSpec s (isAffineOpen_top (Spec (.of ℂ))) U.2 le_top`. Rewrite `h` using `[IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]`. Rewrite using `[← h, ← Spec.map_comp]`. Both sides reduce to the same expression.
-/
theorem specMap_constSec {S : Scheme.{0}} (s : S ⟶ Spec (.of ℂ)) (U : S.affineOpens) :
    Spec.map (CommRingCat.ofHom (constSec s U.1)) = U.2.fromSpec ≫ s := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec s (isAffineOpen_top (Spec (.of ℂ))) U.2 le_top
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
  rw [← h, ← Spec.map_comp]
  rfl

/- English proof (translation)
Set `_ : Algebra ℂ (FinalTheorems.reesChart g i)` to `((algebraMap R (FinalTheorems.reesChart g i)).comp c).toAlgebra`. Establish `hR : ∀ r : R, algebraMap R (FinalTheorems.reesChart g i) r ∈ Algebra.adjoin ℂ (Set.range y)`. Introduce `r`. Take `⟨f, rfl⟩` from `hz r`. Proceed by induction on `f using MvPolynomial.induction_on with`.

Consider the case `C a`. Rewrite using `[eval₂_C]`. Conclude with `Subalgebra.algebraMap_mem _ a`. Consider the case `add f h hf hh => rw [eval₂_add, map_add]`. Conclude with `add_mem hf hh`.

Consider the case `mul_X f q hf`. Rewrite using `[eval₂_mul, eval₂_X, map_mul]`. Take `⟨l, hl⟩` from `hyz q`. Use `mul_mem hf ?_` and prove the remaining obligations. Rewrite using `[← hl]`.

Conclude with `Algebra.subset_adjoin ⟨l, rfl⟩`. Rewrite using `[eq_top_iff]`. Introduce and unpack `⟨x, hx⟩ -`. Proceed by induction on `hx using Algebra.adjoin_induction with`. Consider the case `mem x hx`.

Take `⟨k, rfl⟩` from `hx`. Take `⟨l, hl⟩` from `hyt k`. Establish `h2 : y l ∈ Algebra.adjoin ℂ (Set.range y)` using `Algebra.subset_adjoin ⟨l, rfl⟩`. Rewrite `h2` using `[hl]`. Conclude with `h2`.

Consider the case `algebraMap r => exact hR r`. Consider the case `add x y hx hy ihx ihy => exact add_mem ihx ihy`. Consider the case `mul x y hx hy ihx ihy => exact mul_mem ihx ihy`.
-/
theorem adjoin_reesChart_eq_top {R : Type} [CommRing R] (c : ℂ →+* R) {σ : Type} (z : σ → R)
    (hz : ∀ r : R, ∃ f : MvPolynomial σ ℂ, r = eval₂ c z f) {m : ℕ} (g : Fin m → R) (i : Fin m)
    {n : ℕ} (y : Fin n → FinalTheorems.reesChart g i)
    (hyz : ∀ q, ∃ l, y l = algebraMap R _ (z q)) (hyt : ∀ k, ∃ l, y l = fracR g i k) :
    @Algebra.adjoin ℂ (FinalTheorems.reesChart g i) _ _ ((algebraMap R (FinalTheorems.reesChart g i)).comp c).toAlgebra
      (Set.range y) = ⊤ := by
  let _ : Algebra ℂ (FinalTheorems.reesChart g i) := ((algebraMap R (FinalTheorems.reesChart g i)).comp c).toAlgebra
  have hR : ∀ r : R, algebraMap R (FinalTheorems.reesChart g i) r ∈ Algebra.adjoin ℂ (Set.range y) := by
    intro r
    obtain ⟨f, rfl⟩ := hz r
    induction f using MvPolynomial.induction_on with
    | C a =>
      rw [eval₂_C]
      exact Subalgebra.algebraMap_mem _ a
    | add f h hf hh => rw [eval₂_add, map_add]; exact add_mem hf hh
    | mul_X f q hf =>
      rw [eval₂_mul, eval₂_X, map_mul]
      obtain ⟨l, hl⟩ := hyz q
      refine mul_mem hf ?_
      rw [← hl]
      exact Algebra.subset_adjoin ⟨l, rfl⟩
  rw [eq_top_iff]
  rintro ⟨x, hx⟩ -
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    obtain ⟨l, hl⟩ := hyt k
    have h2 : y l ∈ Algebra.adjoin ℂ (Set.range y) := Algebra.subset_adjoin ⟨l, rfl⟩
    rw [hl] at h2
    exact h2
  | algebraMap r => exact hR r
  | add x y hx hy ihx ihy => exact add_mem ihx ihy
  | mul x y hx hy ihx ihy => exact mul_mem ihx ihy

variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Take `⟨f, hf⟩` from `Ideal.Quotient.mk_surjective (gammaChart hP p r)`. Use `⟨f, ?_⟩` and prove the remaining obligations. Rewrite using `[← gammaChart_symm_mk, hf, RingEquiv.symm_apply_apply]`.
-/
theorem exists_eval₂_chartCoord {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P)
    (p : (k : K) → ι k) (r : Γ(projX P hP, (chartOpen hP p).1)) :
    ∃ f : MvPolynomial (Σ k, ι k) ℂ, r = eval₂ (constSec (toSpecC hP) (chartOpen hP p).1) (chartCoord hP p) f := by
  obtain ⟨f, hf⟩ := Ideal.Quotient.mk_surjective (gammaChart hP p r)
  refine ⟨f, ?_⟩
  rw [← gammaChart_symm_mk, hf, RingEquiv.symm_apply_apply]

def yC {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P) (p : (k : K) → ι k) {m : ℕ}
    (g : Fin m → Γ(projX P hP, (chartOpen hP p).1)) (i : Fin m) :
    Fin (Fintype.card (Σ k, ι k) + m) → FinalTheorems.reesChart g i :=
  fun l => Sum.elim (fun a => algebraMap _ (FinalTheorems.reesChart g i)
    (chartCoord hP p ((Fintype.equivFin _).symm a))) (fracR g i) (finSumFinEquiv.symm l)

/- English proof (translation)
Simplify using `[yC]`.
-/
theorem yC_yq {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P) (p : (k : K) → ι k)
    {m : ℕ} (g : Fin m → Γ(projX P hP, (chartOpen hP p).1)) (i : Fin m) (q : Σ k, ι k) :
    yC hP p g i (finSumFinEquiv (Sum.inl (Fintype.equivFin _ q))) =
      algebraMap _ (FinalTheorems.reesChart g i) (chartCoord hP p q) := by
  simp [yC]

/- English proof (translation)
Simplify using `[yC]`.
-/
theorem yC_yt {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P) (p : (k : K) → ι k)
    {m : ℕ} (g : Fin m → Γ(projX P hP, (chartOpen hP p).1)) (i : Fin m) (k : Fin m) :
    yC hP p g i (finSumFinEquiv (Sum.inr k)) = fracR g i k := by
  simp [yC]

/- English proof (translation)
The claim follows from `adjoin_reesChart_eq_top _ (chartCoord hP p) (exists_eval₂_chartCoord hP p) g i (yC hP p g i) (fun q => ⟨_, yC_yq hP p g i q⟩) (fun k => ⟨_, yC_yt hP p g i k⟩)`.
-/
theorem adjoin_yC {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P)
    (p : (k : K) → ι k) {m : ℕ} (g : Fin m → Γ(projX P hP, (chartOpen hP p).1)) (i : Fin m) :
    @Algebra.adjoin ℂ (FinalTheorems.reesChart g i) _ _
      ((algebraMap _ (FinalTheorems.reesChart g i)).comp (constSec (toSpecC hP) (chartOpen hP p).1)).toAlgebra
      (Set.range (yC hP p g i)) = ⊤ :=
  adjoin_reesChart_eq_top _ (chartCoord hP p) (exists_eval₂_chartCoord hP p) g i (yC hP p g i)
    (fun q => ⟨_, yC_yq hP p g i q⟩) (fun k => ⟨_, yC_yt hP p g i k⟩)

end

end ReciprocityTheory.AnForm.R
