import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.SymExp
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsAntisym
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

omit [∀ k, Fintype (ι k)] in

/- English proof (translation)
Consider the cases of `A`. Consider the cases of `B`. Consider the cases of `ha`. Consider the cases of `hh`. Both sides reduce to the same expression.
-/
theorem hermLine_eq_of {A B : HermLine ι} (ha : A.a = B.a) (hh : A.h = B.h) : A = B := by
  cases A
  cases B
  cases ha
  cases hh
  rfl

/- English proof (translation)
The claim follows from `hA.mul hB`.
-/
theorem isSmoothHerm_tensor {A B : HermLine ι} (hA : IsSmoothHerm A) (hB : IsSmoothHerm B) :
    IsSmoothHerm (A.tensor B) :=
  hA.mul hB

/- English proof (translation)
Take `⟨n, rfl | rfl⟩` from `Int.eq_nat_or_neg m`. Establish `h : (hermZpow A (n : ℤ)).h = fun z => A.h z ^ n` using `funext fun z => zpow_natCast (A.h z) n`. Unfold `IsSmoothHerm`. Rewrite using `[h]`. Conclude with `hA.pow n`.

Establish `h : (hermZpow A (-(n : ℤ))).h = fun z => (A.h z ^ n)⁻¹`. Use function extensionality and compare the values at `fun z => by rw [← zpow_natCast, ← zpow_neg]; rfl`. Unfold `IsSmoothHerm`. Rewrite using `[h]`. Conclude with `(hA.pow n).inv fun z hz => (pow_pos (A.pos z hz) n).ne'`.
-/
theorem isSmoothHerm_hermZpow {A : HermLine ι} (hA : IsSmoothHerm A) (m : ℤ) :
    IsSmoothHerm (hermZpow A m) := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · have h : (hermZpow A (n : ℤ)).h = fun z => A.h z ^ n := funext fun z => zpow_natCast (A.h z) n
    unfold IsSmoothHerm
    rw [h]
    exact hA.pow n
  · have h : (hermZpow A (-(n : ℤ))).h = fun z => (A.h z ^ n)⁻¹ :=
      funext fun z => by rw [← zpow_natCast, ← zpow_neg]; rfl
    unfold IsSmoothHerm
    rw [h]
    exact (hA.pow n).inv fun z hz => (pow_pos (A.pos z hz) n).ne'

def famExt (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (P : Ideal (MRing ι)) (n : ℕ)
    (e : Fin 2 → HermLine ι) : MultilinearMap ℝ (fun _ : Fin n => Fin 2 → ℝ) ℝ :=
  ∑ s : Fin n → Fin 2,
    I P n (e ∘ s) • (MultilinearMap.mkPiAlgebra ℝ (Fin n) ℝ).compLinearMap fun j => LinearMap.proj (s j)

section Family

variable {I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ} {P : Ideal (MRing ι)} {n : ℕ}

omit [∀ k, Fintype (ι k)] in

/- English proof (translation)
Simplify using `[famExt, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]`.
-/
theorem famExt_apply (e : Fin 2 → HermLine ι) (v : Fin n → Fin 2 → ℝ) :
    famExt I P n e v = ∑ s : Fin n → Fin 2, I P n (e ∘ s) * ∏ j, v j (s j) := by
  simp [famExt, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]

omit [∀ k, Fintype (ι k)] in

/- English proof (translation)
Rewrite using `[famExt_apply, Finset.sum_eq_single t]`. Simplify using the standard rewrite rules. Introduce `s _ hs`. Choose the witnesses or unpack the hypotheses as in `⟨j, hj⟩ : ∃ j, s j ≠ t j := by`. Assume the negation of the conclusion as `h`.

Use `push Not at h`. Conclude with `hs (funext h)`. Rewrite using `[Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj]), mul_zero]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ t) h`.
-/
theorem famExt_basis (e : Fin 2 → HermLine ι) (t : Fin n → Fin 2) :
    famExt I P n e (fun j => Pi.single (t j) 1) = I P n (e ∘ t) := by
  rw [famExt_apply, Finset.sum_eq_single t]
  · simp
  · intro s _ hs
    obtain ⟨j, hj⟩ : ∃ j, s j ≠ t j := by
      by_contra h
      push Not at h
      exact hs (funext h)
    rw [Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj]), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ t) h

/- English proof (translation)
Introduce `σ v`. Rewrite using `[famExt_apply, famExt_apply]`. Use `Fintype.sum_equiv (Equiv.arrowCongr σ (Equiv.refl (Fin 2))) _ _ fun s => ?_` and prove the remaining obligations. Establish `h1 : e ∘ (Equiv.arrowCongr σ (Equiv.refl (Fin 2)) s) = (e ∘ s) ∘ σ.symm` using `rfl`. Establish `h2 : ∏ j, v j ((Equiv.arrowCongr σ (Equiv.refl (Fin 2)) s) j) = ∏ j, (v ∘ σ) j (s j)`.

Use `(Equiv.prod_comp σ fun j => v j (s (σ.symm j))).symm.trans ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Rewrite using `[h1, h2, hI.1 P n (e ∘ s) σ.symm hP fun j => he _]`.
-/
theorem famExt_symm (hI : IsIntersectionFamily I) (hP : IsArithVar P n) (e : Fin 2 → HermLine ι)
    (he : ∀ i, IsSmoothHerm (e i)) : IsSymmForm (famExt I P n e) := by
  intro σ v
  rw [famExt_apply, famExt_apply]
  refine Fintype.sum_equiv (Equiv.arrowCongr σ (Equiv.refl (Fin 2))) _ _ fun s => ?_
  have h1 : e ∘ (Equiv.arrowCongr σ (Equiv.refl (Fin 2)) s) = (e ∘ s) ∘ σ.symm := rfl
  have h2 : ∏ j, v j ((Equiv.arrowCongr σ (Equiv.refl (Fin 2)) s) j) = ∏ j, (v ∘ σ) j (s j) := by
    refine (Equiv.prod_comp σ fun j => v j (s (σ.symm j))).symm.trans ?_
    simp
  rw [h1, h2, hI.1 P n (e ∘ s) σ.symm hP fun j => he _]

/- English proof (translation)
Establish `e : (hermZpow X 0).tensor (hermZpow X 0) = hermZpow X 0` using `hermLine_eq_of (by simp [HermLine.tensor, hermZpow]) (by funext z; simp [HermLine.tensor, hermZpow])`. Establish `h` using `hI.2.1 P n L _ _ hP hL (isSmoothHerm_hermZpow hX 0) (isSmoothHerm_hermZpow hX 0)`. Rewrite `h` using `[e]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem fam_snoc_zpow_zero (hI : IsIntersectionFamily I) (hP : IsArithVar P (n + 1))
    (L : Fin n → HermLine ι) (hL : ∀ j, IsSmoothHerm (L j)) {X : HermLine ι} (hX : IsSmoothHerm X) :
    I P (n + 1) (Fin.snoc L (hermZpow X 0)) = 0 := by
  have e : (hermZpow X 0).tensor (hermZpow X 0) = hermZpow X 0 :=
    hermLine_eq_of (by simp [HermLine.tensor, hermZpow]) (by funext z; simp [HermLine.tensor, hermZpow])
  have h := hI.2.1 P n L _ _ hP hL (isSmoothHerm_hermZpow hX 0) (isSmoothHerm_hermZpow hX 0)
  rw [e] at h
  linarith

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Simplify using `only [Nat.cast_zero, zero_mul]`. Conclude with `fam_snoc_zpow_zero hI hP L hL hX`. Consider the case `succ k ih`.

Establish `e : hermZpow X ((k + 1 : ℕ) : ℤ) = (hermZpow X k).tensor X` using `hermLine_eq_of (by simp [HermLine.tensor, hermZpow, add_smul]) (funext fun z => by show X.h z ^ ((k + 1 : ℕ) : ℤ) = X.h z ^ (k : ℤ) * X.h z`. Rewrite using `[zpow_natCast, zpow_natCast, pow_succ])`. Rewrite using `[e, hI.2.1 P n L _ _ hP hL (isSmoothHerm_hermZpow hX k) hX, ih]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fam_snoc_zpow_nat (hI : IsIntersectionFamily I) (hP : IsArithVar P (n + 1))
    (L : Fin n → HermLine ι) (hL : ∀ j, IsSmoothHerm (L j)) {X : HermLine ι} (hX : IsSmoothHerm X) (k : ℕ) :
    I P (n + 1) (Fin.snoc L (hermZpow X k)) = k * I P (n + 1) (Fin.snoc L X) := by
  induction k with
  | zero =>
    simp only [Nat.cast_zero, zero_mul]
    exact fam_snoc_zpow_zero hI hP L hL hX
  | succ k ih =>
    have e : hermZpow X ((k + 1 : ℕ) : ℤ) = (hermZpow X k).tensor X :=
      hermLine_eq_of (by simp [HermLine.tensor, hermZpow, add_smul])
        (funext fun z => by
          show X.h z ^ ((k + 1 : ℕ) : ℤ) = X.h z ^ (k : ℤ) * X.h z
          rw [zpow_natCast, zpow_natCast, pow_succ])
    rw [e, hI.2.1 P n L _ _ hP hL (isSmoothHerm_hermZpow hX k) hX, ih]
    push_cast
    ring

/- English proof (translation)
Take `⟨k, rfl | rfl⟩` from `Int.eq_nat_or_neg m`. Rewrite using `[fam_snoc_zpow_nat hI hP L hL hX k, Int.cast_natCast]`. Establish `hs : ∀ m : ℤ, IsSmoothHerm (hermZpow X m)` using `isSmoothHerm_hermZpow hX`. Establish `hsum` using `hI.2.1 P n L _ _ hP hL (hs (-k)) (hs k)`. Establish `h1 : (1 : MRing ι) ∉ P` using `(Ideal.ne_top_iff_one P).mp hP.2.1.1.ne_top`.

Establish `hh : IsMultiHomog (1 : MRing ι) (0 : K → ℕ)`. Introduce `d hd k'`. Rewrite `hd` using `[MvPolynomial.support_one, Finset.mem_singleton]`. Substitute `hd` using the available equality. Simplify using the standard rewrite rules.

Establish `hT : I P (n + 1) (Fin.snoc L ((hermZpow X (-k)).tensor (hermZpow X k))) = I P (n + 1) (Fin.snoc L (hermZpow X 0))`. Rewrite using `[hI.2.2 P n L _ 1 0 hP hL (isSmoothHerm_tensor (hs _) (hs _)) (fun k' => by simp [HermLine.tensor, hermZpow]) hh h1, hI.2.2 P n L _ 1 0 hP hL (hs 0) (fun k' => by simp [hermZpow]) hh h1, recR_eq, recR_eq]`. Use `congr 1`. Unfold `arInt`. Use `congr 1`.

Use function extensionality and compare the values at `z`. Unfold `logNorm`. Simplify using `only [map_one, norm_one]`. Use `show Real.log (1 / (X.h z ^ (-(k : ℤ)) * X.h z ^ (k : ℤ))) = Real.log (1 / X.h z ^ (0 : ℤ))`. Break down `eq_or_ne (X.h z) 0 with hx | hx` into its components or cases.

Rewrite using `[hx]`. Break down `eq_or_ne k 0 with rfl | hk` into its components or cases. Simplify using the standard rewrite rules. Rewrite using `[zero_zpow (k : ℤ) (by exact_mod_cast hk), mul_zero]`. Simplify using the standard rewrite rules.

Rewrite using `[zpow_neg, inv_mul_cancel₀ (zpow_ne_zero _ hx)]`. Simplify using the standard rewrite rules. Rewrite `hsum` using `[hT, fam_snoc_zpow_zero hI hP L hL hX, fam_snoc_zpow_nat hI hP L hL hX k]`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem fam_snoc_zpow (hI : IsIntersectionFamily I) (hP : IsArithVar P (n + 1))
    (L : Fin n → HermLine ι) (hL : ∀ j, IsSmoothHerm (L j)) {X : HermLine ι} (hX : IsSmoothHerm X) (m : ℤ) :
    I P (n + 1) (Fin.snoc L (hermZpow X m)) = m * I P (n + 1) (Fin.snoc L X) := by
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · rw [fam_snoc_zpow_nat hI hP L hL hX k, Int.cast_natCast]
  · have hs : ∀ m : ℤ, IsSmoothHerm (hermZpow X m) := isSmoothHerm_hermZpow hX
    have hsum := hI.2.1 P n L _ _ hP hL (hs (-k)) (hs k)
    have h1 : (1 : MRing ι) ∉ P := (Ideal.ne_top_iff_one P).mp hP.2.1.1.ne_top
    have hh : IsMultiHomog (1 : MRing ι) (0 : K → ℕ) := by
      intro d hd k'
      rw [MvPolynomial.support_one, Finset.mem_singleton] at hd
      subst hd
      simp
    have hT : I P (n + 1) (Fin.snoc L ((hermZpow X (-k)).tensor (hermZpow X k))) =
        I P (n + 1) (Fin.snoc L (hermZpow X 0)) := by
      rw [hI.2.2 P n L _ 1 0 hP hL (isSmoothHerm_tensor (hs _) (hs _))
          (fun k' => by simp [HermLine.tensor, hermZpow]) hh h1,
        hI.2.2 P n L _ 1 0 hP hL (hs 0) (fun k' => by simp [hermZpow]) hh h1, recR_eq, recR_eq]
      congr 1
      unfold arInt
      congr 1
      funext z
      unfold logNorm
      simp only [map_one, norm_one]
      show Real.log (1 / (X.h z ^ (-(k : ℤ)) * X.h z ^ (k : ℤ))) = Real.log (1 / X.h z ^ (0 : ℤ))
      rcases eq_or_ne (X.h z) 0 with hx | hx
      · rw [hx]
        rcases eq_or_ne k 0 with rfl | hk
        · simp
        · rw [zero_zpow (k : ℤ) (by exact_mod_cast hk), mul_zero]
          simp
      · rw [zpow_neg, inv_mul_cancel₀ (zpow_ne_zero _ hx)]
        simp
    rw [hT, fam_snoc_zpow_zero hI hP L hL hX, fam_snoc_zpow_nat hI hP L hL hX k] at hsum
    push_cast
    linarith

/- English proof (translation)
Establish `hs : ∀ j, IsSmoothHerm (Function.update L a B j)`. Introduce `j`. Break down `eq_or_ne j a with rfl | h` into its components or cases. Rewrite using `[Function.update_self]` and apply the resulting hypothesis. Rewrite using `[Function.update_of_ne h]`.

Conclude with `hL j`. Rewrite using `[← hI.1 P (n + 1) _ (Equiv.swap a (Fin.last n)) hP hs]`. Use `congr 1`. Use function extensionality and compare the values at `j`. Use `Fin.lastCases ?_ (fun i => ?_) j` and prove the remaining obligations.

Simplify using the standard rewrite rules. Rewrite using `[Function.comp_apply, Fin.snoc_castSucc, Function.update_of_ne]`. Introduce `h`. Rewrite `h` using `[Equiv.swap_apply_eq_iff, Equiv.swap_apply_left]`. Conclude with `Fin.castSucc_ne_last i h`.
-/
theorem fam_update_eq_snoc (hI : IsIntersectionFamily I) (hP : IsArithVar P (n + 1))
    (L : Fin (n + 1) → HermLine ι) (hL : ∀ j, IsSmoothHerm (L j)) (a : Fin (n + 1)) {B : HermLine ι}
    (hB : IsSmoothHerm B) :
    I P (n + 1) (Function.update L a B) =
      I P (n + 1) (Fin.snoc (fun i : Fin n => L (Equiv.swap a (Fin.last n) i.castSucc)) B) := by
  have hs : ∀ j, IsSmoothHerm (Function.update L a B j) := by
    intro j
    rcases eq_or_ne j a with rfl | h
    · rwa [Function.update_self]
    · rw [Function.update_of_ne h]
      exact hL j
  rw [← hI.1 P (n + 1) _ (Equiv.swap a (Fin.last n)) hP hs]
  congr 1
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp
  · rw [Function.comp_apply, Fin.snoc_castSucc, Function.update_of_ne]
    intro h
    rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_left] at h
    exact Fin.castSucc_ne_last i h

/- English proof (translation)
Unfold `lamLine`. Establish `hAA` using `isSmoothHerm_tensor hA hA`. Establish `hXc` using `isSmoothHerm_hermZpow hX (-c)`. Establish `hR : ∀ i : Fin n, IsSmoothHerm ((fun i : Fin n => L (Equiv.swap a (Fin.last n) i.castSucc)) i)` using `fun i => hL _`. Rewrite using `[fam_update_eq_snoc hI hP L hL a (isSmoothHerm_tensor hAA hXc), fam_update_eq_snoc hI hP L hL a hA, fam_update_eq_snoc hI hP L hL a hX]`.

Establish `h₁` using `hI.2.1 P n (fun i : Fin n => L (Equiv.swap a (Fin.last n) i.castSucc)) _ _ hP hR hAA hXc`. Establish `h₂` using `hI.2.1 P n (fun i : Fin n => L (Equiv.swap a (Fin.last n) i.castSucc)) _ _ hP hR hA hA`. Establish `h₃` using `fam_snoc_zpow hI hP (fun i : Fin n => L (Equiv.swap a (Fin.last n) i.castSucc)) hR hX (-c)`. Rewrite using `[h₁, h₂, h₃]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem fam_update_lamLine (hI : IsIntersectionFamily I) (hP : IsArithVar P (n + 1))
    (L : Fin (n + 1) → HermLine ι) (hL : ∀ j, IsSmoothHerm (L j)) (a : Fin (n + 1)) {A X : HermLine ι}
    (hA : IsSmoothHerm A) (hX : IsSmoothHerm X) (c : ℤ) :
    I P (n + 1) (Function.update L a (lamLine A X c)) =
      2 * I P (n + 1) (Function.update L a A) - c * I P (n + 1) (Function.update L a X) := by
  unfold lamLine
  have hAA := isSmoothHerm_tensor hA hA
  have hXc := isSmoothHerm_hermZpow hX (-c)
  have hR : ∀ i : Fin n, IsSmoothHerm ((fun i : Fin n => L (Equiv.swap a (Fin.last n) i.castSucc)) i) :=
    fun i => hL _
  rw [fam_update_eq_snoc hI hP L hL a (isSmoothHerm_tensor hAA hXc), fam_update_eq_snoc hI hP L hL a hA,
    fam_update_eq_snoc hI hP L hL a hX]
  have h₁ := hI.2.1 P n (fun i : Fin n => L (Equiv.swap a (Fin.last n) i.castSucc)) _ _ hP hR hAA hXc
  have h₂ := hI.2.1 P n (fun i : Fin n => L (Equiv.swap a (Fin.last n) i.castSucc)) _ _ hP hR hA hA
  have h₃ := fam_snoc_zpow hI hP (fun i : Fin n => L (Equiv.swap a (Fin.last n) i.castSucc)) hR hX (-c)
  rw [h₁, h₂, h₃]
  push_cast
  ring

/- English proof (translation)
Establish `hsm : ∀ i, IsSmoothHerm (![X, A] i)` using `Fin.forall_fin_two.mpr ⟨hX, hA⟩`. Proceed by induction on `T using Finset.induction_on generalizing t with`. Consider the case `empty`. Simplify using `only [Finset.notMem_empty, if_false]`. Conclude with `(famExt_basis ![X, A] t).symm`.

Consider the case `insert a T ha ih`. Establish `hins : ∀ {β : Type} (y : β) (F : Fin 2 → β), (fun j => if j ∈ insert a T then y else F (t j)) = Function.update (fun j => if j ∈ T then y else F (t j)) a y`. Introduce `β y F`. Use function extensionality and compare the values at `j`. Break down `eq_or_ne j a with rfl | h` into its components or cases.

Simplify using the standard rewrite rules. Simplify using `[h]`. Establish `hupd : ∀ {β : Type} (y : β) (F : Fin 2 → β) (i : Fin 2), Function.update (fun j => if j ∈ T then y else F (t j)) a (F i) = fun j => if j ∈ T then y else F (Function.update t a i j)`. Introduce `β y F i`. Use function extensionality and compare the values at `j`.

Break down `eq_or_ne j a with rfl | h` into its components or cases. Simplify using `[ha]`. Simplify using `[Function.update_of_ne h]`. Establish `hL : ∀ j, IsSmoothHerm ((fun j => if j ∈ T then lamLine A X c else ![X, A] (t j)) j)`. Introduce `j`.

Simplify using `only`. Use `split_ifs`. Conclude with `isSmoothHerm_tensor (isSmoothHerm_tensor hA hA) (isSmoothHerm_hermZpow hX _)`. Conclude with `hsm (t j)`. Establish `eL : (fun j => if j ∈ insert a T then lamLine A X c else ![X, A] (t j)) = Function.update (fun j => if j ∈ T then lamLine A X c else ![X, A] (t j)) a (lamLine A X c)` using `hins _ _`.

Establish `eV : (fun j => if j ∈ insert a T then (![-(c : ℝ), 2] : Fin 2 → ℝ) else Pi.single (t j) 1) = Function.update (fun j => if j ∈ T then (![-(c : ℝ), 2] : Fin 2 → ℝ) else Pi.single (t j) 1) a ![-(c : ℝ), 2]` using `hins (![-(c : ℝ), 2] : Fin 2 → ℝ) fun i => Pi.single i 1`. Establish `hA1 : Function.update (fun j => if j ∈ T then lamLine A X c else ![X, A] (t j)) a A = fun j => if j ∈ T then lamLine A X c else ![X, A] (Function.update t a 1 j)` using `hupd _ ![X, A] 1`. Establish `hX0 : Function.update (fun j => if j ∈ T then lamLine A X c else ![X, A] (t j)) a X = fun j => if j ∈ T then lamLine A X c else ![X, A] (Function.update t a 0 j)` using `hupd _ ![X, A] 0`. Establish `hV1 : Function.update (fun j => if j ∈ T then (![-(c : ℝ), 2] : Fin 2 → ℝ) else Pi.single (t j) 1) a (Pi.single 1 1) = fun j => if j ∈ T then ![-(c : ℝ), 2] else Pi.single (Function.update t a 1 j) 1` using `hupd (![-(c : ℝ), 2] : Fin 2 → ℝ) (fun i => Pi.single i 1) 1`. Establish `hV0 : Function.update (fun j => if j ∈ T then (![-(c : ℝ), 2] : Fin 2 → ℝ) else Pi.single (t j) 1) a (Pi.single 0 1) = fun j => if j ∈ T then ![-(c : ℝ), 2] else Pi.single (Function.update t a 0 j) 1` using `hupd (![-(c : ℝ), 2] : Fin 2 → ℝ) (fun i => Pi.single i 1) 0`.

Establish `hw : (![-(c : ℝ), 2] : Fin 2 → ℝ) = (2 : ℝ) • Pi.single 1 1 + (-(c : ℝ)) • Pi.single 0 1`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `fin_cases i <;> simp`. Rewrite using `[eL, eV, fam_update_lamLine hI hP _ hL a hA hX c, hA1, hX0, ih, ih, congrArg (Function.update (fun j => if j ∈ T then (![-(c : ℝ), 2] : Fin 2 → ℝ) else Pi.single (t j) 1) a) hw, MultilinearMap.map_update_add, MultilinearMap.map_update_smul, MultilinearMap.map_update_smul, hV1, hV …`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fam_eq_famExt (hI : IsIntersectionFamily I) (hP : IsArithVar P (n + 1)) {A X : HermLine ι}
    (hA : IsSmoothHerm A) (hX : IsSmoothHerm X) (c : ℤ) (T : Finset (Fin (n + 1))) (t : Fin (n + 1) → Fin 2) :
    I P (n + 1) (fun j => if j ∈ T then lamLine A X c else ![X, A] (t j)) =
      famExt I P (n + 1) ![X, A] (fun j => if j ∈ T then ![-(c : ℝ), 2] else Pi.single (t j) 1) := by
  have hsm : ∀ i, IsSmoothHerm (![X, A] i) := Fin.forall_fin_two.mpr ⟨hX, hA⟩
  induction T using Finset.induction_on generalizing t with
  | empty =>
    simp only [Finset.notMem_empty, if_false]
    exact (famExt_basis ![X, A] t).symm
  | insert a T ha ih =>
    have hins : ∀ {β : Type} (y : β) (F : Fin 2 → β),
        (fun j => if j ∈ insert a T then y else F (t j)) =
          Function.update (fun j => if j ∈ T then y else F (t j)) a y := by
      intro β y F
      funext j
      rcases eq_or_ne j a with rfl | h
      · simp
      · simp [h]
    have hupd : ∀ {β : Type} (y : β) (F : Fin 2 → β) (i : Fin 2),
        Function.update (fun j => if j ∈ T then y else F (t j)) a (F i) =
          fun j => if j ∈ T then y else F (Function.update t a i j) := by
      intro β y F i
      funext j
      rcases eq_or_ne j a with rfl | h
      · simp [ha]
      · simp [Function.update_of_ne h]
    have hL : ∀ j, IsSmoothHerm ((fun j => if j ∈ T then lamLine A X c else ![X, A] (t j)) j) := by
      intro j
      dsimp only
      split_ifs
      · exact isSmoothHerm_tensor (isSmoothHerm_tensor hA hA) (isSmoothHerm_hermZpow hX _)
      · exact hsm (t j)
    have eL : (fun j => if j ∈ insert a T then lamLine A X c else ![X, A] (t j)) =
        Function.update (fun j => if j ∈ T then lamLine A X c else ![X, A] (t j)) a (lamLine A X c) :=
      hins _ _
    have eV : (fun j => if j ∈ insert a T then (![-(c : ℝ), 2] : Fin 2 → ℝ) else Pi.single (t j) 1) =
        Function.update (fun j => if j ∈ T then (![-(c : ℝ), 2] : Fin 2 → ℝ) else Pi.single (t j) 1) a
          ![-(c : ℝ), 2] :=
      hins (![-(c : ℝ), 2] : Fin 2 → ℝ) fun i => Pi.single i 1
    have hA1 : Function.update (fun j => if j ∈ T then lamLine A X c else ![X, A] (t j)) a A =
        fun j => if j ∈ T then lamLine A X c else ![X, A] (Function.update t a 1 j) :=
      hupd _ ![X, A] 1
    have hX0 : Function.update (fun j => if j ∈ T then lamLine A X c else ![X, A] (t j)) a X =
        fun j => if j ∈ T then lamLine A X c else ![X, A] (Function.update t a 0 j) :=
      hupd _ ![X, A] 0
    have hV1 : Function.update (fun j => if j ∈ T then (![-(c : ℝ), 2] : Fin 2 → ℝ) else Pi.single (t j) 1) a
        (Pi.single 1 1) = fun j => if j ∈ T then ![-(c : ℝ), 2] else Pi.single (Function.update t a 1 j) 1 :=
      hupd (![-(c : ℝ), 2] : Fin 2 → ℝ) (fun i => Pi.single i 1) 1
    have hV0 : Function.update (fun j => if j ∈ T then (![-(c : ℝ), 2] : Fin 2 → ℝ) else Pi.single (t j) 1) a
        (Pi.single 0 1) = fun j => if j ∈ T then ![-(c : ℝ), 2] else Pi.single (Function.update t a 0 j) 1 :=
      hupd (![-(c : ℝ), 2] : Fin 2 → ℝ) (fun i => Pi.single i 1) 0
    have hw : (![-(c : ℝ), 2] : Fin 2 → ℝ) = (2 : ℝ) • Pi.single 1 1 + (-(c : ℝ)) • Pi.single 0 1 := by
      funext i
      fin_cases i <;> simp
    rw [eL, eV, fam_update_lamLine hI hP _ hL a hA hX c, hA1, hX0, ih, ih,
      congrArg (Function.update (fun j => if j ∈ T then (![-(c : ℝ), 2] : Fin 2 → ℝ) else Pi.single (t j) 1) a) hw, MultilinearMap.map_update_add, MultilinearMap.map_update_smul,
      MultilinearMap.map_update_smul, hV1, hV0, smul_eq_mul, smul_eq_mul]
    ring

/- English proof (translation)
Establish `hsm : ∀ i, IsSmoothHerm (![X, A] i)` using `Fin.forall_fin_two.mpr ⟨hX, hA⟩`. Establish `h` using `fam_eq_famExt hI hP hA hX c Finset.univ (fun _ => 0)`. Simplify using `only [Finset.mem_univ, if_true] at h`. Rewrite using `[h]`. Establish `hw : (fun _ : Fin (n + 1) => (![-(c : ℝ), 2] : Fin 2 → ℝ)) = fun _ => (2 : ℝ) • ((Pi.single 1 1 : Fin 2 → ℝ) + (-(c : ℝ) / 2) • Pi.single 0 1)`.

Use function extensionality and compare the values at `i k`. Use `fin_cases k`. Simplify using `only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Pi.smul_apply, Pi.add_apply, smul_eq_mul]`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.

Simplify using the standard rewrite rules. Rewrite using `[hw, MultilinearMap.map_smul_univ, Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, symm_expand _ (famExt_symm hI hP ![X, A] hsm)]`. Use `congr 1`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `hm : (mix j (Pi.single 0 1) (Pi.single 1 1) : Fin (n + 1) → Fin 2 → ℝ) = fun i => Pi.single ((fun i : Fin (n + 1) => if (i : ℕ) < j then (0 : Fin 2) else 1) i) 1`.

Use function extensionality and compare the values at `i`. Simplify using `only [mix]`. Apply the tactic sequence `split_ifs <;> rfl`. Rewrite using `[hm, famExt_basis]`. Use `congr 2`.

Use function extensionality and compare the values at `i`. Simplify using `only [mix, Function.comp]`. Apply the tactic sequence `split_ifs <;> rfl`.
-/
theorem fam_lamLine_expand (hI : IsIntersectionFamily I) (hP : IsArithVar P (n + 1)) {A X : HermLine ι}
    (hA : IsSmoothHerm A) (hX : IsSmoothHerm X) (c : ℤ) :
    I P (n + 1) (fun _ => lamLine A X c) =
      2 ^ (n + 1) * ∑ j ∈ Finset.range (n + 1 + 1),
        ((n + 1).choose j : ℝ) * (-(c : ℝ) / 2) ^ j * I P (n + 1) (mix j X A) := by
  have hsm : ∀ i, IsSmoothHerm (![X, A] i) := Fin.forall_fin_two.mpr ⟨hX, hA⟩
  have h := fam_eq_famExt hI hP hA hX c Finset.univ (fun _ => 0)
  simp only [Finset.mem_univ, if_true] at h
  rw [h]
  have hw : (fun _ : Fin (n + 1) => (![-(c : ℝ), 2] : Fin 2 → ℝ)) =
      fun _ => (2 : ℝ) • ((Pi.single 1 1 : Fin 2 → ℝ) + (-(c : ℝ) / 2) • Pi.single 0 1) := by
    funext i k
    fin_cases k
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
      simp
      ring
    · simp
  rw [hw, MultilinearMap.map_smul_univ, Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    symm_expand _ (famExt_symm hI hP ![X, A] hsm)]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  have hm : (mix j (Pi.single 0 1) (Pi.single 1 1) : Fin (n + 1) → Fin 2 → ℝ) =
      fun i => Pi.single ((fun i : Fin (n + 1) => if (i : ℕ) < j then (0 : Fin 2) else 1) i) 1 := by
    funext i
    simp only [mix]
    split_ifs <;> rfl
  rw [hm, famExt_basis]
  congr 2
  funext i
  simp only [mix, Function.comp]
  split_ifs <;> rfl

end Family

end

end GroundTheory.Heights₂.Heights.Inter
