import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.RestPathFrom
import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.DividedPowerZeroOfGlActionZero

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.ColumnFamilies

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.LemmaBAlt

/- English proof (translation)
Use function extensionality and compare the values at `J`. Unfold `wedgeR Formalism.InvariantFactorPaths.GelfandTsetlinBases.wedgeF Formalism.InvariantFactorPaths.GelfandTsetlinBases.sg`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem wedgeR_eq_wedgeF {n : ℕ} {P : Type*} [CommRing P] (x : Fin n → P) (K : Finset (Fin n) → P) :
    wedgeR x K = Formalism.InvariantFactorPaths.GelfandTsetlinBases.wedgeF K x := by
  funext J
  unfold wedgeR Formalism.InvariantFactorPaths.GelfandTsetlinBases.wedgeF Formalism.InvariantFactorPaths.GelfandTsetlinBases.sg
  refine Finset.sum_congr rfl fun m _ => ?_
  push_cast
  ring

/- English proof (translation)
Use function extensionality and compare the values at `J`. Unfold `contrR Formalism.InvariantFactorPaths.GelfandTsetlinBases.contrF Formalism.InvariantFactorPaths.GelfandTsetlinBases.sg`. Rewrite using `[Finset.compl_eq_univ_sdiff]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem contrR_eq_contrF {n : ℕ} {P : Type*} [CommRing P] (x : Fin n → P) (K : Finset (Fin n) → P) :
    contrR x K = Formalism.InvariantFactorPaths.GelfandTsetlinBases.contrF K x := by
  funext J
  unfold contrR Formalism.InvariantFactorPaths.GelfandTsetlinBases.contrF Formalism.InvariantFactorPaths.GelfandTsetlinBases.sg
  rw [Finset.compl_eq_univ_sdiff]
  refine Finset.sum_congr rfl fun m _ => ?_
  push_cast
  ring

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem colHeight_eq {n : ℕ} (mu : Fin n → ℤ) (c : ℤ) : Formalism.InvariantFactorPaths.GelfandTsetlinBases.colHeight mu c = colH mu c := rfl

/- English proof (translation)
Unfold `ext`. Rewrite using `[dif_pos h]`.
-/
theorem ext_apply {N n : ℕ} (mu : Fin (N + 1) → Fin n → ℤ) (j : ℕ) (h : j < N + 1) : ext mu j = mu ⟨j, h⟩ := by
  unfold ext; rw [dif_pos h]

/- English proof (translation)
Establish `hs` using `P.step ⟨j, h⟩`. Establish `e1 : (Fin.castSucc (⟨j, h⟩ : Fin N)) = ⟨j, by omega⟩` using `rfl`. Establish `e2 : (Fin.succ (⟨j, h⟩ : Fin N)) = ⟨j + 1, by omega⟩` using `rfl`. Rewrite `hs` using `[e1, e2]`. Use `split_ifs with hv`.

Rewrite `hs` using `[if_pos hv]`. Conclude with `column_height_mono hs.1 c`. Rewrite `hs` using `[if_neg hv]`. Conclude with `column_height_mono hs.1 c`.
-/
theorem colH_step {n N : ℕ} {LL : Letters (Fin N)} {B : Fin N → ℕ} (P : PPath n N LL B) (c : ℤ) (j : ℕ) (h : j < N) :
    if LL.vec ⟨j, h⟩ then colH (P.mu ⟨j, by omega⟩) c ≤ colH (P.mu ⟨j + 1, by omega⟩) c
    else colH (P.mu ⟨j + 1, by omega⟩) c ≤ colH (P.mu ⟨j, by omega⟩) c := by
  have hs := P.step ⟨j, h⟩
  have e1 : (Fin.castSucc (⟨j, h⟩ : Fin N)) = ⟨j, by omega⟩ := rfl
  have e2 : (Fin.succ (⟨j, h⟩ : Fin N)) = ⟨j + 1, by omega⟩ := rfl
  rw [e1, e2] at hs
  split_ifs with hv
  · rw [if_pos hv] at hs
    exact column_height_mono hs.1 c
  · rw [if_neg hv] at hs
    exact column_height_mono hs.1 c

/- English proof (translation)
Proceed by induction on `j generalizing J with`. Consider the case `zero`. Simplify using `only [Kcol, Formalism.InvariantFactorPaths.GelfandTsetlinBases.pathWord]`. Conclude with `map_exterior_one (rename (iv N n) : MvPolynomial (Fin N × Fin n) R →ₐ[R] _).toRingHom J`. Consider the case `succ j ih`.

Establish `h : j < N` using `hj`. Establish `ih'` using `ih (by omega)`. Simplify using `only [Kcol, Formalism.InvariantFactorPaths.GelfandTsetlinBases.pathWord]`. Rewrite using `[dif_pos h]`. Establish `hm` using `map_column_operator (rename (iv N n) : MvPolynomial (Fin N × Fin n) R →ₐ[R] _).toRingHom c (colH (P.mu ⟨j, by omega⟩) c) (colH (P.mu ⟨j + 1, by omega⟩) c) (letVec R ⟨j, h⟩) (Kcol R P.mu c j) J`.

Establish `h1 : (fun m => (rename (iv N n) : MvPolynomial (Fin N × Fin n) R →ₐ[R] _).toRingHom (letVec R (⟨j, h⟩ : Fin N) m)) = fun a => (X (j, a) : MvPolynomial (ℕ × Fin n) R)`. Use function extensionality and compare the values at `m`. Simplify using `[letVec, iv]`. Establish `h2 : (fun J => (rename (iv N n) : MvPolynomial (Fin N × Fin n) R →ₐ[R] _).toRingHom (Kcol R P.mu c j J)) = Formalism.InvariantFactorPaths.GelfandTsetlinBases.pathWord (isV LL) (ext P.mu) c (fun i a => (X (i, a) : MvPolynomial (ℕ × Fin n) R)) j` using `funext ih'`. Rewrite `hm` using `[h1, h2]`.

Establish `hm' : rename (iv N n) (colStep c (colH (P.mu ⟨j, by omega⟩) c) (colH (P.mu ⟨j + 1, by omega⟩) c) (letVec R ⟨j, h⟩) (Kcol R P.mu c j) J) = _` using `hm`. Rewrite using `[hm', colHeight_eq, colHeight_eq, ext_apply P.mu j (by omega), ext_apply P.mu (j + 1) (by omega)]`. Establish `hst` using `colH_step P c j h`. Establish `hV : isV LL j = LL.vec ⟨j, h⟩` using `by unfold isV; rw [dif_pos h]`. Rewrite using `[hV]`.

Unfold `colStep Formalism.InvariantFactorPaths.GelfandTsetlinBases.stepF`. Distinguish the cases in `hv : LL.vec ⟨j, h⟩ = true`. Rewrite `hst` using `[if_pos hv]`. Rewrite using `[hv]`. Distinguish the cases in `he : colH (P.mu ⟨j + 1, by omega⟩) c = colH (P.mu ⟨j, by omega⟩) c`.

Rewrite using `[if_pos he, if_neg (by omega), if_neg (by omega)]`. Rewrite using `[if_neg he, if_pos (by omega)]`. Distinguish the cases in `hc : 1 ≤ c`. Simplify using `[hc, wedgeR_eq_wedgeF]`. Simplify using `[hc, contrR_eq_contrF]`.

Rewrite `hst` using `[if_neg hv]`. Establish `hv' : LL.vec ⟨j, h⟩ = false` using `by simpa using hv`. Rewrite using `[hv']`. Distinguish the cases in `he : colH (P.mu ⟨j + 1, by omega⟩) c = colH (P.mu ⟨j, by omega⟩) c`. Rewrite using `[if_pos he, if_neg (by omega), if_neg (by omega)]`.

Rewrite using `[if_neg he, if_neg (by omega), if_pos (by omega)]`. Distinguish the cases in `hc : 1 ≤ c`. Simplify using `[hc, contrR_eq_contrF]`. Simplify using `[hc, wedgeR_eq_wedgeF]`.
-/
theorem Kcol_eq_pathWord (R : Type*) [CommRing R] {n N : ℕ} {LL : Letters (Fin N)} {B : Fin N → ℕ}
    (P : PPath n N LL B) (c : ℤ) (j : ℕ) (hj : j ≤ N) (J : Finset (Fin n)) :
    rename (iv N n) (Kcol R P.mu c j J) =
      Formalism.InvariantFactorPaths.GelfandTsetlinBases.pathWord (isV LL) (ext P.mu) c
        (fun i a => (X (i, a) : MvPolynomial (ℕ × Fin n) R)) j J := by
  induction j generalizing J with
  | zero =>
    simp only [Kcol, Formalism.InvariantFactorPaths.GelfandTsetlinBases.pathWord]
    exact map_exterior_one (rename (iv N n) : MvPolynomial (Fin N × Fin n) R →ₐ[R] _).toRingHom J
  | succ j ih =>
    have h : j < N := hj
    have ih' := ih (by omega)
    simp only [Kcol, Formalism.InvariantFactorPaths.GelfandTsetlinBases.pathWord]
    rw [dif_pos h]
    have hm := map_column_operator (rename (iv N n) : MvPolynomial (Fin N × Fin n) R →ₐ[R] _).toRingHom c
      (colH (P.mu ⟨j, by omega⟩) c) (colH (P.mu ⟨j + 1, by omega⟩) c) (letVec R ⟨j, h⟩) (Kcol R P.mu c j) J
    have h1 : (fun m => (rename (iv N n) : MvPolynomial (Fin N × Fin n) R →ₐ[R] _).toRingHom
        (letVec R (⟨j, h⟩ : Fin N) m)) = fun a => (X (j, a) : MvPolynomial (ℕ × Fin n) R) := by
      funext m; simp [letVec, iv]
    have h2 : (fun J => (rename (iv N n) : MvPolynomial (Fin N × Fin n) R →ₐ[R] _).toRingHom
        (Kcol R P.mu c j J)) = Formalism.InvariantFactorPaths.GelfandTsetlinBases.pathWord (isV LL) (ext P.mu) c
        (fun i a => (X (i, a) : MvPolynomial (ℕ × Fin n) R)) j := funext ih'
    rw [h1, h2] at hm
    have hm' : rename (iv N n) (colStep c (colH (P.mu ⟨j, by omega⟩) c) (colH (P.mu ⟨j + 1, by omega⟩) c)
        (letVec R ⟨j, h⟩) (Kcol R P.mu c j) J) = _ := hm
    rw [hm', colHeight_eq, colHeight_eq, ext_apply P.mu j (by omega), ext_apply P.mu (j + 1) (by omega)]
    have hst := colH_step P c j h
    have hV : isV LL j = LL.vec ⟨j, h⟩ := by unfold isV; rw [dif_pos h]
    rw [hV]
    unfold colStep Formalism.InvariantFactorPaths.GelfandTsetlinBases.stepF
    by_cases hv : LL.vec ⟨j, h⟩ = true
    · rw [if_pos hv] at hst
      rw [hv]
      by_cases he : colH (P.mu ⟨j + 1, by omega⟩) c = colH (P.mu ⟨j, by omega⟩) c
      · rw [if_pos he, if_neg (by omega), if_neg (by omega)]
      · rw [if_neg he, if_pos (by omega)]
        by_cases hc : 1 ≤ c
        · simp [hc, wedgeR_eq_wedgeF]
        · simp [hc, contrR_eq_contrF]
    · rw [if_neg hv] at hst
      have hv' : LL.vec ⟨j, h⟩ = false := by simpa using hv
      rw [hv']
      by_cases he : colH (P.mu ⟨j + 1, by omega⟩) c = colH (P.mu ⟨j, by omega⟩) c
      · rw [if_pos he, if_neg (by omega), if_neg (by omega)]
      · rw [if_neg he, if_neg (by omega), if_pos (by omega)]
        by_cases hc : 1 ≤ c
        · simp [hc, contrR_eq_contrF]
        · simp [hc, wedgeR_eq_wedgeF]

/- English proof (translation)
Establish `hT : ∀ m, |mu i m| ≤ ∑ i, ∑ m, |mu i m|` using `fun m => abs_entry_le_total mu i m`. Establish `hT0 : (0 : ℤ) ≤ ∑ i, ∑ m, |mu i m|` using `Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _`. Simplify using `only [colRange, Finset.mem_Icc, not_and_or, not_le] at hc`. Unfold `colH`. Break down `hc with hc | hc` into its components or cases.

Rewrite using `[if_neg (by omega)]`. Rewrite using `[Finset.filter_true_of_mem, Finset.card_univ, Fintype.card_fin]`. Introduce `m _`. Use `abs_le.mp (hT m)` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Rewrite using `[if_pos (by omega)]`. Rewrite using `[Finset.card_eq_zero, Finset.filter_eq_empty_iff]`. Introduce `m _`. Use `abs_le.mp (hT m)` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem colH_off {N n : ℕ} (mu : Fin (N + 1) → Fin n → ℤ) {c : ℤ} (hc : c ∉ colRange mu) (i : Fin (N + 1)) :
    colH (mu i) c = if 1 ≤ c then 0 else n := by
  have hT : ∀ m, |mu i m| ≤ ∑ i, ∑ m, |mu i m| := fun m => abs_entry_le_total mu i m
  have hT0 : (0 : ℤ) ≤ ∑ i, ∑ m, |mu i m| := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  simp only [colRange, Finset.mem_Icc, not_and_or, not_le] at hc
  unfold colH
  rcases hc with hc | hc
  · rw [if_neg (by omega)]
    rw [Finset.filter_true_of_mem, Finset.card_univ, Fintype.card_fin]
    intro m _
    have := abs_le.mp (hT m)
    omega
  · rw [if_pos (by omega)]
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro m _
    have := abs_le.mp (hT m)
    omega

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero => rfl`. Consider the case `succ j ih`. Simplify using `only [Formalism.InvariantFactorPaths.GelfandTsetlinBases.pathWord]`. Rewrite using `[colHeight_eq, colHeight_eq, ext_apply mu j (by omega), ext_apply mu (j + 1) (by omega), colH_off mu hc, colH_off mu hc, if_pos rfl]`.

Conclude with `ih (by omega)`.
-/
theorem pathWord_off (R : Type*) [CommRing R] {n N : ℕ} (isVec : ℕ → Bool) (mu : Fin (N + 1) → Fin n → ℤ) {c : ℤ}
    (hc : c ∉ colRange mu) (Xr : ℕ → Fin n → R) (j : ℕ) (hj : j ≤ N) :
    Formalism.InvariantFactorPaths.GelfandTsetlinBases.pathWord isVec (ext mu) c Xr j = Formalism.InvariantFactorPaths.GelfandTsetlinBases.oneF := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [Formalism.InvariantFactorPaths.GelfandTsetlinBases.pathWord]
    rw [colHeight_eq, colHeight_eq, ext_apply mu j (by omega), ext_apply mu (j + 1) (by omega),
      colH_off mu hc, colH_off mu hc, if_pos rfl]
    exact ih (by omega)

/- English proof (translation)
Introduce `R _ n N LL B P I hI`. Unfold `Psi Formalism.InvariantFactorPaths.GelfandTsetlinBases.psiPath`. Rewrite using `[map_prod]`. Rewrite using `[finprod_eq_prod_of_mulSupport_subset (s := colRange P.mu)]`. Conclude with `Finset.prod_congr rfl fun c _ => Kcol_eq_pathWord R P c N le_rfl (I c)`.

Introduce `c hc`. Assume the negation of the conclusion as `hcn`. Apply `hc` to reduce the goal to its premises. Establish `hcn' : c ∉ colRange P.mu` using `hcn`. Use `show Formalism.InvariantFactorPaths.GelfandTsetlinBases.pathWord (isV LL) (ext P.mu) c _ N (I c) = 1`.

Rewrite using `[pathWord_off _ _ _ hcn' _ N le_rfl]`. Establish `hcard` using `hI c`. Rewrite `hcard` using `[colHeight_eq]`. Establish `h0 : colH (pEnd P.mu) c = if 1 ≤ c then 0 else n` using `colH_off P.mu hcn' (Fin.last N)`. Establish `: (I c).card = 0`.

Rewrite using `[hcard, h0]`. Apply the tactic sequence `split_ifs <;> simp`. Rewrite `this` using `[Finset.card_eq_zero]`. Rewrite using `[this]`. Simplify using `[Formalism.InvariantFactorPaths.GelfandTsetlinBases.oneF]`.
-/
theorem restPsi : RestPsi := by
  intro R _ n N LL B P I hI
  unfold Psi Formalism.InvariantFactorPaths.GelfandTsetlinBases.psiPath
  rw [map_prod]
  rw [finprod_eq_prod_of_mulSupport_subset (s := colRange P.mu)]
  · exact Finset.prod_congr rfl fun c _ => Kcol_eq_pathWord R P c N le_rfl (I c)
  · intro c hc
    by_contra hcn
    apply hc
    have hcn' : c ∉ colRange P.mu := hcn
    show Formalism.InvariantFactorPaths.GelfandTsetlinBases.pathWord (isV LL) (ext P.mu) c _ N (I c) = 1
    rw [pathWord_off _ _ _ hcn' _ N le_rfl]
    have hcard := hI c
    rw [colHeight_eq] at hcard
    have h0 : colH (pEnd P.mu) c = if 1 ≤ c then 0 else n := colH_off P.mu hcn' (Fin.last N)
    have : (I c).card = 0 := by
      rw [hcard, h0]
      split_ifs <;> simp
    rw [Finset.card_eq_zero] at this
    rw [this]
    simp [Formalism.InvariantFactorPaths.GelfandTsetlinBases.oneF]

end Formalism.MainNotions.G.ColumnFamilies
