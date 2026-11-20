import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MonomialRepresentations.HenselDiag

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

section
variable {R : Type} [CommRing R]

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev, Matrix.mul_apply, Fin.sum_univ_four] <;> ring`.
-/
private theorem adj_mul' (X Y : M4 R) : adj (X * Y) = adj Y * adj X := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev]`.
-/
private theorem adj_adj' (X : M4 R) : adj (adj X) = X := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev]

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev, Matrix.diagonal]`.
-/
private theorem adj_diag' (d : Fin 4 → R) : adj (Matrix.diagonal d) = Matrix.diagonal fun i => d i.rev := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev, Matrix.diagonal]

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev]`.
-/
private theorem adj_sub_one (X : M4 R) : adj (X - 1) = adj X - 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev]

/- English proof (translation)
Assume the negation of the conclusion as `hx`. Establish `hx' : x ∈ maximalIdeal R` using `(mem_maximalIdeal x).mpr hx`. Establish `hy' : y ∈ maximalIdeal R`. Use `Ideal.sub_mem _ hx' h` as an intermediate fact. Rewrite `this` using `[sub_sub_cancel]`. Then use the resulting hypothesis.

Conclude with `(mem_maximalIdeal y).mp hy' hy`.
-/
private theorem unit_of_sub [IsLocalRing R] {x y : R} (hy : IsUnit y) (h : x - y ∈ maximalIdeal R) : IsUnit x := by
  by_contra hx
  have hx' : x ∈ maximalIdeal R := (mem_maximalIdeal x).mpr hx
  have hy' : y ∈ maximalIdeal R := by
    have := Ideal.sub_mem _ hx' h
    rwa [sub_sub_cancel] at this
  exact (mem_maximalIdeal y).mp hy' hy

private def sg (R : Type) [CommRing R] : Fin 4 → R := ![1, -1, 1, -1]

/- English proof (translation)
Apply the tactic sequence `fin_cases i <;> simp [sg]`.
-/
private theorem sg_sq (i : Fin 4) : sg R i * sg R i = 1 := by fin_cases i <;> simp [sg]

/- English proof (translation)
Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [sg, lamW] at h ⊢`.
-/
private theorem sg_ne (i j : Fin 4) (h : lamW i ≠ lamW j) : sg R i * sg R j = -1 := by
  fin_cases i <;> fin_cases j <;> simp [sg, lamW] at h ⊢

/- English proof (translation)
Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [sg, lamW] at h ⊢`.
-/
private theorem sg_eq (i j : Fin 4) (h : lamW i = lamW j) : sg R i = sg R j := by
  fin_cases i <;> fin_cases j <;> simp [sg, lamW] at h ⊢

end

/- English proof (translation)
Introduce `C _ _ _ ν g h2u hg hoff hdiff hν`. Use `haveI : HenselianLocalRing C := { (inferInstance : IsLocalRing C) with is_henselian := fun f hf a₀ h₁ h₂ => (IsAdicComplete.henselianRing C (maximalIdeal C)).is_henselian f hf a₀ h₁ (h₂.map (Ideal.Quotient.mk _)) }`. Take `⟨u, d, hu1, hgu, hdg, huniq⟩` from `UpperTheory.V.AlgebraTools.henselDiag C (Fin 4) g hoff hdiff`. Establish `hg' : adj g * g = ν • 1` using `hg`. Establish `mulL : ∀ X Y : M4 C, (∀ i j, X i j ∈ maximalIdeal C) → ∀ i j, (X * Y) i j ∈ maximalIdeal C`.

Introduce `X Y hX i j`. Rewrite using `[Matrix.mul_apply]`. Conclude with `Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (hX i k)`. Establish `mulR : ∀ X Y : M4 C, (∀ i j, Y i j ∈ maximalIdeal C) → ∀ i j, (X * Y) i j ∈ maximalIdeal C`. Introduce `X Y hY i j`.

Rewrite using `[Matrix.mul_apply]`. Conclude with `Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (hY k j)`. Establish `adjM : ∀ X : M4 C, (∀ i j, X i j ∈ maximalIdeal C) → ∀ i j, adj X i j ∈ maximalIdeal C`. Introduce `X hX i j`. Rewrite using `[adj_apply, zsmul_eq_mul]`.

Conclude with `Ideal.mul_mem_left _ _ (hX _ _)`. Establish `hW1 : ∀ i j, (adj u * u - 1) i j ∈ maximalIdeal C`. Establish `e : adj u * u - 1 = adj (u - 1) * (u - 1) + adj (u - 1) + (u - 1)`. Rewrite using `[adj_sub_one]`. Use `noncomm_ring`.

Introduce `i j`. Rewrite using `[e, Matrix.add_apply, Matrix.add_apply]`. Conclude with `Ideal.add_mem _ (Ideal.add_mem _ (mulL _ _ (adjM _ hu1) i j) (adjM _ hu1 i j)) (hu1 i j)`. Establish `hWu : ∀ i, IsUnit ((adj u * u) i i)` using `fun i => unit_of_sub isUnit_one (by`. Use `hW1 i i` as an intermediate fact.

Rewrite using `[Matrix.sub_apply, Matrix.one_apply_eq] at this)` and apply the resulting hypothesis. Establish `hkey : ν • (adj u * u) = adj (Matrix.diagonal d) * (adj u * u) * Matrix.diagonal d`. Establish `e1 : adj u * adj g = adj (Matrix.diagonal d) * adj u`. Rewrite using `[← adj_mul', ← adj_mul', hgu]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hg']`. Simplify using `[Matrix.mul_smul, Matrix.smul_mul]`. Use `_ = (adj u * adj g) * (g * u) := by simp only [Matrix.mul_assoc]`. Use `_ = adj (Matrix.diagonal d) * adj u * (u * Matrix.diagonal d) := by rw [e1, hgu]`. Use `_ = _ := by simp only [Matrix.mul_assoc]`.

Establish `hent : ∀ i j, ν * (adj u * u) i j = d i.rev * (adj u * u) i j * d j`. Introduce `i j`. Use `congrFun (congrFun hkey i) j` as an intermediate fact. Rewrite `this` using `[adj_diag']`. Simplify using `only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_diagonal, Matrix.diagonal_mul] at this`.

Conclude with `this`. Establish `hdd : ∀ i, d i.rev * d i = ν`. Introduce `i`. Establish `h0 : (adj u * u) i i * (d i.rev * d i - ν) = 0`. Take the linear combination `(-1 : C) * hent i i`.

Conclude with `sub_eq_zero.mp ((hWu i).mul_right_eq_zero.mp h0)`. Establish `hdu : ∀ i, IsUnit (d i)` using `fun i => by`. Establish `: IsUnit (d i.rev * d i)` using `by rw [hdd i]; exact hν`. Conclude with `isUnit_of_mul_isUnit_right this`. Establish `hoffW : ∀ i j, i ≠ j → (adj u * u) i j = 0`.

Introduce `i j hij`. Establish `h0 : (adj u * u) i j * (d i.rev * d j - ν) = 0`. Take the linear combination `(-1 : C) * hent i j`. Establish `hu : IsUnit (d i.rev * d j - ν)`. Rewrite using `[← hdd i, ← mul_sub]`.

Use `(hdu _).mul ?_` and prove the remaining obligations. Use `unit_of_sub (hdiff j i (Ne.symm hij)) ?_` and prove the remaining obligations. Use `Ideal.sub_mem _ (hdg j) (hdg i)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.

Conclude with `hu.mul_left_eq_zero.mp h0`. Take `⟨w, hw⟩ : ∃ w : Fin 4 → C, ∀ i, w i = (adj u * u) i i` from `⟨_, fun _ => rfl⟩`. Establish `hWd : adj u * u = Matrix.diagonal w`. Use extensionality with `i j`. Distinguish the cases in `hij : i = j`.

Substitute `hij` using the available equality. Rewrite using `[Matrix.diagonal_apply_eq, hw]`. Rewrite using `[hoffW i j hij, Matrix.diagonal_apply_ne _ hij]`. Establish `hwu : ∀ i, IsUnit (w i)` using `fun i => by rw [hw]; exact hWu i`. Establish `hwm : ∀ i, w i - 1 ∈ maximalIdeal C` using `fun i => by`.

Use `hW1 i i` as an intermediate fact. Rewrite `this` using `[Matrix.sub_apply, Matrix.one_apply_eq, ← hw]`. Then use the resulting hypothesis. Establish `hwrev : ∀ i, w i.rev = w i`. Establish `h : adj (adj u * u) = adj u * u` using `by rw [adj_mul', adj_adj']`. Rewrite `h` using `[hWd, adj_diag']`.

Introduce `i`. Use `congrFun (congrFun h i) i` as an intermediate fact. Simplify using `using this`. Establish `h21 : w 2 = w 1` using `by simpa [Fin.rev] using hwrev 1`. Establish `h30 : w 3 = w 0` using `by simpa [Fin.rev] using hwrev 0`.

Take `⟨a, ha⟩ : ∃ a, a * w 1 = 1` from `⟨_, (hwu 1).val_inv_mul⟩`. Take `⟨b, hb⟩ : ∃ b, b * w 0 = 1` from `⟨_, (hwu 0).val_inv_mul⟩`. Establish `ha1 : a - 1 ∈ maximalIdeal C`. Establish `e : a - 1 = -(a * (w 1 - 1))` using `by linear_combination ha`. Rewrite using `[e]`.

Conclude with `Submodule.neg_mem _ (Ideal.mul_mem_left _ _ (hwm 1))`. Establish `hb1 : b - 1 ∈ maximalIdeal C`. Establish `e : b - 1 = -(b * (w 0 - 1))` using `by linear_combination hb`. Rewrite using `[e]`. Conclude with `Submodule.neg_mem _ (Ideal.mul_mem_left _ _ (hwm 0))`.

Take `⟨t, ht⟩ : ∃ t : Fin 4 → C, t = ![1, 1, a, b]` from `⟨_, rfl⟩`. Establish `htw : ∀ i, t i.rev * w i * t i = 1`. Introduce `i`. Apply the tactic sequence `fin_cases i <;> simp [ht, Fin.rev, h21, h30] <;> first | linear_combination ha | linear_combination hb`. Establish `htm : ∀ i, t i - 1 ∈ maximalIdeal C`.

Introduce `i`. Apply the tactic sequence `fin_cases i <;> simp [ht] <;> first | exact ha1 | exact hb1`. Use `⟨u * Matrix.diagonal t, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `show adj (u * Matrix.diagonal t) * (u * Matrix.diagonal t) = (1 : C) • (1 : M4 C)`. Rewrite using `[adj_mul', adj_diag', one_smul]`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = 1 := by`. Rewrite using `[hWd, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`.

Use function extensionality and compare the values at `i`. Conclude with `htw i`. Introduce `i j`. Establish `e : u * Matrix.diagonal t - 1 = (u - 1) * Matrix.diagonal t + (Matrix.diagonal t - 1)` using `by noncomm_ring`. Rewrite using `[e, Matrix.add_apply]`.

Use `Ideal.add_mem _ (mulL _ _ hu1 i j) ?_` and prove the remaining obligations. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Rewrite using `[Matrix.sub_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq]`. Conclude with `htm i`.

Rewrite using `[Matrix.sub_apply, Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij, sub_zero]`. Conclude with `Submodule.zero_mem _`. Establish `e : adj (u * Matrix.diagonal t) * g * (u * Matrix.diagonal t) = Matrix.diagonal (fun i => t i.rev) * (adj u * u) * Matrix.diagonal d * Matrix.diagonal t`. Rewrite using `[adj_mul', adj_diag']`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = _ := by`. Rewrite using `[hgu]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[e, hWd, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]`.

Conclude with `Matrix.isDiag_diagonal _`. Introduce `hB`. Establish `hB' : ∀ i j, lamW i ≠ lamW j → g i j = 0` using `hB`. Take `⟨S, hS⟩ : ∃ S : M4 C, S = Matrix.diagonal (sg C)` from `⟨_, rfl⟩`. Establish `hSS : S * S = 1`.

Rewrite using `[hS, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Conclude with `sg_sq (R := C) i`. Establish `hgS : g * S = S * g`.

Use extensionality with `i j`. Rewrite using `[hS, Matrix.mul_diagonal, Matrix.diagonal_mul]`. Distinguish the cases in `h : lamW i = lamW j`. Rewrite using `[sg_eq (R := C) i j h, mul_comm]`. Rewrite using `[hB' i j h]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hdS : Matrix.diagonal d * S = S * Matrix.diagonal d`. Rewrite using `[hS, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Expand and normalize the polynomial expressions, which then agree. Establish `h1 : ∀ i j, (S * u * S - 1) i j ∈ maximalIdeal C`. Establish `e : S * u * S - 1 = S * (u - 1) * S`. Rewrite using `[Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hSS]`. Introduce `i j`.

Rewrite using `[e]`. Conclude with `mulL _ _ (mulR _ _ hu1) i j`. Establish `h2 : g * (S * u * S) = S * u * S * Matrix.diagonal d`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, hgS, Matrix.mul_assoc S g u]`.

Use `_ = S * u * (Matrix.diagonal d * S) := by`. Rewrite using `[hgu]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = S * u * S * Matrix.diagonal d := by`. Rewrite using `[hdS]`.

Simplify using `only [Matrix.mul_assoc]`. Take `⟨-, t', ht'⟩` from `huniq (S * u * S) d h1 h2`. Establish `hent2 : ∀ i j, sg C i * u i j * sg C j = u i j * t' j`. Introduce `i j`. Use `congrFun (congrFun ht' i) j` as an intermediate fact.

Simplify using `only [hS, Matrix.mul_diagonal, Matrix.diagonal_mul] at this`. Conclude with `this`. Establish `ht'1 : ∀ j, t' j = 1`. Introduce `j`. Establish `h` using `hent2 j j`.

Establish `hu : IsUnit (u j j)` using `unit_of_sub isUnit_one (by`. Use `hu1 j j` as an intermediate fact. Rewrite using `[Matrix.sub_apply, Matrix.one_apply_eq] at this)` and apply the resulting hypothesis. Establish `h0 : u j j * (t' j - 1) = 0`. Take the linear combination `(-1 : C) * h + u j j * sg_sq (R := C) j`.

Conclude with `sub_eq_zero.mp (hu.mul_right_eq_zero.mp h0)`. Establish `hBu : ∀ i j, lamW i ≠ lamW j → u i j = 0`. Introduce `i j hij`. Establish `h` using `hent2 i j`. Rewrite `h` using `[ht'1 j, mul_one]`.

Establish `h' : (2 : C) * u i j = 0`. Take the linear combination `(-1 : C) * h + u i j * sg_ne (R := C) i j hij`. Conclude with `h2u.mul_right_eq_zero.mp h'`. Introduce `i j hij`. Rewrite using `[Matrix.mul_diagonal, hBu i j hij, zero_mul]`.
-/
theorem UpperTheory.V.Ws.normal :
    ∀ (C : Type) [CommRing C] [IsLocalRing C] [IsAdicComplete (maximalIdeal C) C] (ν : C) (g : M4 C), IsUnit (2 : C) → IsGSp ν g →
      (∀ i j, i ≠ j → g i j ∈ maximalIdeal C) → (∀ i j, i ≠ j → IsUnit (g i i - g j j)) → IsUnit ν →
      ∃ u : M4 C, IsGSp 1 u ∧ (∀ i j, (u - 1) i j ∈ maximalIdeal C) ∧ (adj u * g * u).IsDiag ∧ (IsBlock g → IsBlock u) := by
  intro C _ _ _ ν g h2u hg hoff hdiff hν
  haveI : HenselianLocalRing C :=
    { (inferInstance : IsLocalRing C) with
      is_henselian := fun f hf a₀ h₁ h₂ =>
        (IsAdicComplete.henselianRing C (maximalIdeal C)).is_henselian f hf a₀ h₁
          (h₂.map (Ideal.Quotient.mk _)) }
  obtain ⟨u, d, hu1, hgu, hdg, huniq⟩ := UpperTheory.V.AlgebraTools.henselDiag C (Fin 4) g hoff hdiff
  have hg' : adj g * g = ν • 1 := hg
  have mulL : ∀ X Y : M4 C, (∀ i j, X i j ∈ maximalIdeal C) →
      ∀ i j, (X * Y) i j ∈ maximalIdeal C := by
    intro X Y hX i j
    rw [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (hX i k)
  have mulR : ∀ X Y : M4 C, (∀ i j, Y i j ∈ maximalIdeal C) →
      ∀ i j, (X * Y) i j ∈ maximalIdeal C := by
    intro X Y hY i j
    rw [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (hY k j)
  have adjM : ∀ X : M4 C, (∀ i j, X i j ∈ maximalIdeal C) →
      ∀ i j, adj X i j ∈ maximalIdeal C := by
    intro X hX i j
    rw [adj_apply, zsmul_eq_mul]
    exact Ideal.mul_mem_left _ _ (hX _ _)
  have hW1 : ∀ i j, (adj u * u - 1) i j ∈ maximalIdeal C := by
    have e : adj u * u - 1 = adj (u - 1) * (u - 1) + adj (u - 1) + (u - 1) := by
      rw [adj_sub_one]
      noncomm_ring
    intro i j
    rw [e, Matrix.add_apply, Matrix.add_apply]
    exact Ideal.add_mem _ (Ideal.add_mem _ (mulL _ _ (adjM _ hu1) i j) (adjM _ hu1 i j)) (hu1 i j)
  have hWu : ∀ i, IsUnit ((adj u * u) i i) := fun i =>
    unit_of_sub isUnit_one (by
      have := hW1 i i
      rwa [Matrix.sub_apply, Matrix.one_apply_eq] at this)
  have hkey : ν • (adj u * u) = adj (Matrix.diagonal d) * (adj u * u) * Matrix.diagonal d := by
    have e1 : adj u * adj g = adj (Matrix.diagonal d) * adj u := by
      rw [← adj_mul', ← adj_mul', hgu]
    calc ν • (adj u * u) = adj u * (adj g * g) * u := by
          rw [hg']
          simp [Matrix.mul_smul, Matrix.smul_mul]
      _ = (adj u * adj g) * (g * u) := by simp only [Matrix.mul_assoc]
      _ = adj (Matrix.diagonal d) * adj u * (u * Matrix.diagonal d) := by rw [e1, hgu]
      _ = _ := by simp only [Matrix.mul_assoc]
  have hent : ∀ i j, ν * (adj u * u) i j = d i.rev * (adj u * u) i j * d j := by
    intro i j
    have := congrFun (congrFun hkey i) j
    rw [adj_diag'] at this
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_diagonal, Matrix.diagonal_mul] at this
    exact this
  have hdd : ∀ i, d i.rev * d i = ν := by
    intro i
    have h0 : (adj u * u) i i * (d i.rev * d i - ν) = 0 := by
      linear_combination (-1 : C) * hent i i
    exact sub_eq_zero.mp ((hWu i).mul_right_eq_zero.mp h0)
  have hdu : ∀ i, IsUnit (d i) := fun i => by
    have : IsUnit (d i.rev * d i) := by rw [hdd i]; exact hν
    exact isUnit_of_mul_isUnit_right this
  have hoffW : ∀ i j, i ≠ j → (adj u * u) i j = 0 := by
    intro i j hij
    have h0 : (adj u * u) i j * (d i.rev * d j - ν) = 0 := by
      linear_combination (-1 : C) * hent i j
    have hu : IsUnit (d i.rev * d j - ν) := by
      rw [← hdd i, ← mul_sub]
      refine (hdu _).mul ?_
      refine unit_of_sub (hdiff j i (Ne.symm hij)) ?_
      have := Ideal.sub_mem _ (hdg j) (hdg i)
      convert this using 1
      ring
    exact hu.mul_left_eq_zero.mp h0
  obtain ⟨w, hw⟩ : ∃ w : Fin 4 → C, ∀ i, w i = (adj u * u) i i := ⟨_, fun _ => rfl⟩
  have hWd : adj u * u = Matrix.diagonal w := by
    ext i j
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq, hw]
    · rw [hoffW i j hij, Matrix.diagonal_apply_ne _ hij]
  have hwu : ∀ i, IsUnit (w i) := fun i => by rw [hw]; exact hWu i
  have hwm : ∀ i, w i - 1 ∈ maximalIdeal C := fun i => by
    have := hW1 i i
    rwa [Matrix.sub_apply, Matrix.one_apply_eq, ← hw] at this
  have hwrev : ∀ i, w i.rev = w i := by
    have h : adj (adj u * u) = adj u * u := by rw [adj_mul', adj_adj']
    rw [hWd, adj_diag'] at h
    intro i
    have := congrFun (congrFun h i) i
    simpa using this
  have h21 : w 2 = w 1 := by simpa [Fin.rev] using hwrev 1
  have h30 : w 3 = w 0 := by simpa [Fin.rev] using hwrev 0
  obtain ⟨a, ha⟩ : ∃ a, a * w 1 = 1 := ⟨_, (hwu 1).val_inv_mul⟩
  obtain ⟨b, hb⟩ : ∃ b, b * w 0 = 1 := ⟨_, (hwu 0).val_inv_mul⟩
  have ha1 : a - 1 ∈ maximalIdeal C := by
    have e : a - 1 = -(a * (w 1 - 1)) := by linear_combination ha
    rw [e]
    exact Submodule.neg_mem _ (Ideal.mul_mem_left _ _ (hwm 1))
  have hb1 : b - 1 ∈ maximalIdeal C := by
    have e : b - 1 = -(b * (w 0 - 1)) := by linear_combination hb
    rw [e]
    exact Submodule.neg_mem _ (Ideal.mul_mem_left _ _ (hwm 0))
  obtain ⟨t, ht⟩ : ∃ t : Fin 4 → C, t = ![1, 1, a, b] := ⟨_, rfl⟩
  have htw : ∀ i, t i.rev * w i * t i = 1 := by
    intro i
    fin_cases i <;> simp [ht, Fin.rev, h21, h30] <;>
      first | linear_combination ha | linear_combination hb
  have htm : ∀ i, t i - 1 ∈ maximalIdeal C := by
    intro i
    fin_cases i <;> simp [ht] <;> first | exact ha1 | exact hb1
  refine ⟨u * Matrix.diagonal t, ?_, ?_, ?_, ?_⟩
  · show adj (u * Matrix.diagonal t) * (u * Matrix.diagonal t) = (1 : C) • (1 : M4 C)
    rw [adj_mul', adj_diag', one_smul]
    calc Matrix.diagonal (fun i => t i.rev) * adj u * (u * Matrix.diagonal t)
        = Matrix.diagonal (fun i => t i.rev) * (adj u * u) * Matrix.diagonal t := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [hWd, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
            ← Matrix.diagonal_one]
          congr 1
          funext i
          exact htw i
  · intro i j
    have e : u * Matrix.diagonal t - 1 = (u - 1) * Matrix.diagonal t + (Matrix.diagonal t - 1) := by
      noncomm_ring
    rw [e, Matrix.add_apply]
    refine Ideal.add_mem _ (mulL _ _ hu1 i j) ?_
    by_cases hij : i = j
    · subst hij
      rw [Matrix.sub_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
      exact htm i
    · rw [Matrix.sub_apply, Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij, sub_zero]
      exact Submodule.zero_mem _
  · have e : adj (u * Matrix.diagonal t) * g * (u * Matrix.diagonal t)
        = Matrix.diagonal (fun i => t i.rev) * (adj u * u) * Matrix.diagonal d * Matrix.diagonal t := by
      rw [adj_mul', adj_diag']
      calc Matrix.diagonal (fun i => t i.rev) * adj u * g * (u * Matrix.diagonal t)
          = Matrix.diagonal (fun i => t i.rev) * adj u * (g * u) * Matrix.diagonal t := by
            simp only [Matrix.mul_assoc]
        _ = _ := by
            rw [hgu]
            simp only [Matrix.mul_assoc]
    rw [e, hWd, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal]
    exact Matrix.isDiag_diagonal _
  · intro hB
    have hB' : ∀ i j, lamW i ≠ lamW j → g i j = 0 := hB
    obtain ⟨S, hS⟩ : ∃ S : M4 C, S = Matrix.diagonal (sg C) := ⟨_, rfl⟩
    have hSS : S * S = 1 := by
      rw [hS, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      exact sg_sq (R := C) i
    have hgS : g * S = S * g := by
      ext i j
      rw [hS, Matrix.mul_diagonal, Matrix.diagonal_mul]
      by_cases h : lamW i = lamW j
      · rw [sg_eq (R := C) i j h, mul_comm]
      · rw [hB' i j h]
        ring
    have hdS : Matrix.diagonal d * S = S * Matrix.diagonal d := by
      rw [hS, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      ring
    have h1 : ∀ i j, (S * u * S - 1) i j ∈ maximalIdeal C := by
      have e : S * u * S - 1 = S * (u - 1) * S := by
        rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hSS]
      intro i j
      rw [e]
      exact mulL _ _ (mulR _ _ hu1) i j
    have h2 : g * (S * u * S) = S * u * S * Matrix.diagonal d := by
      calc g * (S * u * S) = S * (g * u) * S := by
            rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hgS, Matrix.mul_assoc S g u]
        _ = S * u * (Matrix.diagonal d * S) := by
            rw [hgu]
            simp only [Matrix.mul_assoc]
        _ = S * u * S * Matrix.diagonal d := by
            rw [hdS]
            simp only [Matrix.mul_assoc]
    obtain ⟨-, t', ht'⟩ := huniq (S * u * S) d h1 h2
    have hent2 : ∀ i j, sg C i * u i j * sg C j = u i j * t' j := by
      intro i j
      have := congrFun (congrFun ht' i) j
      simp only [hS, Matrix.mul_diagonal, Matrix.diagonal_mul] at this
      exact this
    have ht'1 : ∀ j, t' j = 1 := by
      intro j
      have h := hent2 j j
      have hu : IsUnit (u j j) := unit_of_sub isUnit_one (by
        have := hu1 j j
        rwa [Matrix.sub_apply, Matrix.one_apply_eq] at this)
      have h0 : u j j * (t' j - 1) = 0 := by
        linear_combination (-1 : C) * h + u j j * sg_sq (R := C) j
      exact sub_eq_zero.mp (hu.mul_right_eq_zero.mp h0)
    have hBu : ∀ i j, lamW i ≠ lamW j → u i j = 0 := by
      intro i j hij
      have h := hent2 i j
      rw [ht'1 j, mul_one] at h
      have h' : (2 : C) * u i j = 0 := by
        linear_combination (-1 : C) * h + u i j * sg_ne (R := C) i j hij
      exact h2u.mul_right_eq_zero.mp h'
    intro i j hij
    rw [Matrix.mul_diagonal, hBu i j hij, zero_mul]
