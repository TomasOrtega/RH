import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.SwapOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkDedekind
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkBern
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.SwapOneAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkDdSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeEqDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.EqOneOfStrictMono
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkInd

open MvPolynomial Equiv UpperTheory.V.AlgebraTools.Hk

/- English proof (translation)
Take `⟨hA, -, h1, -⟩` from `UpperTheory.V.AlgebraTools.hkInv n`. Establish `hac : (1 : Perm (Fin n))⁻¹ a < (1 : Perm (Fin n))⁻¹ c`. Rewrite using `[inv_one, Perm.one_apply, Perm.one_apply, Fin.lt_def]`. Use linear arithmetic over natural numbers and integers. Use `(hA a c h 1 hac).2.2` as an intermediate fact.

Rewrite `this` using `[mul_one, invN.eq_def 1, h1, Finset.card_empty, zero_add]`. Rewrite using `[(UpperTheory.V.AlgebraTools.hkOne R n q H b).1, this, pow_one]`.
-/
private theorem simple_one {R : Type} [CommRing R] {n : ℕ} {q : R} {H : Type} [Ring H] [Algebra R H]
    (b : Bern n q H) {a c : Fin n} (h : a.val + 1 = c.val) : b.T (swap a c) * b.one = q • b.one := by
  obtain ⟨hA, -, h1, -⟩ := UpperTheory.V.AlgebraTools.hkInv n
  have hac : (1 : Perm (Fin n))⁻¹ a < (1 : Perm (Fin n))⁻¹ c := by
    rw [inv_one, Perm.one_apply, Perm.one_apply, Fin.lt_def]; omega
  have := (hA a c h 1 hac).2.2
  rw [mul_one, invN.eq_def 1, h1, Finset.card_empty, zero_add] at this
  rw [(UpperTheory.V.AlgebraTools.hkOne R n q H b).1, this, pow_one]

/- English proof (translation)
Establish `hs : ∀ a c : Fin n, a.val + 1 = c.val → rename (swap a c) y = y`. Introduce `a c h`. Establish `hac : a ≠ c` using `fun e => by rw [e] at h; omega`. Take `⟨z, hz, e⟩` from `(UpperTheory.V.AlgebraTools.hkBern R n q H b).1 a c h y`. Establish `e1` using `hy a c h`.

Rewrite `e1` using `[← mul_assoc, e, add_mul, mul_assoc, simple_one b h, mul_smul_comm, smul_mul_assoc]`. Establish `e2 : q • rename (swap a c) y + (q - 1) • (X a * z) - q • y = 0`. Apply `hb` to reduce the goal to its premises. Rewrite using `[map_sub, map_add, map_smul, map_smul, map_smul, sub_mul, add_mul, smul_mul_assoc, smul_mul_assoc, smul_mul_assoc, e1, sub_self]`. Establish `e3 : (C q * X c - X a) * z = 0`.

Simplify using `only [smul_eq_C_mul, map_sub, map_one] at e2`. Take the linear combination `e2 - C q * hz`. Break down `mul_eq_zero.1 e3 with h0 | h0` into its components or cases. Use `congrArg (eval fun k => if k = a then (1 : R) else 0) h0` as an intermediate fact. Simplify using `[hac.symm] at this`.

Rewrite `hz` using `[h0, mul_zero]`. Conclude with `(sub_eq_zero.1 hz.symm).symm`. Use `UpperTheory.V.AlgebraTools.hkInd n (fun w => rename w y = y) ?_ ?_ w` and prove the remaining obligations. Simplify using the standard rewrite rules. Introduce `a c h w _ ih`.

Rewrite using `[Perm.coe_mul, ← rename_rename, ih, hs a c h]`.
-/
private theorem symm_of_eigen {R : Type} [CommRing R] [IsDomain R] {n : ℕ} {q : R} {H : Type} [Ring H]
    [Algebra R H] (b : Bern n q H) (hb : b.Faithful) (y : MvPolynomial (Fin n) R)
    (hy : ∀ a c : Fin n, a.val + 1 = c.val → b.T (swap a c) * (b.th y * b.one) = q • (b.th y * b.one))
    (w : Perm (Fin n)) : rename w y = y := by
  have hs : ∀ a c : Fin n, a.val + 1 = c.val → rename (swap a c) y = y := by
    intro a c h
    have hac : a ≠ c := fun e => by rw [e] at h; omega
    obtain ⟨z, hz, e⟩ := (UpperTheory.V.AlgebraTools.hkBern R n q H b).1 a c h y
    have e1 := hy a c h
    rw [← mul_assoc, e, add_mul, mul_assoc, simple_one b h, mul_smul_comm, smul_mul_assoc] at e1
    have e2 : q • rename (swap a c) y + (q - 1) • (X a * z) - q • y = 0 := by
      apply hb
      rw [map_sub, map_add, map_smul, map_smul, map_smul, sub_mul, add_mul, smul_mul_assoc, smul_mul_assoc,
        smul_mul_assoc, e1, sub_self]
    have e3 : (C q * X c - X a) * z = 0 := by
      simp only [smul_eq_C_mul, map_sub, map_one] at e2
      linear_combination e2 - C q * hz
    rcases mul_eq_zero.1 e3 with h0 | h0
    · have := congrArg (eval fun k => if k = a then (1 : R) else 0) h0
      simp [hac.symm] at this
    · rw [h0, mul_zero] at hz
      exact (sub_eq_zero.1 hz.symm).symm
  refine UpperTheory.V.AlgebraTools.hkInd n (fun w => rename w y = y) ?_ ?_ w
  · simp
  · intro a c h w _ ih
    rw [Perm.coe_mul, ← rename_rename, ih, hs a c h]

/- English proof (translation)
Rewrite using `[NN, map_prod]`. Use `Finset.prod_nbij' (fun p => (p.2.rev, p.1.rev)) (fun p => (p.2.rev, p.1.rev)) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `p hp`. Simplify `hp` using `[pairs]`. Introduce `p hp`.

Simplify `hp` using `[pairs]`. Introduce `p _`. Simplify using the standard rewrite rules. Introduce `p _`. Simplify using the standard rewrite rules.

Introduce `p _`. Simplify using the standard rewrite rules.
-/
private theorem rename_rev_NN {R : Type} [CommRing R] (n : ℕ) (q : R) :
    rename (Fin.revPerm : Perm (Fin n)) (NN n q) = ∏ p ∈ pairs n, (X p.1 - C q * X p.2) := by
  rw [NN, map_prod]
  refine Finset.prod_nbij' (fun p => (p.2.rev, p.1.rev)) (fun p => (p.2.rev, p.1.rev)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simpa [pairs] using hp
  · intro p hp
    simpa [pairs] using hp
  · intro p _
    simp
  · intro p _
    simp
  · intro p _
    simp

/- English proof (translation)
Simplify `rename_rev_NN n (1 : R)` using `[NN, De]`.
-/
private theorem rename_rev_De (R : Type) [CommRing R] (n : ℕ) :
    rename (Fin.revPerm : Perm (Fin n)) (De R n) = ∏ p ∈ pairs n, (X p.1 - X p.2) := by
  simpa [NN, De] using rename_rev_NN n (1 : R)

/- English proof (translation)
Take `⟨σ, rfl⟩ : ∃ σ, v = σ * r` from `⟨v * r⁻¹, by simp⟩`. Set `φ : K ≃+* K` to `IsFractionRing.ringEquivOfRingEquiv (renameEquiv R σ).toRingEquiv`. Establish `hφ : ∀ x : MvPolynomial (Fin n) R, φ (algebraMap _ K x) = algebraMap _ K (rename σ x)` using `fun x => IsFractionRing.ringEquivOfRingEquiv_algebraMap _ x`. Establish `h0` using `UpperTheory.V.AlgebraTools.hkDedekind R n K (fun u => F u - φ (F (σ⁻¹ * u))) (by`. Introduce `x`.

Take `⟨y, hy, e⟩` from `hF x`. Establish `e'` using `congrArg φ e`. Rewrite `e'` using `[hφ, hy, e, map_sum]`. Simplify using `only [sub_mul, Finset.sum_sub_distrib]`. Rewrite using `[e', sub_eq_zero]`.

Use `Fintype.sum_equiv (Equiv.mulLeft σ) _ _ fun u => ?_` and prove the remaining obligations. Rewrite using `[map_mul, hφ, rename_rename, Equiv.coe_mulLeft, inv_mul_cancel_left, Perm.coe_mul])`. Establish `h1` using `congrFun h0 (σ * r)`. Simplify using `only [Pi.zero_apply, inv_mul_cancel_left, sub_eq_zero] at h1`. Rewrite using `[h1, hr, map_div₀, hφ, hφ, rename_rename, rename_rename, Perm.coe_mul]`.
-/
private theorem coeff_eq {R : Type} [CommRing R] [IsDomain R] {n : ℕ} {K : Type} [Field K]
    [Algebra (MvPolynomial (Fin n) R) K] [IsFractionRing (MvPolynomial (Fin n) R) K] (F : Perm (Fin n) → K)
    (hF : ∀ x : MvPolynomial (Fin n) R, ∃ y : MvPolynomial (Fin n) R, (∀ w : Perm (Fin n), rename w y = y) ∧
      algebraMap _ K y = ∑ u, F u * algebraMap _ K (rename u x))
    (N D : MvPolynomial (Fin n) R) (r : Perm (Fin n))
    (hr : F r = algebraMap _ K (rename r N) / algebraMap _ K (rename r D)) (v : Perm (Fin n)) :
    F v = algebraMap _ K (rename v N) / algebraMap _ K (rename v D) := by
  obtain ⟨σ, rfl⟩ : ∃ σ, v = σ * r := ⟨v * r⁻¹, by simp⟩
  let φ : K ≃+* K := IsFractionRing.ringEquivOfRingEquiv (renameEquiv R σ).toRingEquiv
  have hφ : ∀ x : MvPolynomial (Fin n) R, φ (algebraMap _ K x) = algebraMap _ K (rename σ x) := fun x =>
    IsFractionRing.ringEquivOfRingEquiv_algebraMap _ x
  have h0 := UpperTheory.V.AlgebraTools.hkDedekind R n K (fun u => F u - φ (F (σ⁻¹ * u))) (by
    intro x
    obtain ⟨y, hy, e⟩ := hF x
    have e' := congrArg φ e
    rw [hφ, hy, e, map_sum] at e'
    simp only [sub_mul, Finset.sum_sub_distrib]
    rw [e', sub_eq_zero]
    refine Fintype.sum_equiv (Equiv.mulLeft σ) _ _ fun u => ?_
    rw [map_mul, hφ, rename_rename, Equiv.coe_mulLeft, inv_mul_cancel_left, Perm.coe_mul])
  have h1 := congrFun h0 (σ * r)
  simp only [Pi.zero_apply, inv_mul_cancel_left, sub_eq_zero] at h1
  rw [h1, hr, map_div₀, hφ, hφ, rename_rename, rename_rename, Perm.coe_mul]

/- English proof (translation)
Introduce `R _ _ n q H _ _ b hb x`. Set `K` to `FractionRing (MvPolynomial (Fin n) R)`. Use `choose f hf hfw hf0 using UpperTheory.V.AlgebraTools.hkAct R n q H b K`. Take `⟨-, -, -, hrev, hlt⟩` from `UpperTheory.V.AlgebraTools.hkInv n`. Take `⟨hD, hsg, -⟩` from `UpperTheory.V.AlgebraTools.hkDe R n`.

Establish `hsum : ∀ x : MvPolynomial (Fin n) R, ∃ y : MvPolynomial (Fin n) R, b.one * b.th x * b.one = b.th y * b.one ∧ algebraMap _ K y = ∑ u, (∑ w, f w u) * algebraMap _ K (rename u x)`. Introduce `x`. Use `choose y hy hy' using fun w => hf w x`. Use `⟨∑ w, y w, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_sum, Finset.sum_mul, ← Finset.sum_congr rfl fun w _ => hy w, ← Finset.sum_mul, ← Finset.sum_mul]`.

Both sides reduce to the same expression. Simplify using `only [map_sum, hy', Finset.sum_mul]`. Conclude with `Finset.sum_comm`. Establish `hF` using `coeff_eq (K := K) (fun u => ∑ w, f w u) (by`. Introduce `x`.

Take `⟨y, hy, e⟩` from `hsum x`. Use `⟨y, symm_of_eigen b hb y fun a c h => ?_, e⟩` and prove the remaining obligations. Rewrite using `[← hy, ← mul_assoc, ← mul_assoc, simple_one b h, smul_mul_assoc, smul_mul_assoc])`. Use the proof step `(NN n q) (De R n) Fin.revPerm (by`. Rewrite using `[Finset.sum_eq_single Fin.revPerm (fun w _ hw => hf0 w _ hw.symm (hlt w hw).le) (by simp), hfw, hrev, rename_rev_NN, rename_rev_De, map_prod, map_prod, Finset.prod_div_distrib])`.

Take `⟨y, hy, e⟩` from `hsum x`. Establish `hinj` using `IsFractionRing.injective (MvPolynomial (Fin n) R) K`. Establish `hD' : algebraMap _ K (De R n) ≠ 0` using `fun h => hD (hinj (by rw [h, map_zero]))`. Establish `: y = dd (NN n q * x)`. Apply `mul_left_cancel₀ hD` to reduce the goal to its premises.

Apply `hinj` to reduce the goal to its premises. Rewrite using `[UpperTheory.V.AlgebraTools.hkDdSpec, map_mul, e, alt, map_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun u _ => ?_` and prove the remaining obligations. Establish `hu` using `hF u`. Rewrite using `[hu, hsg, map_mul]`.

Break down `Int.units_eq_one_or (Perm.sign u) with h | h` into its components or cases. Rewrite using `[h, one_smul, one_smul, map_mul, ← mul_assoc, mul_div_cancel₀ _ hD']`. Rewrite using `[h, Units.neg_smul, Units.neg_smul, one_smul, one_smul, map_neg, map_neg, map_mul, div_neg, neg_mul, mul_neg, ← mul_assoc, mul_div_cancel₀ _ hD']`. Rewrite using `[hy, this]`.
-/
theorem UpperTheory.V.AlgebraTools.hkSandwich :
    ∀ (R : Type) [CommRing R] [IsDomain R] (n : ℕ) (q : R) (H : Type) [Ring H] [Algebra R H] (b : Bern n q H), b.Faithful → ∀ x : MvPolynomial (Fin n) R, b.one * b.th x * b.one = b.th (dd (NN n q * x)) * b.one := by
  intro R _ _ n q H _ _ b hb x
  let K := FractionRing (MvPolynomial (Fin n) R)
  choose f hf hfw hf0 using UpperTheory.V.AlgebraTools.hkAct R n q H b K
  obtain ⟨-, -, -, hrev, hlt⟩ := UpperTheory.V.AlgebraTools.hkInv n
  obtain ⟨hD, hsg, -⟩ := UpperTheory.V.AlgebraTools.hkDe R n
  have hsum : ∀ x : MvPolynomial (Fin n) R, ∃ y : MvPolynomial (Fin n) R,
      b.one * b.th x * b.one = b.th y * b.one ∧
      algebraMap _ K y = ∑ u, (∑ w, f w u) * algebraMap _ K (rename u x) := by
    intro x
    choose y hy hy' using fun w => hf w x
    refine ⟨∑ w, y w, ?_, ?_⟩
    · rw [map_sum, Finset.sum_mul, ← Finset.sum_congr rfl fun w _ => hy w, ← Finset.sum_mul, ← Finset.sum_mul]
      rfl
    · simp only [map_sum, hy', Finset.sum_mul]
      exact Finset.sum_comm
  have hF := coeff_eq (K := K) (fun u => ∑ w, f w u) (by
    intro x
    obtain ⟨y, hy, e⟩ := hsum x
    refine ⟨y, symm_of_eigen b hb y fun a c h => ?_, e⟩
    rw [← hy, ← mul_assoc, ← mul_assoc, simple_one b h, smul_mul_assoc, smul_mul_assoc])
    (NN n q) (De R n) Fin.revPerm (by
    rw [Finset.sum_eq_single Fin.revPerm (fun w _ hw => hf0 w _ hw.symm (hlt w hw).le) (by simp), hfw, hrev,
      rename_rev_NN, rename_rev_De, map_prod, map_prod, Finset.prod_div_distrib])
  obtain ⟨y, hy, e⟩ := hsum x
  have hinj := IsFractionRing.injective (MvPolynomial (Fin n) R) K
  have hD' : algebraMap _ K (De R n) ≠ 0 := fun h => hD (hinj (by rw [h, map_zero]))
  have : y = dd (NN n q * x) := by
    apply mul_left_cancel₀ hD
    apply hinj
    rw [UpperTheory.V.AlgebraTools.hkDdSpec, map_mul, e, alt, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    have hu := hF u
    rw [hu, hsg, map_mul]
    rcases Int.units_eq_one_or (Perm.sign u) with h | h
    · rw [h, one_smul, one_smul, map_mul, ← mul_assoc, mul_div_cancel₀ _ hD']
    · rw [h, Units.neg_smul, Units.neg_smul, one_smul, one_smul, map_neg, map_neg, map_mul, div_neg, neg_mul,
        mul_neg, ← mul_assoc, mul_div_cancel₀ _ hD']
  rw [hy, this]
