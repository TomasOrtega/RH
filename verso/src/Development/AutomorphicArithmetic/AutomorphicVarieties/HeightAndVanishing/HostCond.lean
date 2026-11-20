import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.LayerLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.HostLevel
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.LevChange
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.LevGal
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsOnto

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

/- English proof (translation)
Simplify using `[ZMod.unitsMap, ZMod.coe_unitOfCoprime, ZMod.castHom_apply, ZMod.cast_natCast hd]`.
-/
private theorem unitsMap_unitOfCoprime_coe_eq {n m : ℕ} (hd : m ∣ n) (c : ℕ) (hc : c.Coprime n) :
    ((ZMod.unitsMap hd (ZMod.unitOfCoprime c hc) : (ZMod m)ˣ) : ZMod m) = c := by
  simp [ZMod.unitsMap, ZMod.coe_unitOfCoprime, ZMod.castHom_apply, ZMod.cast_natCast hd]

/- English proof (translation)
Use `set P := ordProj[p] N with hPdef`. Use `set K := ordCompl[p] N with hKdef`. Establish `hPK : P * K = N` using `Nat.ordProj_mul_ordCompl_eq_self N p`. Establish `hPpos : 0 < P` using `pow_pos hp.pos _`. Establish `hcop : P.Coprime K` using `(Nat.coprime_ordCompl hp hN).pow_left _`.

Establish `hpP : p ∣ P` using `dvd_pow_self p (hp.factorization_pos_of_dvd hN hpN).ne'`. Take `⟨c, hcP, hcK⟩` from `Nat.chineseRemainder hcop w 1`. Establish `hRP : R = P * (R / P)` using `(Nat.mul_div_cancel' hPR).symm`. Establish `hRPK : R / P ∣ K`. Establish `: P * (R / P) ∣ P * K` using `by rw [← hRP, hPK]; exact hR`.

Conclude with `Nat.dvd_of_mul_dvd_mul_left hPpos this`. Establish `hRPp : R / P ∣ R / p`. Apply `Nat.dvd_div_of_mul_dvd` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Use `⟨c, ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hRP]`. Use `(Nat.modEq_and_modEq_iff_modEq_mul (hcop.coprime_dvd_right hRPK)).1 ⟨hcP, ?_⟩` and prove the remaining obligations. Conclude with `((hcK.of_dvd hRPK).trans (hw.of_dvd hRPp).symm)`. Establish `hNp : N / p = (P / p) * K`. Rewrite using `[Nat.div_mul_right_comm hpP, hPK]`.

Establish `hPpK : (P / p).Coprime K` using `hcop.coprime_dvd_left (Nat.div_dvd_of_dvd hpP)`. Rewrite using `[hNp]`. Use `(Nat.modEq_and_modEq_iff_modEq_mul hPpK).1 ⟨?_, hcK⟩` and prove the remaining obligations. Establish `h1 : P / p ∣ P` using `Nat.div_dvd_of_dvd hpP`. Establish `h2 : P / p ∣ R / p` using `Nat.div_dvd_div hpP hPR`.

Conclude with `(hcP.of_dvd h1).trans (hw.of_dvd h2)`. Rewrite using `[← hPK]`. Use `Nat.Coprime.mul_right ?_ ?_` and prove the remaining obligations. Establish `: c.gcd P = w.gcd P` using `hcP.gcd_eq`. Rewrite using `[Nat.Coprime, this]`.

Conclude with `Nat.Coprime.pow_right _ hwp`. Establish `: c.gcd K = (1 : ℕ).gcd K` using `hcK.gcd_eq`. Rewrite using `[Nat.Coprime, this, Nat.gcd_one_left]`.
-/
private theorem exists_coprime_modEq_of_modEq_one_div {N p R w : ℕ} (hp : p.Prime) (hN : N ≠ 0) (hpN : p ∣ N)
    (hR : R ∣ N) (hPR : ordProj[p] N ∣ R) (hw : w ≡ 1 [MOD R / p]) (hwp : w.Coprime p) :
    ∃ c, c ≡ w [MOD R] ∧ c ≡ 1 [MOD N / p] ∧ c.Coprime N := by
  set P := ordProj[p] N with hPdef
  set K := ordCompl[p] N with hKdef
  have hPK : P * K = N := Nat.ordProj_mul_ordCompl_eq_self N p
  have hPpos : 0 < P := pow_pos hp.pos _
  have hcop : P.Coprime K := (Nat.coprime_ordCompl hp hN).pow_left _
  have hpP : p ∣ P := dvd_pow_self p (hp.factorization_pos_of_dvd hN hpN).ne'
  obtain ⟨c, hcP, hcK⟩ := Nat.chineseRemainder hcop w 1
  have hRP : R = P * (R / P) := (Nat.mul_div_cancel' hPR).symm
  have hRPK : R / P ∣ K := by
    have : P * (R / P) ∣ P * K := by rw [← hRP, hPK]; exact hR
    exact Nat.dvd_of_mul_dvd_mul_left hPpos this
  have hRPp : R / P ∣ R / p := by
    apply Nat.dvd_div_of_mul_dvd
    calc p * (R / P) ∣ P * (R / P) := mul_dvd_mul_right hpP _
      _ = R := hRP.symm
  refine ⟨c, ?_, ?_, ?_⟩
  · rw [hRP]
    refine (Nat.modEq_and_modEq_iff_modEq_mul (hcop.coprime_dvd_right hRPK)).1 ⟨hcP, ?_⟩
    exact ((hcK.of_dvd hRPK).trans (hw.of_dvd hRPp).symm)
  · have hNp : N / p = (P / p) * K := by
      rw [Nat.div_mul_right_comm hpP, hPK]
    have hPpK : (P / p).Coprime K := hcop.coprime_dvd_left (Nat.div_dvd_of_dvd hpP)
    rw [hNp]
    refine (Nat.modEq_and_modEq_iff_modEq_mul hPpK).1 ⟨?_, hcK⟩
    have h1 : P / p ∣ P := Nat.div_dvd_of_dvd hpP
    have h2 : P / p ∣ R / p := Nat.div_dvd_div hpP hPR
    exact (hcP.of_dvd h1).trans (hw.of_dvd h2)
  · rw [← hPK]
    refine Nat.Coprime.mul_right ?_ ?_
    · have : c.gcd P = w.gcd P := hcP.gcd_eq
      rw [Nat.Coprime, this]
      exact Nat.Coprime.pow_right _ hwp
    · have : c.gcd K = (1 : ℕ).gcd K := hcK.gcd_eq
      rw [Nat.Coprime, this, Nat.gcd_one_left]
/- English proof (translation)
Use `haveI : IsAlgClosure ℚ (AlgebraicClosure ℚ) := by`. Use `AlgebraicClosure.instIsAlgClosure ℚ` and compare the differences between its conclusion and the goal. Apply the tactic sequence `all_goals first | rfl | exact Subsingleton.elim _ _`. Set `f : E →ₐ[ℚ] AlgebraicClosure ℚ` to `IsAlgClosed.lift`. Use `letI : Algebra E (AlgebraicClosure ℚ) := f.toRingHom.toAlgebra`.

Establish `e1` using `((Chr.levGal E L H₁ h₁).2.2 (AlgebraicClosure ℚ)).1`. Establish `e2` using `((Chr.levGal E L H₂ h₂).2.2 (AlgebraicClosure ℚ)).1`. Establish `e3 : Chr.levH ℚ (AlgebraicClosure ℚ) H₁ = Chr.levH ℚ (AlgebraicClosure ℚ) H₂` using `e1.symm.trans e2`. Conclude with `Subgroup.comap_injective (Chr.clsOnto (AlgebraicClosure ℚ) L).1 e3`.
-/
private theorem subgroup_eq_of_chr_hasLevel (E : Type) [Field E] [NumberField E] (L : ℕ) [NeZero L]
    (H₁ H₂ : Subgroup (ZMod L)ˣ) (h₁ : Chr.HasLevel E L H₁) (h₂ : Chr.HasLevel E L H₂) :
    H₁ = H₂ := by
  haveI : IsAlgClosure ℚ (AlgebraicClosure ℚ) := by
    convert AlgebraicClosure.instIsAlgClosure ℚ
    all_goals first | rfl | exact Subsingleton.elim _ _
  let f : E →ₐ[ℚ] AlgebraicClosure ℚ := IsAlgClosed.lift
  letI : Algebra E (AlgebraicClosure ℚ) := f.toRingHom.toAlgebra
  have e1 := ((Chr.levGal E L H₁ h₁).2.2 (AlgebraicClosure ℚ)).1
  have e2 := ((Chr.levGal E L H₂ h₂).2.2 (AlgebraicClosure ℚ)).1
  have e3 : Chr.levH ℚ (AlgebraicClosure ℚ) H₁ = Chr.levH ℚ (AlgebraicClosure ℚ) H₂ :=
    e1.symm.trans e2
  exact Subgroup.comap_injective (Chr.clsOnto (AlgebraicClosure ℚ) L).1 e3

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Establish `hd : Q / p ∣ Q` using `Nat.div_dvd_of_dvd hpQ`. Establish `hft : χ.FactorsThrough (Q / p)`. Rewrite using `[DirichletCharacter.factorsThrough_iff_ker_unitsMap hd]`.

Introduce `u hu`. Rewrite `hu`, the goal using `[MonoidHom.mem_ker]`. Establish `hu' : ((ZMod.unitsMap hd u : (ZMod (Q / p))ˣ) : ZMod (Q / p)) = 1` using `by simp [hu]`. Establish `hval : (((u : ZMod Q).val : ℕ) : ZMod (Q / p)) = ((1 : ℕ) : ZMod (Q / p))`. Rewrite using `[Nat.cast_one, ← hu']`.

Use `show _ = ZMod.cast (u : ZMod Q)`. Rewrite using `[ZMod.cast_eq_val]`. Establish `hmod : (u : ZMod Q).val ≡ 1 [MOD Q / p]` using `(ZMod.natCast_eq_natCast_iff _ _ _).1 hval`. Establish `h1` using `hcon _ (ZMod.val_coe_unit_coprime u) hmod`. Rewrite `h1` using `[ZMod.natCast_zmod_val]`.

Use `ext`. Simplify using `[MulChar.coe_toUnitHom, h1]`. Establish `hle : χ.conductor ≤ Q / p` using `Nat.sInf_le ((DirichletCharacter.mem_conductorSet_iff χ).mpr hft)`. Rewrite `hle` using `[(DirichletCharacter.isPrimitive_def χ).1 hχ]`. Establish `hlt : Q / p < Q` using `Nat.div_lt_self (Nat.pos_of_ne_zero (NeZero.ne Q)) hp.one_lt`.

Use linear arithmetic over natural numbers and integers.
-/
private theorem exists_coprime_modEq_one_chi_ne_one_of_primitive {Q p : ℕ} [NeZero Q] (χ : DirichletCharacter ℂ Q)
    (hχ : χ.IsPrimitive) (hp : p.Prime) (hpQ : p ∣ Q) :
    ∃ w : ℕ, w.Coprime Q ∧ w ≡ 1 [MOD Q / p] ∧ χ (w : ZMod Q) ≠ 1 := by
  by_contra hcon
  push_neg at hcon
  have hd : Q / p ∣ Q := Nat.div_dvd_of_dvd hpQ
  have hft : χ.FactorsThrough (Q / p) := by
    rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hd]
    intro u hu
    rw [MonoidHom.mem_ker] at hu ⊢
    have hu' : ((ZMod.unitsMap hd u : (ZMod (Q / p))ˣ) : ZMod (Q / p)) = 1 := by simp [hu]
    have hval : (((u : ZMod Q).val : ℕ) : ZMod (Q / p)) = ((1 : ℕ) : ZMod (Q / p)) := by
      rw [Nat.cast_one, ← hu']
      show _ = ZMod.cast (u : ZMod Q)
      rw [ZMod.cast_eq_val]
    have hmod : (u : ZMod Q).val ≡ 1 [MOD Q / p] := (ZMod.natCast_eq_natCast_iff _ _ _).1 hval
    have h1 := hcon _ (ZMod.val_coe_unit_coprime u) hmod
    rw [ZMod.natCast_zmod_val] at h1
    ext
    simp [MulChar.coe_toUnitHom, h1]
  have hle : χ.conductor ≤ Q / p :=
    Nat.sInf_le ((DirichletCharacter.mem_conductorSet_iff χ).mpr hft)
  rw [(DirichletCharacter.isPrimitive_def χ).1 hχ] at hle
  have hlt : Q / p < Q := Nat.div_lt_self (Nat.pos_of_ne_zero (NeZero.ne Q)) hp.one_lt
  omega
/- English proof (translation)
Take `⟨hq1, hq18, hdp, hd16, -⟩` from `h.pair`. Introduce `hmem`. Simplify using `only [Host.H, Subgroup.mem_inf, Subgroup.mem_comap] at hmem`. Take `⟨⟨⟨h2, hχ⟩, hsq1⟩, hsqd⟩` from `hmem`. Break down `hcond with ⟨hne1, hne2⟩ | hχc | hc1 | hcd` into its components or cases.

Take `⟨k, hk⟩` from `Subgroup.mem_zpowers_iff.1 h2`. Establish `hv` using `congrArg Units.val hk`. Rewrite `hv` using `[unitsMap_unitOfCoprime_coe_eq]`. Break down `Int.even_or_odd k with he | ho` into its components or cases. Rewrite `hv` using `[he.neg_one_zpow]`.

Conclude with `hne1 (by simpa using hv.symm)`. Rewrite `hv` using `[ho.neg_one_zpow]`. Conclude with `hne2 (by simpa using hv.symm)`. Rewrite `hχ` using `[MonoidHom.mem_ker]`. Establish `hv` using `congrArg Units.val hχ`.

Rewrite `hv` using `[MulChar.coe_toUnitHom, unitsMap_unitOfCoprime_coe_eq]`. Conclude with `hχc (by simpa using hv)`. Take `⟨y, hy⟩` from `hsq1`. Establish `hv` using `congrArg Units.val hy`. Rewrite `hv` using `[unitsMap_unitOfCoprime_coe_eq, hc1]`.

Use `haveI := Fact.mk hq1`. Establish `hs : IsSquare (-1 : ZMod h.q1)` using `⟨(y : ZMod h.q1), by rw [← hv]; simp [sq]⟩`. Conclude with `(ZMod.exists_sq_eq_neg_one_iff.1 hs) (by omega)`. Take `⟨y, hy⟩` from `hsqd`. Establish `hv` using `congrArg Units.val hy`.

Rewrite `hv` using `[unitsMap_unitOfCoprime_coe_eq, hcd]`. Use `haveI := Fact.mk hdp`. Establish `hs : IsSquare (-1 : ZMod h.d)` using `⟨(y : ZMod h.d), by rw [← hv]; simp [sq]⟩`. Conclude with `(ZMod.exists_sq_eq_neg_one_iff.1 hs) (by omega)`.
-/
private theorem unitOfCoprime_not_mem_host_H_of_cond (h : Host) (c : ℕ) (hc : c.Coprime h.N)
    (hcond : ((c : ZMod (2 ^ (h.ex + 2))) ≠ 1 ∧ (c : ZMod (2 ^ (h.ex + 2))) ≠ -1) ∨
      h.chi.χ (c : ZMod h.chi.N) ≠ 1 ∨ (c : ZMod h.q1) = -1 ∨ (c : ZMod h.d) = -1) :
    ZMod.unitOfCoprime c hc ∉ h.H := by
  obtain ⟨hq1, hq18, hdp, hd16, -⟩ := h.pair
  intro hmem
  simp only [Host.H, Subgroup.mem_inf, Subgroup.mem_comap] at hmem
  obtain ⟨⟨⟨h2, hχ⟩, hsq1⟩, hsqd⟩ := hmem
  rcases hcond with ⟨hne1, hne2⟩ | hχc | hc1 | hcd
  · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h2
    have hv := congrArg Units.val hk
    rw [unitsMap_unitOfCoprime_coe_eq] at hv
    rcases Int.even_or_odd k with he | ho
    · rw [he.neg_one_zpow] at hv
      exact hne1 (by simpa using hv.symm)
    · rw [ho.neg_one_zpow] at hv
      exact hne2 (by simpa using hv.symm)
  · rw [MonoidHom.mem_ker] at hχ
    have hv := congrArg Units.val hχ
    rw [MulChar.coe_toUnitHom, unitsMap_unitOfCoprime_coe_eq] at hv
    exact hχc (by simpa using hv)
  · obtain ⟨y, hy⟩ := hsq1
    have hv := congrArg Units.val hy
    rw [unitsMap_unitOfCoprime_coe_eq, hc1] at hv
    haveI := Fact.mk hq1
    have hs : IsSquare (-1 : ZMod h.q1) := ⟨(y : ZMod h.q1), by rw [← hv]; simp [sq]⟩
    exact (ZMod.exists_sq_eq_neg_one_iff.1 hs) (by omega)
  · obtain ⟨y, hy⟩ := hsqd
    have hv := congrArg Units.val hy
    rw [unitsMap_unitOfCoprime_coe_eq, hcd] at hv
    haveI := Fact.mk hdp
    have hs : IsSquare (-1 : ZMod h.d) := ⟨(y : ZMod h.d), by rw [← hv]; simp [sq]⟩
    exact (ZMod.exists_sq_eq_neg_one_iff.1 hs) (by omega)
/- English proof (translation)
Take `⟨hq1, hq18, hdp, hd16, hcop⟩` from `h.pair`. Establish `hNdef : h.N = (2 ^ (h.ex + 2)).lcm h.q * (h.q1 * h.d)` using `rfl`. Establish `hN0 : h.N ≠ 0` using `(Host.N_pos h).ne'`. Use `haveI := h.chi.ne`. Establish `hq0 : h.q ≠ 0` using `NeZero.ne h.chi.N`.

Establish `hq10 : h.q1 ≠ 0` using `hq1.ne_zero`. Establish `hd0 : h.d ≠ 0` using `hdp.ne_zero`. Establish `h20 : 2 ^ (h.ex + 2) ≠ 0` using `by positivity`. Establish `hA0 : (2 ^ (h.ex + 2)).lcm h.q ≠ 0` using `Nat.lcm_ne_zero h20 hq0`. Establish `he2` using `h.two_le`.

It suffices to establish `key : ∃ R w : ℕ, R ∣ h.N ∧ ordProj[p] h.N ∣ R ∧ w ≡ 1 [MOD R / p] ∧ w.Coprime p ∧ ∀ c, c ≡ w [MOD R] → ((c : ZMod (2 ^ (h.ex + 2))) ≠ 1 ∧ (c : ZMod (2 ^ (h.ex + 2))) ≠ -1) ∨ h.chi.χ (c : ZMod h.chi.N) ≠ 1 ∨ (c : ZMod h.q1) = -1 ∨ (c : ZMod h.d) = -1 by`. Take `⟨R, w, hR, hPR, hw, hwp, hgood⟩` from `key`. Take `⟨c, hcR, hc1, hcN⟩` from `exists_coprime_modEq_of_modEq_one_div hp hN0 hpN hR hPR hw hwp`. Conclude with `⟨c, hcN, hc1, unitOfCoprime_not_mem_host_H_of_cond h c hcN (hgood c hcR)⟩`. Establish `hAN : (2 ^ (h.ex + 2)).lcm h.q ∣ h.N` using `by rw [hNdef]; exact dvd_mul_right _ _`.

Establish `hqN : h.q ∣ h.N` using `(Nat.dvd_lcm_right _ _).trans hAN`. Establish `h2N : 2 ^ (h.ex + 2) ∣ h.N` using `(Nat.dvd_lcm_left _ _).trans hAN`. Establish `hq1N : h.q1 ∣ h.N` using `by rw [hNdef]; exact (dvd_mul_right _ _).trans (dvd_mul_left _ _)`. Establish `hdN : h.d ∣ h.N` using `by rw [hNdef]; exact (dvd_mul_left _ _).trans (dvd_mul_left _ _)`. Establish `hv : ∀ r, h.N.factorization r = max ((2 ^ (h.ex + 2)).factorization r) (h.q.factorization r) + h.q1.factorization r + h.d.factorization r`.

Introduce `r`. Rewrite using `[hNdef, Nat.factorization_mul hA0 (mul_ne_zero hq10 hd0), Nat.factorization_mul hq10 hd0, Nat.factorization_lcm h20 hq0]`. Simplify using `[add_assoc]`. Establish `hodd : ∀ r, r.Prime → r ≠ 2 → ¬ r ∣ 2 ^ (h.ex + 2)`. Introduce `r hr hr2 hdv`.

Conclude with `hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow hdv))`. Establish `hq1q : ¬ h.q1 ∣ h.q`. Introduce `hdv`. Establish `: Nat.Coprime h.q1 h.chi.N` using `hcop.coprime_dvd_left (dvd_mul_right _ _)`. Conclude with `hq1.one_lt.ne' (Nat.Coprime.eq_one_of_dvd this hdv)`.

Establish `hdq : ¬ h.d ∣ h.q`. Introduce `hdv`. Establish `: Nat.Coprime h.d h.chi.N` using `hcop.coprime_dvd_left (dvd_mul_left _ _)`. Conclude with `hdp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd this hdv)`. Establish `hq1d : h.q1 ≠ h.d` using `by omega`.

Establish `hone : ∀ r, r.Prime → r % 4 = 3 → ¬ r ∣ h.q → (r = h.q1 ∨ r = h.d) → ∃ R w : ℕ, R ∣ h.N ∧ ordProj[r] h.N ∣ R ∧ w ≡ 1 [MOD R / r] ∧ w.Coprime r ∧ ∀ c, c ≡ w [MOD R] → (c : ZMod r) = -1`. Introduce `r hr hr4 hrq hrr`. Establish `hr2 : r ≠ 2` using `by omega`. Establish `hvr : h.N.factorization r = 1`. Rewrite using `[hv r, Nat.factorization_eq_zero_of_not_dvd (hodd r hr hr2), Nat.factorization_eq_zero_of_not_dvd hrq]`.

Break down `hrr with rfl | rfl` into its components or cases. Rewrite using `[hr.factorization_self, Nat.factorization_eq_zero_of_not_dvd]`. Simplify using the standard rewrite rules. Introduce `hdv`. Conclude with `hq1d ((Nat.prime_dvd_prime_iff_eq hr hdp).1 hdv)`.

Rewrite using `[hr.factorization_self, Nat.factorization_eq_zero_of_not_dvd]`. Simplify using the standard rewrite rules. Introduce `hdv`. Conclude with `hq1d ((Nat.prime_dvd_prime_iff_eq hr hq1).1 hdv).symm`. Use `⟨r, r - 1, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Break down `hrr with rfl | rfl` into its components or cases. Conclude with `hq1N`. Conclude with `hdN`. Rewrite using `[hvr, pow_one]`. Rewrite using `[Nat.div_self hr.pos]`.

Conclude with `Nat.modEq_one`. Use `(hr.coprime_iff_not_dvd.2 ?_).symm` and prove the remaining obligations. Conclude with `Nat.not_dvd_of_pos_of_lt (by omega) (by omega)`. Introduce `c hc`. Rewrite using `[(ZMod.natCast_eq_natCast_iff c (r - 1) r).2 hc, Nat.cast_sub hr.one_le, Nat.cast_one, ZMod.natCast_self, zero_sub]`.

Distinguish the cases in `hpq1 : p = h.q1`. Substitute `hpq1` using the available equality. Take `⟨R, w, a1, a2, a3, a4, a5⟩` from `hone h.q1 hq1 (by omega) hq1q (Or.inl rfl)`. Conclude with `⟨R, w, a1, a2, a3, a4, fun c hc ↦ Or.inr (Or.inr (Or.inl (a5 c hc)))⟩`. Distinguish the cases in `hpd : p = h.d`.

Substitute `hpd` using the available equality. Take `⟨R, w, a1, a2, a3, a4, a5⟩` from `hone h.d hdp (by omega) hdq (Or.inr rfl)`. Conclude with `⟨R, w, a1, a2, a3, a4, fun c hc ↦ Or.inr (Or.inr (Or.inr (a5 c hc)))⟩`. Establish `hpq1' : h.q1.factorization p = 0` using `Nat.factorization_eq_zero_of_not_dvd (fun hdv ↦ hpq1 ((Nat.prime_dvd_prime_iff_eq hp hq1).1 hdv))`. Establish `hpd' : h.d.factorization p = 0` using `Nat.factorization_eq_zero_of_not_dvd (fun hdv ↦ hpd ((Nat.prime_dvd_prime_iff_eq hp hdp).1 hdv))`.

Establish `hvp` using `hv p`. Rewrite `hvp` using `[hpq1', hpd']`. Establish `hpos : 0 < h.N.factorization p` using `hp.factorization_pos_of_dvd hN0 hpN`. Distinguish the cases in `hle : h.N.factorization p ≤ h.q.factorization p`. Establish `hpq : p ∣ h.q` using `Nat.dvd_of_factorization_pos (by omega)`.

Take `⟨w, hwq, hw1, hwχ⟩` from `exists_coprime_modEq_one_chi_ne_one_of_primitive h.chi.χ h.chi.prim hp hpq`. Use `⟨h.q, w, hqN, (hp.pow_dvd_iff_le_factorization hq0).2 hle, hw1, hwq.coprime_dvd_right hpq, fun c hc ↦ Or.inr (Or.inl ?_)⟩` and prove the remaining obligations. Rewrite using `[(ZMod.natCast_eq_natCast_iff c w h.q).2 hc]`. Conclude with `hwχ`. Establish `h2pos : 0 < (2 ^ (h.ex + 2)).factorization p` using `by omega`.

Establish `hp2 : p = 2`. Assume the negation of the conclusion as `hp2`. Rewrite `h2pos` using `[Nat.factorization_eq_zero_of_not_dvd (hodd p hp hp2)]`. Conclude with `lt_irrefl 0 h2pos`. Substitute `hp2` using the available equality.

Establish `h2f : (2 ^ (h.ex + 2)).factorization 2 = h.ex + 2`. Rewrite using `[Nat.factorization_pow, Finsupp.smul_apply, Nat.prime_two.factorization_self]`. Simplify using the standard rewrite rules. Establish `hv2 : h.N.factorization 2 = h.ex + 2` using `by omega`. Establish `hpow : 2 ^ (h.ex + 2) = 2 ^ (h.ex + 1) * 2` using `by ring`.

Establish `ht : 2 ≤ 2 ^ (h.ex + 1)`. Combine the equalities or inequalities in the displayed calculation. Use `⟨2 ^ (h.ex + 2), 1 + 2 ^ (h.ex + 1), h2N, by rw [hv2], ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hpow, Nat.mul_div_cancel _ (by norm_num)]`. Conclude with `((Nat.modEq_iff_dvd' (by omega)).2 (by simp)).symm`.

Use `Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 ?_)` and prove the remaining obligations. Rewrite using `[Nat.dvd_add_left (dvd_pow_self 2 (by omega : h.ex + 1 ≠ 0))]`. Evaluate the numerical expressions. Introduce `c hc left`. Rewrite using `[(ZMod.natCast_eq_natCast_iff c _ _).2 hc]`.

Prove the components needed by the constructor for the conclusion. Introduce `heq`. Establish `h1` using `(ZMod.natCast_eq_natCast_iff' (1 + 2 ^ (h.ex + 1)) 1 (2 ^ (h.ex + 2))).1 (by rw [heq, Nat.cast_one])`. Rewrite `h1` using `[Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]`. Use linear arithmetic over natural numbers and integers.

Introduce `heq`. Establish `h0 : (((1 + 2 ^ (h.ex + 1)) + 1 : ℕ) : ZMod (2 ^ (h.ex + 2))) = 0`. Establish `heq' : ((1 : ZMod (2 ^ (h.ex + 2))) + 2 ^ (h.ex + 1)) = -1` using `by exact_mod_cast heq`. Use `push_cast`. Rewrite using `[heq']`.

Expand and normalize the polynomial expressions, which then agree. Rewrite `h0` using `[ZMod.natCast_eq_zero_iff]`. Use `Nat.le_of_dvd (by omega) h0` as an intermediate fact. Establish `ht4 : 4 ≤ 2 ^ (h.ex + 1)`. Combine the equalities or inequalities in the displayed calculation.

Use linear arithmetic over natural numbers and integers.
-/
private theorem exists_modEq_one_unitOfCoprime_not_mem_host_H (h : Host) (p : ℕ) (hp : p.Prime) (hpN : p ∣ h.N) :
    ∃ c : ℕ, ∃ hc : c.Coprime h.N, c ≡ 1 [MOD h.N / p] ∧ ZMod.unitOfCoprime c hc ∉ h.H := by
  obtain ⟨hq1, hq18, hdp, hd16, hcop⟩ := h.pair
  have hNdef : h.N = (2 ^ (h.ex + 2)).lcm h.q * (h.q1 * h.d) := rfl
  have hN0 : h.N ≠ 0 := (Host.N_pos h).ne'
  haveI := h.chi.ne
  have hq0 : h.q ≠ 0 := NeZero.ne h.chi.N
  have hq10 : h.q1 ≠ 0 := hq1.ne_zero
  have hd0 : h.d ≠ 0 := hdp.ne_zero
  have h20 : 2 ^ (h.ex + 2) ≠ 0 := by positivity
  have hA0 : (2 ^ (h.ex + 2)).lcm h.q ≠ 0 := Nat.lcm_ne_zero h20 hq0
  have he2 := h.two_le
  suffices key : ∃ R w : ℕ, R ∣ h.N ∧ ordProj[p] h.N ∣ R ∧ w ≡ 1 [MOD R / p] ∧ w.Coprime p ∧
      ∀ c, c ≡ w [MOD R] → ((c : ZMod (2 ^ (h.ex + 2))) ≠ 1 ∧ (c : ZMod (2 ^ (h.ex + 2))) ≠ -1) ∨
        h.chi.χ (c : ZMod h.chi.N) ≠ 1 ∨ (c : ZMod h.q1) = -1 ∨ (c : ZMod h.d) = -1 by
    obtain ⟨R, w, hR, hPR, hw, hwp, hgood⟩ := key
    obtain ⟨c, hcR, hc1, hcN⟩ := exists_coprime_modEq_of_modEq_one_div hp hN0 hpN hR hPR hw hwp
    exact ⟨c, hcN, hc1, unitOfCoprime_not_mem_host_H_of_cond h c hcN (hgood c hcR)⟩
  have hAN : (2 ^ (h.ex + 2)).lcm h.q ∣ h.N := by rw [hNdef]; exact dvd_mul_right _ _
  have hqN : h.q ∣ h.N := (Nat.dvd_lcm_right _ _).trans hAN
  have h2N : 2 ^ (h.ex + 2) ∣ h.N := (Nat.dvd_lcm_left _ _).trans hAN
  have hq1N : h.q1 ∣ h.N := by rw [hNdef]; exact (dvd_mul_right _ _).trans (dvd_mul_left _ _)
  have hdN : h.d ∣ h.N := by rw [hNdef]; exact (dvd_mul_left _ _).trans (dvd_mul_left _ _)
  have hv : ∀ r, h.N.factorization r = max ((2 ^ (h.ex + 2)).factorization r) (h.q.factorization r)
      + h.q1.factorization r + h.d.factorization r := by
    intro r
    rw [hNdef, Nat.factorization_mul hA0 (mul_ne_zero hq10 hd0), Nat.factorization_mul hq10 hd0,
      Nat.factorization_lcm h20 hq0]
    simp [add_assoc]
  have hodd : ∀ r, r.Prime → r ≠ 2 → ¬ r ∣ 2 ^ (h.ex + 2) := by
    intro r hr hr2 hdv
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow hdv))
  have hq1q : ¬ h.q1 ∣ h.q := by
    intro hdv
    have : Nat.Coprime h.q1 h.chi.N := hcop.coprime_dvd_left (dvd_mul_right _ _)
    exact hq1.one_lt.ne' (Nat.Coprime.eq_one_of_dvd this hdv)
  have hdq : ¬ h.d ∣ h.q := by
    intro hdv
    have : Nat.Coprime h.d h.chi.N := hcop.coprime_dvd_left (dvd_mul_left _ _)
    exact hdp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd this hdv)
  have hq1d : h.q1 ≠ h.d := by omega
  have hone : ∀ r, r.Prime → r % 4 = 3 → ¬ r ∣ h.q → (r = h.q1 ∨ r = h.d) →
      ∃ R w : ℕ, R ∣ h.N ∧ ordProj[r] h.N ∣ R ∧ w ≡ 1 [MOD R / r] ∧ w.Coprime r ∧
      ∀ c, c ≡ w [MOD R] → (c : ZMod r) = -1 := by
    intro r hr hr4 hrq hrr
    have hr2 : r ≠ 2 := by omega
    have hvr : h.N.factorization r = 1 := by
      rw [hv r, Nat.factorization_eq_zero_of_not_dvd (hodd r hr hr2),
        Nat.factorization_eq_zero_of_not_dvd hrq]
      rcases hrr with rfl | rfl
      · rw [hr.factorization_self, Nat.factorization_eq_zero_of_not_dvd]
        · simp
        · intro hdv
          exact hq1d ((Nat.prime_dvd_prime_iff_eq hr hdp).1 hdv)
      · rw [hr.factorization_self, Nat.factorization_eq_zero_of_not_dvd]
        · simp
        · intro hdv
          exact hq1d ((Nat.prime_dvd_prime_iff_eq hr hq1).1 hdv).symm
    refine ⟨r, r - 1, ?_, ?_, ?_, ?_, ?_⟩
    · rcases hrr with rfl | rfl
      · exact hq1N
      · exact hdN
    · rw [hvr, pow_one]
    · rw [Nat.div_self hr.pos]
      exact Nat.modEq_one
    · refine (hr.coprime_iff_not_dvd.2 ?_).symm
      exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
    · intro c hc
      rw [(ZMod.natCast_eq_natCast_iff c (r - 1) r).2 hc, Nat.cast_sub hr.one_le, Nat.cast_one,
        ZMod.natCast_self, zero_sub]
  by_cases hpq1 : p = h.q1
  · subst hpq1
    obtain ⟨R, w, a1, a2, a3, a4, a5⟩ := hone h.q1 hq1 (by omega) hq1q (Or.inl rfl)
    exact ⟨R, w, a1, a2, a3, a4, fun c hc ↦ Or.inr (Or.inr (Or.inl (a5 c hc)))⟩
  by_cases hpd : p = h.d
  · subst hpd
    obtain ⟨R, w, a1, a2, a3, a4, a5⟩ := hone h.d hdp (by omega) hdq (Or.inr rfl)
    exact ⟨R, w, a1, a2, a3, a4, fun c hc ↦ Or.inr (Or.inr (Or.inr (a5 c hc)))⟩
  have hpq1' : h.q1.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd
    (fun hdv ↦ hpq1 ((Nat.prime_dvd_prime_iff_eq hp hq1).1 hdv))
  have hpd' : h.d.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd
    (fun hdv ↦ hpd ((Nat.prime_dvd_prime_iff_eq hp hdp).1 hdv))
  have hvp := hv p
  rw [hpq1', hpd'] at hvp
  have hpos : 0 < h.N.factorization p := hp.factorization_pos_of_dvd hN0 hpN
  by_cases hle : h.N.factorization p ≤ h.q.factorization p
  · have hpq : p ∣ h.q := Nat.dvd_of_factorization_pos (by omega)
    obtain ⟨w, hwq, hw1, hwχ⟩ := exists_coprime_modEq_one_chi_ne_one_of_primitive h.chi.χ h.chi.prim hp hpq
    refine ⟨h.q, w, hqN, (hp.pow_dvd_iff_le_factorization hq0).2 hle, hw1,
      hwq.coprime_dvd_right hpq, fun c hc ↦ Or.inr (Or.inl ?_)⟩
    rw [(ZMod.natCast_eq_natCast_iff c w h.q).2 hc]
    exact hwχ
  · have h2pos : 0 < (2 ^ (h.ex + 2)).factorization p := by omega
    have hp2 : p = 2 := by
      by_contra hp2
      rw [Nat.factorization_eq_zero_of_not_dvd (hodd p hp hp2)] at h2pos
      exact lt_irrefl 0 h2pos
    subst hp2
    have h2f : (2 ^ (h.ex + 2)).factorization 2 = h.ex + 2 := by
      rw [Nat.factorization_pow, Finsupp.smul_apply, Nat.prime_two.factorization_self]
      simp
    have hv2 : h.N.factorization 2 = h.ex + 2 := by omega
    have hpow : 2 ^ (h.ex + 2) = 2 ^ (h.ex + 1) * 2 := by ring
    have ht : 2 ≤ 2 ^ (h.ex + 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (h.ex + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    refine ⟨2 ^ (h.ex + 2), 1 + 2 ^ (h.ex + 1), h2N, by rw [hv2], ?_, ?_, ?_⟩
    · rw [hpow, Nat.mul_div_cancel _ (by norm_num)]
      exact ((Nat.modEq_iff_dvd' (by omega)).2 (by simp)).symm
    · refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 ?_)
      rw [Nat.dvd_add_left (dvd_pow_self 2 (by omega : h.ex + 1 ≠ 0))]
      norm_num
    · intro c hc
      left
      rw [(ZMod.natCast_eq_natCast_iff c _ _).2 hc]
      constructor
      · intro heq
        have h1 := (ZMod.natCast_eq_natCast_iff' (1 + 2 ^ (h.ex + 1)) 1 (2 ^ (h.ex + 2))).1
          (by rw [heq, Nat.cast_one])
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h1
        omega
      · intro heq
        have h0 : (((1 + 2 ^ (h.ex + 1)) + 1 : ℕ) : ZMod (2 ^ (h.ex + 2))) = 0 := by
          have heq' : ((1 : ZMod (2 ^ (h.ex + 2))) + 2 ^ (h.ex + 1)) = -1 := by exact_mod_cast heq
          push_cast
          rw [heq']
          ring
        rw [ZMod.natCast_eq_zero_iff] at h0
        have := Nat.le_of_dvd (by omega) h0
        have ht4 : 4 ≤ 2 ^ (h.ex + 1) := by
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ (h.ex + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega

/- English proof (translation)
Introduce `h E _ _ hE`. Establish `hL` using `hostLevel h E hE`. Establish `hN0 : h.N ≠ 0` using `(Host.N_pos h).ne'`. Establish `hmem : h.N ∈ {N : ℕ | 0 < N ∧ Nonempty (E →ₐ[ℚ] CyclotomicField N ℚ)}`. Take `⟨j, ζ, -, -⟩` from `hL`.

Conclude with `⟨Host.N_pos h, ⟨j⟩⟩`. Establish `key : ∀ M, 0 < M → Nonempty (E →ₐ[ℚ] CyclotomicField M ℚ) → h.N ∣ M`. Introduce `M hM hf`. Use `haveI : NeZero M := ⟨hM.ne'⟩`. Assume the negation of the conclusion as `hnd`.

Rewrite `hnd` using `[← Nat.factorization_le_iff_dvd hN0 hM.ne']`. Choose the witnesses or unpack the hypotheses as in `⟨p, hp⟩ : ∃ p, M.factorization p < h.N.factorization p := by`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Conclude with `hnd (Finsupp.le_def.2 hcon)`.

Establish `hpp : p.Prime`. Assume the negation of the conclusion as `hnp`. Simplify using `[Nat.factorization_eq_zero_of_not_prime _ hnp] at hp`. Establish `hpN : p ∣ h.N` using `Nat.dvd_of_factorization_pos (by omega)`. Take `⟨c, hc, hc1, hcH⟩` from `exists_modEq_one_unitOfCoprime_not_mem_host_H h p hpp hpN`.

Take `⟨H', hH'⟩` from `(Chr.levChange E M).1 hf`. Establish `hL0 : M.lcm h.N ≠ 0` using `Nat.lcm_ne_zero hM.ne' hN0`. Use `haveI : NeZero (M.lcm h.N) := ⟨hL0⟩`. Establish `hML : M ∣ M.lcm h.N` using `Nat.dvd_lcm_left _ _`. Establish `hNL : h.N ∣ M.lcm h.N` using `Nat.dvd_lcm_right _ _`.

Establish `h1` using `((Chr.levChange E (M.lcm h.N)).2 M hML H').1 hH'`. Establish `h2` using `((Chr.levChange E (M.lcm h.N)).2 h.N hNL h.H).1 hL`. Establish `heq` using `subgroup_eq_of_chr_hasLevel E (M.lcm h.N) _ _ h1 h2`. Establish `hLfac : (M.lcm h.N).factorization p = h.N.factorization p`. Rewrite using `[Nat.factorization_lcm hM.ne' hN0, Finsupp.sup_apply, sup_eq_right.2 hp.le]`.

Establish `hPN : ordProj[p] (M.lcm h.N) ∣ h.N`. Rewrite using `[hLfac]`. Conclude with `Nat.ordProj_dvd _ _`. Establish `hcp : c.Coprime p` using `hc.coprime_dvd_right hpN`. Establish `hpL : p ∣ M.lcm h.N` using `hpN.trans hNL`.

Take `⟨v, hvN, hv1, hvL⟩` from `exists_coprime_modEq_of_modEq_one_div hpp hL0 hpL hNL hPN hc1 hcp`. Establish `hLp0 : M.lcm h.N / p ≠ 0` using `(Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hL0) hpL) hpp.pos).ne'`. Establish `hMLp : M ∣ M.lcm h.N / p`. Rewrite using `[← Nat.factorization_le_iff_dvd hM.ne' hLp0, Nat.factorization_div hpL, hpp.factorization]`. Introduce `r`.

Establish `hMr` using `(Nat.factorization_le_iff_dvd hM.ne' hL0).2 hML r`. Rewrite using `[Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply]`. Use `split_ifs with hr`. Substitute `hr` using the available equality. Use linear arithmetic over natural numbers and integers.

Use linear arithmetic over natural numbers and integers. Establish `hV1 : ZMod.unitOfCoprime v hvL ∈ Subgroup.comap (ZMod.unitsMap hML) H'`. Rewrite using `[Subgroup.mem_comap]`. Establish `hone : ZMod.unitsMap hML (ZMod.unitOfCoprime v hvL) = 1`. Apply `Units.ext` to reduce the goal to its premises.

Rewrite using `[unitsMap_unitOfCoprime_coe_eq, Units.val_one, ← Nat.cast_one]`. Conclude with `(ZMod.natCast_eq_natCast_iff _ _ _).2 (hv1.of_dvd hMLp)`. Rewrite using `[hone]`. Conclude with `one_mem _`. Rewrite `hV1` using `[heq, Subgroup.mem_comap]`.

Establish `hmap : ZMod.unitsMap hNL (ZMod.unitOfCoprime v hvL) = ZMod.unitOfCoprime c hc`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[unitsMap_unitOfCoprime_coe_eq, ZMod.coe_unitOfCoprime]`. Conclude with `(ZMod.natCast_eq_natCast_iff _ _ _).2 hvN`. Rewrite `hV1` using `[hmap]`.

Conclude with `hcH hV1`. Use `show sInf {N : ℕ | 0 < N ∧ Nonempty (E →ₐ[ℚ] CyclotomicField N ℚ)} = h.N`. Apply `le_antisymm (Nat.sInf_le hmem)` to reduce the goal to its premises. Take `⟨hpos, hf⟩` from `Nat.sInf_mem ⟨_, hmem⟩`. Conclude with `Nat.le_of_dvd hpos (key _ hpos hf)`.
-/
theorem UpperTheory.V.HV.hostCond :
    ∀ (h : Host) (E : Type) [Field E] [NumberField E], IsChiField h.chi h.ex h.q1 h.d E → condF E = h.N := by
  intro h E _ _ hE
  have hL := hostLevel h E hE
  have hN0 : h.N ≠ 0 := (Host.N_pos h).ne'
  have hmem : h.N ∈ {N : ℕ | 0 < N ∧ Nonempty (E →ₐ[ℚ] CyclotomicField N ℚ)} := by
    obtain ⟨j, ζ, -, -⟩ := hL
    exact ⟨Host.N_pos h, ⟨j⟩⟩
  have key : ∀ M, 0 < M → Nonempty (E →ₐ[ℚ] CyclotomicField M ℚ) → h.N ∣ M := by
    intro M hM hf
    haveI : NeZero M := ⟨hM.ne'⟩
    by_contra hnd
    rw [← Nat.factorization_le_iff_dvd hN0 hM.ne'] at hnd
    obtain ⟨p, hp⟩ : ∃ p, M.factorization p < h.N.factorization p := by
      by_contra hcon
      push_neg at hcon
      exact hnd (Finsupp.le_def.2 hcon)
    have hpp : p.Prime := by
      by_contra hnp
      simp [Nat.factorization_eq_zero_of_not_prime _ hnp] at hp
    have hpN : p ∣ h.N := Nat.dvd_of_factorization_pos (by omega)
    obtain ⟨c, hc, hc1, hcH⟩ := exists_modEq_one_unitOfCoprime_not_mem_host_H h p hpp hpN
    obtain ⟨H', hH'⟩ := (Chr.levChange E M).1 hf
    have hL0 : M.lcm h.N ≠ 0 := Nat.lcm_ne_zero hM.ne' hN0
    haveI : NeZero (M.lcm h.N) := ⟨hL0⟩
    have hML : M ∣ M.lcm h.N := Nat.dvd_lcm_left _ _
    have hNL : h.N ∣ M.lcm h.N := Nat.dvd_lcm_right _ _
    have h1 := ((Chr.levChange E (M.lcm h.N)).2 M hML H').1 hH'
    have h2 := ((Chr.levChange E (M.lcm h.N)).2 h.N hNL h.H).1 hL
    have heq := subgroup_eq_of_chr_hasLevel E (M.lcm h.N) _ _ h1 h2
    have hLfac : (M.lcm h.N).factorization p = h.N.factorization p := by
      rw [Nat.factorization_lcm hM.ne' hN0, Finsupp.sup_apply, sup_eq_right.2 hp.le]
    have hPN : ordProj[p] (M.lcm h.N) ∣ h.N := by
      rw [hLfac]
      exact Nat.ordProj_dvd _ _
    have hcp : c.Coprime p := hc.coprime_dvd_right hpN
    have hpL : p ∣ M.lcm h.N := hpN.trans hNL
    obtain ⟨v, hvN, hv1, hvL⟩ := exists_coprime_modEq_of_modEq_one_div hpp hL0 hpL hNL hPN hc1 hcp
    have hLp0 : M.lcm h.N / p ≠ 0 :=
      (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hL0) hpL) hpp.pos).ne'
    have hMLp : M ∣ M.lcm h.N / p := by
      rw [← Nat.factorization_le_iff_dvd hM.ne' hLp0, Nat.factorization_div hpL, hpp.factorization]
      intro r
      have hMr := (Nat.factorization_le_iff_dvd hM.ne' hL0).2 hML r
      rw [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply]
      split_ifs with hr
      · subst hr
        omega
      · omega
    have hV1 : ZMod.unitOfCoprime v hvL ∈ Subgroup.comap (ZMod.unitsMap hML) H' := by
      rw [Subgroup.mem_comap]
      have hone : ZMod.unitsMap hML (ZMod.unitOfCoprime v hvL) = 1 := by
        apply Units.ext
        rw [unitsMap_unitOfCoprime_coe_eq, Units.val_one, ← Nat.cast_one]
        exact (ZMod.natCast_eq_natCast_iff _ _ _).2 (hv1.of_dvd hMLp)
      rw [hone]
      exact one_mem _
    rw [heq, Subgroup.mem_comap] at hV1
    have hmap : ZMod.unitsMap hNL (ZMod.unitOfCoprime v hvL) = ZMod.unitOfCoprime c hc := by
      apply Units.ext
      rw [unitsMap_unitOfCoprime_coe_eq, ZMod.coe_unitOfCoprime]
      exact (ZMod.natCast_eq_natCast_iff _ _ _).2 hvN
    rw [hmap] at hV1
    exact hcH hV1
  show sInf {N : ℕ | 0 < N ∧ Nonempty (E →ₐ[ℚ] CyclotomicField N ℚ)} = h.N
  apply le_antisymm (Nat.sInf_le hmem)
  obtain ⟨hpos, hf⟩ := Nat.sInf_mem ⟨_, hmem⟩
  exact Nat.le_of_dvd hpos (key _ hpos hf)
