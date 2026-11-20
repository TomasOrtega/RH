import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.IsGenEig

namespace UpperTheory.V.Z.Sym.Glob

/- English proof (translation)
Establish `hinj : Function.Injective (LinearMap.mulLeft ℤ x)` using `hx`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Set `e` to `LinearEquiv.ofInjective (LinearMap.mulLeft ℤ x) hinj`. Establish `h` using `Submodule.natAbs_det_equiv (LinearMap.range (LinearMap.mulLeft ℤ x)) e`. Combine the equalities or inequalities in the displayed calculation.

Use `congr 2`. Rewrite using `[Ne, LinearMap.det_eq_zero_iff_ker_ne_bot, not_not, LinearMap.ker_eq_bot]`. Conclude with `hinj`.
-/
private theorem index_range_mulLeft_eq_natAbs_det_and_det_ne_zero {B : Type} [Ring B] [Module.Free ℤ B] [Module.Finite ℤ B] (x : B)
    (hx : Function.Injective (fun z : B => x * z)) :
    (LinearMap.range (LinearMap.mulLeft ℤ x)).toAddSubgroup.index =
      (LinearMap.det (LinearMap.mulLeft ℤ x)).natAbs ∧ LinearMap.det (LinearMap.mulLeft ℤ x) ≠ 0 := by
  have hinj : Function.Injective (LinearMap.mulLeft ℤ x) := hx
  refine ⟨?_, ?_⟩
  · let e := LinearEquiv.ofInjective (LinearMap.mulLeft ℤ x) hinj
    have h := Submodule.natAbs_det_equiv (LinearMap.range (LinearMap.mulLeft ℤ x)) e
    calc (LinearMap.range (LinearMap.mulLeft ℤ x)).toAddSubgroup.index
        = Nat.card (B ⧸ LinearMap.range (LinearMap.mulLeft ℤ x)) := rfl
      _ = _ := h.symm
      _ = _ := by
        congr 2
  · rw [Ne, LinearMap.det_eq_zero_iff_ker_ne_bot, not_not, LinearMap.ker_eq_bot]
    exact hinj

/- English proof (translation)
Use `set K0 : ℤ := ∑ t, ∑ l, ∑ i, |b.repr (b t * b l) i| with hK0`. Establish `hK0n : 0 ≤ K0` using `Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _`. Use `⟨(Fintype.card ι).factorial * K0.natAbs ^ Fintype.card ι, fun c m hc => ?_⟩` and prove the remaining obligations. Rewrite using `[← LinearMap.det_toMatrix b]`. Establish `hent : ∀ i l, |LinearMap.toMatrix b b (LinearMap.mulLeft ℤ (∑ t, c t • b t)) i l| ≤ (m : ℤ) * K0`.

Introduce `i l`. Rewrite using `[LinearMap.toMatrix_apply, LinearMap.mulLeft_apply, Finset.sum_mul]`. Simplify using `only [smul_mul_assoc, map_sum, map_zsmul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]`. Combine the equalities or inequalities in the displayed calculation. Apply `Finset.sum_le_sum` to reduce the goal to its premises.

Introduce `t _`. Rewrite using `[abs_mul]`. Conclude with `mul_le_mul_of_nonneg_right (hc t) (abs_nonneg _)`. Use `_ = (m : ℤ) * ∑ t, |b.repr (b t * b l) i| := by rw [Finset.mul_sum]`. Use `_ ≤ (m : ℤ) * K0 := by`.

Apply `mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg m)` to reduce the goal to its premises. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `t _`. Combine the equalities or inequalities in the displayed calculation. Establish `hdet` using `Matrix.det_le (abv := AbsoluteValue.abs) (x := (m : ℤ) * K0) (fun i l => hent i l)`.

Establish `key : (((LinearMap.toMatrix b b (LinearMap.mulLeft ℤ (∑ t, c t • b t))).det.natAbs : ℕ) : ℤ) ≤ (((Fintype.card ι).factorial * K0.natAbs ^ Fintype.card ι * m ^ Fintype.card ι : ℕ) : ℤ)`. Rewrite using `[Int.natCast_natAbs]`. Use `push_cast`. Rewrite using `[abs_of_nonneg hK0n]`. Combine the equalities or inequalities in the displayed calculation.

Conclude with `key` after adjusting the coercions.
-/
private theorem exists_natAbs_det_mulLeft_sum_le_mul_pow_card {B : Type} [Ring B] {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℤ B) :
    ∃ C : ℕ, ∀ (c : ι → ℤ) (m : ℕ), (∀ i, |c i| ≤ m) →
      (LinearMap.det (LinearMap.mulLeft ℤ (∑ i, c i • b i))).natAbs ≤ C * m ^ Fintype.card ι := by
  set K0 : ℤ := ∑ t, ∑ l, ∑ i, |b.repr (b t * b l) i| with hK0
  have hK0n : 0 ≤ K0 := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨(Fintype.card ι).factorial * K0.natAbs ^ Fintype.card ι, fun c m hc => ?_⟩
  rw [← LinearMap.det_toMatrix b]
  have hent : ∀ i l, |LinearMap.toMatrix b b (LinearMap.mulLeft ℤ (∑ t, c t • b t)) i l| ≤ (m : ℤ) * K0 := by
    intro i l
    rw [LinearMap.toMatrix_apply, LinearMap.mulLeft_apply, Finset.sum_mul]
    simp only [smul_mul_assoc, map_sum, map_zsmul, Finsupp.coe_finset_sum, Finset.sum_apply,
      Finsupp.smul_apply, smul_eq_mul]
    calc |∑ t, c t * b.repr (b t * b l) i| ≤ ∑ t, |c t * b.repr (b t * b l) i| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ t, (m : ℤ) * |b.repr (b t * b l) i| := by
          apply Finset.sum_le_sum
          intro t _
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (hc t) (abs_nonneg _)
      _ = (m : ℤ) * ∑ t, |b.repr (b t * b l) i| := by rw [Finset.mul_sum]
      _ ≤ (m : ℤ) * K0 := by
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg m)
          apply Finset.sum_le_sum
          intro t _
          calc |b.repr (b t * b l) i| ≤ ∑ i', |b.repr (b t * b l) i'| :=
                Finset.single_le_sum (f := fun i' => |b.repr (b t * b l) i'|)
                  (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
            _ ≤ ∑ l', ∑ i', |b.repr (b t * b l') i'| :=
                Finset.single_le_sum (f := fun l' => ∑ i', |b.repr (b t * b l') i'|)
                  (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ l)
  have hdet := Matrix.det_le (abv := AbsoluteValue.abs) (x := (m : ℤ) * K0) (fun i l => hent i l)
  have key : (((LinearMap.toMatrix b b (LinearMap.mulLeft ℤ (∑ t, c t • b t))).det.natAbs : ℕ) : ℤ) ≤
      (((Fintype.card ι).factorial * K0.natAbs ^ Fintype.card ι * m ^ Fintype.card ι : ℕ) : ℤ) := by
    rw [Int.natCast_natAbs]
    push_cast
    rw [abs_of_nonneg hK0n]
    calc |(LinearMap.toMatrix b b (LinearMap.mulLeft ℤ (∑ t, c t • b t))).det|
        ≤ (Fintype.card ι).factorial • ((m : ℤ) * K0) ^ Fintype.card ι := hdet
      _ = _ := by rw [nsmul_eq_mul, mul_pow]; ring
  exact_mod_cast key

/- English proof (translation)
Set `b` to `Module.Free.chooseBasis ℤ B`. Take `⟨C, hC⟩` from `exists_natAbs_det_mulLeft_sum_le_mul_pow_card b`. Use `⟨C.factorial, Nat.factorial_ne_zero C, fun I hI hD => ?_⟩` and prove the remaining obligations. Establish `hk : 0 < Fintype.card (Module.Free.ChooseBasisIndex ℤ B)`. Use `Module.finrank_pos (R := ℤ) (M := B)` as an intermediate fact.

Rewrite `this` using `[Module.finrank_eq_card_chooseBasisIndex]`. Then use the resulting hypothesis. Use `set k := Fintype.card (Module.Free.ChooseBasisIndex ℤ B) with hkdef`. Use `set D := I.index with hDdef`. Use `set m := Nat.findGreatest (fun m => m ^ k ≤ D) D with hmdef`. Establish `hm1 : m ^ k ≤ D` using `Nat.findGreatest_spec (P := fun m => m ^ k ≤ D) (Nat.zero_le D) (by rw [zero_pow hk.ne']; exact Nat.zero_le _)`.

Establish `hm2 : D < (m + 1) ^ k`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Establish `hle : m + 1 ≤ D` using `le_trans (Nat.le_self_pow hk.ne' _) hcon`. Conclude with `Nat.findGreatest_is_greatest (P := fun m => m ^ k ≤ D) (Nat.lt_succ_self m) hle hcon`.

Use `haveI : I.FiniteIndex := ⟨hD⟩`. Use `haveI : Finite (B ⧸ I) := AddSubgroup.finite_quotient_of_finiteIndex`. Use `letI := Fintype.ofFinite (B ⧸ I)`. Set `f : (Module.Free.ChooseBasisIndex ℤ B → Fin (m + 1)) → B ⧸ I` to `fun c => QuotientAddGroup.mk (∑ i, ((c i : ℕ) : ℤ) • b i)`. Establish `hcard : Fintype.card (B ⧸ I) < Fintype.card (Module.Free.ChooseBasisIndex ℤ B → Fin (m + 1))`.

Rewrite using `[Fintype.card_fun, Fintype.card_fin, ← Nat.card_eq_fintype_card]`. Conclude with `hm2`. Take `⟨c, c', hne, hcc⟩` from `Fintype.exists_ne_map_eq_of_card_lt f hcard`. Set `d : Module.Free.ChooseBasisIndex ℤ B → ℤ` to `fun i => ((c i : ℕ) : ℤ) - ((c' i : ℕ) : ℤ)`. Establish `hxeq : ∑ i, d i • b i = (∑ i, ((c i : ℕ) : ℤ) • b i) - ∑ i, ((c' i : ℕ) : ℤ) • b i`.

Simplify using `only [d, sub_smul, Finset.sum_sub_distrib]`. Establish `hxI : ∑ i, d i • b i ∈ I`. Establish `h0` using `(QuotientAddGroup.eq (s := I)).1 hcc`. Rewrite using `[hxeq]`. Establish `h1` using `I.neg_mem h0`.

Simplify `h1` using `[sub_eq_add_neg, add_comm]`. Establish `hx0 : ∑ i, d i • b i ≠ 0`. Introduce `h0`. Apply `hne` to reduce the goal to its premises. Use function extensionality and compare the values at `i`.

Establish `h1` using `congrArg (fun v => b.repr v i) h0`. Simplify using `only [Module.Basis.repr_sum_self, map_zero, Finsupp.coe_zero, Pi.zero_apply, d] at h1`. Conclude with `Fin.ext (by omega)`. Establish `hdb : ∀ i, |d i| ≤ (m : ℤ)`. Introduce `i`.

Establish `h1 : (c i : ℕ) ≤ m` using `Nat.lt_succ_iff.1 (c i).isLt`. Establish `h2 : (c' i : ℕ) ≤ m` using `Nat.lt_succ_iff.1 (c' i).isLt`. Rewrite using `[abs_le]`. Apply the tactic sequence `constructor <;> simp only [d] <;> omega`. Take `⟨hidx, hdet0⟩` from `index_range_mulLeft_eq_natAbs_det_and_det_ne_zero _ (hinj _ hx0)`.

Use `set x := ∑ i, d i • b i with hx`. Use `set X := (LinearMap.range (LinearMap.mulLeft ℤ x)).toAddSubgroup with hXdef`. Establish `hXI : X ≤ I`. Introduce and unpack `_ ⟨z, rfl⟩`. Conclude with `hI x hxI z`.

Establish `hrel` using `AddSubgroup.relIndex_mul_index hXI`. Establish `hbound : X.index ≤ C * D`. Rewrite using `[hidx]`. Conclude with `le_trans (hC d m hdb) (Nat.mul_le_mul_left C hm1)`. Establish `hX0 : X.index ≠ 0`.

Rewrite using `[hidx]`. Conclude with `Int.natAbs_ne_zero.2 hdet0`. Establish `hr0 : X.relIndex I ≠ 0`. Introduce `h0`. Rewrite `hrel` using `[h0, zero_mul]`.

Conclude with `hX0 hrel.symm`. Establish `hrC : X.relIndex I ≤ C`. Establish `hDpos : 0 < D` using `Nat.pos_of_ne_zero hD`. Rewrite `hbound` using `[← hrel]`. Conclude with `Nat.le_of_mul_le_mul_right hbound hDpos`.

Use `⟨x, hxI, hx0, fun y hy => ?_⟩` and prove the remaining obligations. Establish `hmem` using `AddSubgroup.nsmul_index_mem (X.addSubgroupOf I) ⟨y, hy⟩`. Rewrite `hmem` using `[AddSubgroup.mem_addSubgroupOf]`. Establish `hmem' : X.relIndex I • y ∈ X` using `hmem`. Take `⟨q, hq⟩` from `Nat.dvd_factorial (Nat.pos_of_ne_zero hr0) hrC`.

Establish `hCy : (C.factorial : B) * y ∈ X`. Rewrite using `[← nsmul_eq_mul, hq, mul_comm, ← smul_smul]`. Conclude with `X.nsmul_mem hmem' q`. Take `⟨z, hz⟩` from `hCy`. Conclude with `⟨z, hz.symm⟩`.
-/
private theorem exists_nat_mul_mem_principal_of_rightIdeal_index_ne_zero {B : Type} [Ring B] [Nontrivial B] [Module.Free ℤ B] [Module.Finite ℤ B]
    (hinj : ∀ x : B, x ≠ 0 → Function.Injective (fun z : B => x * z)) :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ I : AddSubgroup B, (∀ y ∈ I, ∀ z : B, y * z ∈ I) → I.index ≠ 0 →
      ∃ x ∈ I, x ≠ 0 ∧ ∀ y ∈ I, ∃ z : B, (N : B) * y = x * z := by
  classical
  let b := Module.Free.chooseBasis ℤ B
  obtain ⟨C, hC⟩ := exists_natAbs_det_mulLeft_sum_le_mul_pow_card b
  refine ⟨C.factorial, Nat.factorial_ne_zero C, fun I hI hD => ?_⟩
  have hk : 0 < Fintype.card (Module.Free.ChooseBasisIndex ℤ B) := by
    have := Module.finrank_pos (R := ℤ) (M := B)
    rwa [Module.finrank_eq_card_chooseBasisIndex] at this
  set k := Fintype.card (Module.Free.ChooseBasisIndex ℤ B) with hkdef
  set D := I.index with hDdef
  set m := Nat.findGreatest (fun m => m ^ k ≤ D) D with hmdef
  have hm1 : m ^ k ≤ D := Nat.findGreatest_spec (P := fun m => m ^ k ≤ D) (Nat.zero_le D)
    (by rw [zero_pow hk.ne']; exact Nat.zero_le _)
  have hm2 : D < (m + 1) ^ k := by
    by_contra hcon
    push_neg at hcon
    have hle : m + 1 ≤ D := le_trans (Nat.le_self_pow hk.ne' _) hcon
    exact Nat.findGreatest_is_greatest (P := fun m => m ^ k ≤ D) (Nat.lt_succ_self m) hle hcon
  haveI : I.FiniteIndex := ⟨hD⟩
  haveI : Finite (B ⧸ I) := AddSubgroup.finite_quotient_of_finiteIndex
  letI := Fintype.ofFinite (B ⧸ I)
  let f : (Module.Free.ChooseBasisIndex ℤ B → Fin (m + 1)) → B ⧸ I :=
    fun c => QuotientAddGroup.mk (∑ i, ((c i : ℕ) : ℤ) • b i)
  have hcard : Fintype.card (B ⧸ I) < Fintype.card (Module.Free.ChooseBasisIndex ℤ B → Fin (m + 1)) := by
    rw [Fintype.card_fun, Fintype.card_fin, ← Nat.card_eq_fintype_card]
    exact hm2
  obtain ⟨c, c', hne, hcc⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  let d : Module.Free.ChooseBasisIndex ℤ B → ℤ := fun i => ((c i : ℕ) : ℤ) - ((c' i : ℕ) : ℤ)
  have hxeq : ∑ i, d i • b i = (∑ i, ((c i : ℕ) : ℤ) • b i) - ∑ i, ((c' i : ℕ) : ℤ) • b i := by
    simp only [d, sub_smul, Finset.sum_sub_distrib]
  have hxI : ∑ i, d i • b i ∈ I := by
    have h0 := (QuotientAddGroup.eq (s := I)).1 hcc
    rw [hxeq]
    have h1 := I.neg_mem h0
    simpa [sub_eq_add_neg, add_comm] using h1
  have hx0 : ∑ i, d i • b i ≠ 0 := by
    intro h0
    apply hne
    funext i
    have h1 := congrArg (fun v => b.repr v i) h0
    simp only [Module.Basis.repr_sum_self, map_zero, Finsupp.coe_zero, Pi.zero_apply, d] at h1
    exact Fin.ext (by omega)
  have hdb : ∀ i, |d i| ≤ (m : ℤ) := by
    intro i
    have h1 : (c i : ℕ) ≤ m := Nat.lt_succ_iff.1 (c i).isLt
    have h2 : (c' i : ℕ) ≤ m := Nat.lt_succ_iff.1 (c' i).isLt
    rw [abs_le]
    constructor <;> simp only [d] <;> omega
  obtain ⟨hidx, hdet0⟩ := index_range_mulLeft_eq_natAbs_det_and_det_ne_zero _ (hinj _ hx0)
  set x := ∑ i, d i • b i with hx
  set X := (LinearMap.range (LinearMap.mulLeft ℤ x)).toAddSubgroup with hXdef
  have hXI : X ≤ I := by
    rintro _ ⟨z, rfl⟩
    exact hI x hxI z
  have hrel := AddSubgroup.relIndex_mul_index hXI
  have hbound : X.index ≤ C * D := by
    rw [hidx]
    exact le_trans (hC d m hdb) (Nat.mul_le_mul_left C hm1)
  have hX0 : X.index ≠ 0 := by
    rw [hidx]
    exact Int.natAbs_ne_zero.2 hdet0
  have hr0 : X.relIndex I ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hrel
    exact hX0 hrel.symm
  have hrC : X.relIndex I ≤ C := by
    have hDpos : 0 < D := Nat.pos_of_ne_zero hD
    rw [← hrel] at hbound
    exact Nat.le_of_mul_le_mul_right hbound hDpos
  refine ⟨x, hxI, hx0, fun y hy => ?_⟩
  have hmem := AddSubgroup.nsmul_index_mem (X.addSubgroupOf I) ⟨y, hy⟩
  rw [AddSubgroup.mem_addSubgroupOf] at hmem
  have hmem' : X.relIndex I • y ∈ X := hmem
  obtain ⟨q, hq⟩ := Nat.dvd_factorial (Nat.pos_of_ne_zero hr0) hrC
  have hCy : (C.factorial : B) * y ∈ X := by
    rw [← nsmul_eq_mul, hq, mul_comm, ← smul_smul]
    exact X.nsmul_mem hmem' q
  obtain ⟨z, hz⟩ := hCy
  exact ⟨z, hz.symm⟩

/- English proof (translation)
Establish `hunit : ∀ γ, σ γ * σ γ⁻¹ = 1 ∧ σ γ⁻¹ * σ γ = 1` using `fun γ => ⟨by rw [← map_mul, mul_inv_cancel, map_one], by rw [← map_mul, inv_mul_cancel, map_one]⟩`. Establish `hjunit : ∀ γ, j (σ γ) * j (σ γ⁻¹) = 1 ∧ j (σ γ⁻¹) * j (σ γ) = 1` using `fun γ => ⟨by rw [← map_mul, (hunit γ).1, map_one], by rw [← map_mul, (hunit γ).2, map_one]⟩`. Establish `hρinv : ∀ g, ρ g * ρ g⁻¹ = 1 ∧ ρ g⁻¹ * ρ g = 1` using `fun g => ⟨by rw [← map_mul, mul_inv_cancel, map_one], by rw [← map_mul, inv_mul_cancel, map_one]⟩`. Establish `hinjA : ∀ y : A, y ∈ R.comap j → y ≠ 0 → ∀ z z' : A, y * z = y * z' → z = z'`. Introduce `y hy hy0 z z' h`.

Take `⟨γ, rfl⟩` from `hσ y hy hy0`. Combine the equalities or inequalities in the displayed calculation. Use `haveI : NoZeroSMulDivisors ℤ (R.comap j) := ⟨fun {c x} h => by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`.

Take `⟨hc0, hx0⟩` from `hc`. Establish `hx0' : (x : A) ≠ 0` using `fun h' => hx0 (Subtype.ext h')`. Establish `h1 : (c : A) * (x : A) = 0`. Establish `h2` using `congrArg Subtype.val h`. Simplify `h2` using `[zsmul_eq_mul]`.

Take `⟨γ, hγ⟩` from `hσ x x.2 hx0'`. Establish `h3 : (c : A) = 0`. Combine the equalities or inequalities in the displayed calculation. Conclude with `hc0 (Int.cast_eq_zero.1 h3)⟩`. Use `haveI : Module.Free ℤ (R.comap j) := Module.free_of_finite_type_torsion_free'`.

Use `haveI : Nontrivial (R.comap j) := inferInstance`. Take `⟨N, hN0, hNA⟩` from `exists_nat_mul_mem_principal_of_rightIdeal_index_ne_zero (B := R.comap j) (fun x hx z z' h => Subtype.ext (hinjA _ x.2 (fun h' => hx (Subtype.ext h')) _ _ (congrArg Subtype.val h)))`. Set `good : G → Prop` to `fun k => ρ k⁻¹ ∈ R ∧ (N : M) * ρ k ∈ R`. Establish `hstep : ∀ g, ∃ γ k, good k ∧ g = ι γ * k`. Introduce `g`.

Take `⟨n, hn0, hnR⟩` from `hden g`. Establish `hnB : (n : A) ∈ R.comap j` using `by show j (n : A) ∈ R`. Rewrite using `[map_natCast]`. Conclude with `natCast_mem R n`. Take `⟨γ1, hγ1⟩` from `hσ (n : A) hnB (Nat.cast_ne_zero.2 hn0)`.

Establish `ha : ρ (ι γ1 * g) ∈ R`. Rewrite using `[map_mul, hι, hγ1, map_natCast]`. Conclude with `hnR`. Take `⟨n', hn'0, hn'R⟩` from `hden (ι γ1 * g)⁻¹`. Use `set a := ρ (ι γ1 * g)`.

Use `set a' := ρ (ι γ1 * g)⁻¹`. Establish `haa' : a * a' = 1` using `(hρinv _).1`. Establish `ha'a : a' * a = 1` using `(hρinv _).2`. Establish `hn'R2 : a' * (n' : M) ∈ R`. Rewrite using `[← Nat.cast_comm]`.

Conclude with `hn'R`. Set `I : AddSubgroup (R.comap j)` to `{ carrier := {y | ∃ r ∈ R, j (y : A) = a * r} add_mem' := by`. Introduce and unpack `x y ⟨r, hr, hx⟩ ⟨s, hs, hy⟩`. Conclude with `⟨r + s, R.add_mem hr hs, by simp only [Subring.coe_add, map_add, hx, hy, mul_add]⟩`. Use the proof step `zero_mem' := ⟨0, R.zero_mem, by simp⟩`.

Use the proof step `neg_mem' := by`. Introduce and unpack `x ⟨r, hr, hx⟩`. Conclude with `⟨-r, R.neg_mem hr, by simp only [Subring.coe_neg, map_neg, hx, mul_neg]⟩ }`. Establish `hIr : ∀ y ∈ I, ∀ z : R.comap j, y * z ∈ I`. Introduce and unpack `y ⟨r, hr, hy⟩ z`.

Conclude with `⟨r * j (z : A), R.mul_mem hr z.2, by simp only [Subring.coe_mul, map_mul, hy, mul_assoc]⟩`. Establish `hn'I : ((n' : R.comap j)) ∈ I` using `⟨a' * n', hn'R2, by simp only [Subring.coe_natCast, map_natCast]; rw [← mul_assoc, haa', one_mul]⟩`. Establish `hn'0B : ((n' : R.comap j)) ≠ 0`. Introduce `h`. Apply `hn'0` to reduce the goal to its premises.

Establish `h2` using `congrArg Subtype.val h`. Simplify using `using h2`. Take `⟨hidx, hdet⟩` from `index_range_mulLeft_eq_natAbs_det_and_det_ne_zero (n' : R.comap j) (fun z z' h => Subtype.ext (hinjA _ (n' : R.comap j).2 (fun h' => hn'0B (Subtype.ext h')) _ _ (congrArg Subtype.val h)))`. Establish `hle : (LinearMap.range (LinearMap.mulLeft ℤ (n' : R.comap j))).toAddSubgroup ≤ I`. Introduce and unpack `_ ⟨z, rfl⟩`.

Conclude with `hIr _ hn'I z`. Use `haveI : (LinearMap.range (LinearMap.mulLeft ℤ (n' : R.comap j))).toAddSubgroup.FiniteIndex := ⟨by rw [hidx]; exact Int.natAbs_ne_zero.2 hdet⟩`. Establish `hIidx : I.index ≠ 0` using `(AddSubgroup.finiteIndex_of_le hle).index_ne_zero`. Take `⟨x, ⟨r0, hr0R, hr0⟩, hx0, hxdiv⟩` from `hNA I hIr hIidx`. Establish `hx0' : (x : A) ≠ 0` using `fun h' => hx0 (Subtype.ext h')`.

Take `⟨γx, hγx⟩` from `hσ x x.2 hx0'`. Take `⟨y, hyB, r, hr, hay⟩` from `hap a ha n' hn'0`. Establish `hyI : (⟨y, hyB⟩ : R.comap j) ∈ I`. Use `⟨1 - a' * n' * r, R.sub_mem R.one_mem (R.mul_mem hn'R2 hr), ?_⟩` and prove the remaining obligations. Use `show j y = a * (1 - a' * n' * r)`.

Rewrite using `[mul_sub, mul_one, ← mul_assoc, ← mul_assoc, haa', one_mul, hay]`. Normalize the expressions using the abelian group laws. Take `⟨z, hz⟩` from `hxdiv _ hyI`. Take `⟨z', hz'⟩` from `hxdiv _ hn'I`. Establish `hz1 : (N : M) * j y = j (σ γx) * j (z : A)`.

Establish `h2` using `congrArg (fun w : R.comap j => j (w : A)) hz`. Simplify using `only [Subring.coe_mul, Subring.coe_natCast, map_mul, map_natCast] at h2`. Rewrite using `[hγx]`. Conclude with `h2`. Establish `hz2 : (N : M) * (n' : M) = j (σ γx) * j (z' : A)`.

Establish `h2` using `congrArg (fun w : R.comap j => j (w : A)) hz'`. Simplify using `only [Subring.coe_mul, Subring.coe_natCast, map_mul, map_natCast] at h2`. Rewrite using `[hγx]`. Conclude with `h2`. Use `⟨γ1⁻¹ * γx, ι γx⁻¹ * (ι γ1 * g), ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[mul_inv_rev, map_inv ι, inv_inv, map_mul, hι, hγx, hr0, ← mul_assoc, ha'a, one_mul]`. Conclude with `hr0R`. Rewrite using `[map_mul, hι]`. Establish `h3 : (N : M) * (j (σ γx⁻¹) * a) = j (z : A) + j (z' : A) * r`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← mul_assoc, Nat.cast_comm, mul_assoc]`. Use `_ = j (σ γx⁻¹) * (j (σ γx) * (j (z : A) + j (z' : A) * r)) := by`. Use `congr 1`. Rewrite using `[hay, mul_add, hz1, ← mul_assoc (N : M) (n' : M) r, hz2, mul_add, mul_assoc]`. Use `_ = _ := by rw [← mul_assoc, (hjunit γx).2, one_mul]`.

Rewrite using `[h3]`. Conclude with `R.add_mem z.2 (R.mul_mem z'.2 hr)`. Rewrite using `[map_mul, map_inv, map_inv] group`. Establish `hN0B : ((N : R.comap j)) ≠ 0`. Introduce `h`.

Apply `hN0` to reduce the goal to its premises. Establish `h2` using `congrArg Subtype.val h`. Simplify using `using h2`. Take `⟨hKidx, hKdet⟩` from `index_range_mulLeft_eq_natAbs_det_and_det_ne_zero (N : R.comap j) (fun z z' h => Subtype.ext (hinjA _ (N : R.comap j).2 (fun h' => hN0B (Subtype.ext h')) _ _ (congrArg Subtype.val h)))`. Use `set K := (LinearMap.range (LinearMap.mulLeft ℤ (N : R.comap j))).toAddSubgroup with hKd`.

Use `haveI : K.FiniteIndex := ⟨by rw [hKidx]; exact Int.natAbs_ne_zero.2 hKdet⟩`. Use `haveI : Finite (R.comap j ⧸ K) := AddSubgroup.finite_quotient_of_finiteIndex`. Set `φ : G → Set (R.comap j ⧸ K)` to `fun k => (QuotientAddGroup.mk : R.comap j → R.comap j ⧸ K) '' {y | ∃ r ∈ R, j (y : A) = r * ρ k⁻¹}`. Establish `hsub : ∀ s k, good s → good k → φ s ⊆ φ k → ρ (s⁻¹ * k) ∈ R`. Introduce and unpack `s k ⟨hs1, hs2⟩ ⟨hk1, hk2⟩ hφ`.

Take `⟨y, hyB, r, hr, hcy⟩` from `hap (ρ s⁻¹) hs1 N hN0`. Establish `hyJ : (⟨y, hyB⟩ : R.comap j) ∈ {y : R.comap j | ∃ r ∈ R, j (y : A) = r * ρ s⁻¹}`. Use `⟨1 - r * ((N : M) * ρ s), R.sub_mem R.one_mem (R.mul_mem hr hs2), ?_⟩` and prove the remaining obligations. Use `show j y = (1 - r * ((N : M) * ρ s)) * ρ s⁻¹`. Rewrite using `[sub_mul, one_mul, mul_assoc, mul_assoc, (hρinv s).1, mul_one, hcy, Nat.cast_comm]`.

Normalize the expressions using the abelian group laws. Take `⟨y', ⟨r', hr', hy'⟩, hyy'⟩` from `hφ ⟨_, hyJ, rfl⟩`. Take `⟨w, hw⟩` from `(QuotientAddGroup.eq (s := K)).1 hyy'`. Establish `hw' : j y = j (y' : A) + (N : M) * j (w : A)`. Establish `h2` using `congrArg (fun v : R.comap j => j (v : A)) hw`.

Simplify using `only [LinearMap.mulLeft_apply, Subring.coe_mul, Subring.coe_natCast, Subring.coe_add, Subring.coe_neg, map_mul, map_natCast, map_add, map_neg] at h2`. Rewrite using `[h2]`. Normalize the expressions using the abelian group laws. Establish `e1 : j (w : A) * ((N : M) * ρ k) * ρ k⁻¹ = (N : M) * j (w : A)`. Rewrite using `[mul_assoc, mul_assoc, (hρinv k).1, mul_one, Nat.cast_comm]`.

Establish `e2 : r * ((N : M) * ρ k) * ρ k⁻¹ = (N : M) * r`. Rewrite using `[mul_assoc, mul_assoc, (hρinv k).1, mul_one, Nat.cast_comm]`. Establish `key : ρ s⁻¹ = (r' + j (w : A) * ((N : M) * ρ k) + r * ((N : M) * ρ k)) * ρ k⁻¹`. Rewrite using `[add_mul, add_mul, e1, e2, ← hy', ← hw', hcy]`. Rewrite using `[map_mul, key, mul_assoc, (hρinv k).2, mul_one]`.

Conclude with `R.add_mem (R.add_mem hr' (R.mul_mem w.2 hk2)) (R.mul_mem hr hk2)`. Establish `hfin : (φ '' {k | good k}).Finite` using `Set.toFinite _`. Use `⟨hfin.toFinset.image (fun v => if h : ∃ k, good k ∧ φ k = v then Classical.choose h else 1), fun g => ?_⟩` and prove the remaining obligations. Take `⟨γ, k, hk, rfl⟩` from `hstep g`. Establish `hex : ∃ k', good k' ∧ φ k' = φ k` using `⟨k, hk, rfl⟩`.

Establish `hs` using `Classical.choose_spec hex`. Use `⟨γ, Classical.choose hex, ?_, (Classical.choose hex)⁻¹ * k, ?_, by group⟩` and prove the remaining obligations. Rewrite using `[Finset.mem_image]`. Use `⟨φ k, hfin.mem_toFinset.2 ⟨k, hk, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[dif_pos hex]`.

Apply `hU` to reduce the goal to its premises. Conclude with `hsub _ k hs.1 hk hs.2.le`. Rewrite using `[mul_inv_rev, inv_inv]`. Conclude with `hsub k _ hk hs.1 hs.2.ge`.
-/
theorem cls_abs {A M Γ G : Type} [Ring A] [CharZero A] [Ring M] [Group Γ] [Group G] (j : A →+* M) (R : Subring M)
    [Module.Finite ℤ (R.comap j)] (ι : Γ →* G) (σ : Γ →* A) (ρ : G →* M) (hι : ∀ γ, ρ (ι γ) = j (σ γ)) (U : Subgroup G)
    (hU : ∀ g, ρ g ∈ R → ρ g⁻¹ ∈ R → g ∈ U) (hσ : ∀ y ∈ R.comap j, y ≠ 0 → ∃ γ, σ γ = y)
    (hap : ∀ m ∈ R, ∀ n : ℕ, n ≠ 0 → ∃ x ∈ R.comap j, ∃ r ∈ R, m = j x + (n : M) * r)
    (hden : ∀ g, ∃ n : ℕ, n ≠ 0 ∧ (n : M) * ρ g ∈ R) :
    ∃ S : Finset G, ∀ g, ∃ γ, ∃ s ∈ S, ∃ u ∈ U, g = ι γ * s * u := by
  classical
  have hunit : ∀ γ, σ γ * σ γ⁻¹ = 1 ∧ σ γ⁻¹ * σ γ = 1 := fun γ =>
    ⟨by rw [← map_mul, mul_inv_cancel, map_one], by rw [← map_mul, inv_mul_cancel, map_one]⟩
  have hjunit : ∀ γ, j (σ γ) * j (σ γ⁻¹) = 1 ∧ j (σ γ⁻¹) * j (σ γ) = 1 := fun γ =>
    ⟨by rw [← map_mul, (hunit γ).1, map_one], by rw [← map_mul, (hunit γ).2, map_one]⟩
  have hρinv : ∀ g, ρ g * ρ g⁻¹ = 1 ∧ ρ g⁻¹ * ρ g = 1 := fun g =>
    ⟨by rw [← map_mul, mul_inv_cancel, map_one], by rw [← map_mul, inv_mul_cancel, map_one]⟩
  have hinjA : ∀ y : A, y ∈ R.comap j → y ≠ 0 → ∀ z z' : A, y * z = y * z' → z = z' := by
    intro y hy hy0 z z' h
    obtain ⟨γ, rfl⟩ := hσ y hy hy0
    calc z = σ γ⁻¹ * (σ γ * z) := by rw [← mul_assoc, (hunit γ).2, one_mul]
      _ = z' := by rw [h, ← mul_assoc, (hunit γ).2, one_mul]
  haveI : NoZeroSMulDivisors ℤ (R.comap j) := ⟨fun {c x} h => by
    by_contra hc
    push_neg at hc
    obtain ⟨hc0, hx0⟩ := hc
    have hx0' : (x : A) ≠ 0 := fun h' => hx0 (Subtype.ext h')
    have h1 : (c : A) * (x : A) = 0 := by
      have h2 := congrArg Subtype.val h
      simpa [zsmul_eq_mul] using h2
    obtain ⟨γ, hγ⟩ := hσ x x.2 hx0'
    have h3 : (c : A) = 0 := by
      calc (c : A) = (c : A) * (σ γ * σ γ⁻¹) := by rw [(hunit γ).1, mul_one]
        _ = 0 := by rw [← mul_assoc, hγ, h1, zero_mul]
    exact hc0 (Int.cast_eq_zero.1 h3)⟩
  haveI : Module.Free ℤ (R.comap j) := Module.free_of_finite_type_torsion_free'
  haveI : Nontrivial (R.comap j) := inferInstance
  obtain ⟨N, hN0, hNA⟩ := exists_nat_mul_mem_principal_of_rightIdeal_index_ne_zero (B := R.comap j) (fun x hx z z' h =>
    Subtype.ext (hinjA _ x.2 (fun h' => hx (Subtype.ext h')) _ _ (congrArg Subtype.val h)))
  let good : G → Prop := fun k => ρ k⁻¹ ∈ R ∧ (N : M) * ρ k ∈ R
  have hstep : ∀ g, ∃ γ k, good k ∧ g = ι γ * k := by
    intro g
    obtain ⟨n, hn0, hnR⟩ := hden g
    have hnB : (n : A) ∈ R.comap j := by
      show j (n : A) ∈ R
      rw [map_natCast]
      exact natCast_mem R n
    obtain ⟨γ1, hγ1⟩ := hσ (n : A) hnB (Nat.cast_ne_zero.2 hn0)
    have ha : ρ (ι γ1 * g) ∈ R := by
      rw [map_mul, hι, hγ1, map_natCast]
      exact hnR
    obtain ⟨n', hn'0, hn'R⟩ := hden (ι γ1 * g)⁻¹
    set a := ρ (ι γ1 * g)
    set a' := ρ (ι γ1 * g)⁻¹
    have haa' : a * a' = 1 := (hρinv _).1
    have ha'a : a' * a = 1 := (hρinv _).2
    have hn'R2 : a' * (n' : M) ∈ R := by
      rw [← Nat.cast_comm]
      exact hn'R
    let I : AddSubgroup (R.comap j) :=
      { carrier := {y | ∃ r ∈ R, j (y : A) = a * r}
        add_mem' := by
          rintro x y ⟨r, hr, hx⟩ ⟨s, hs, hy⟩
          exact ⟨r + s, R.add_mem hr hs, by simp only [Subring.coe_add, map_add, hx, hy, mul_add]⟩
        zero_mem' := ⟨0, R.zero_mem, by simp⟩
        neg_mem' := by
          rintro x ⟨r, hr, hx⟩
          exact ⟨-r, R.neg_mem hr, by simp only [Subring.coe_neg, map_neg, hx, mul_neg]⟩ }
    have hIr : ∀ y ∈ I, ∀ z : R.comap j, y * z ∈ I := by
      rintro y ⟨r, hr, hy⟩ z
      exact ⟨r * j (z : A), R.mul_mem hr z.2, by simp only [Subring.coe_mul, map_mul, hy, mul_assoc]⟩
    have hn'I : ((n' : R.comap j)) ∈ I :=
      ⟨a' * n', hn'R2, by simp only [Subring.coe_natCast, map_natCast]; rw [← mul_assoc, haa', one_mul]⟩
    have hn'0B : ((n' : R.comap j)) ≠ 0 := by
      intro h
      apply hn'0
      have h2 := congrArg Subtype.val h
      simpa using h2
    obtain ⟨hidx, hdet⟩ := index_range_mulLeft_eq_natAbs_det_and_det_ne_zero (n' : R.comap j) (fun z z' h =>
      Subtype.ext (hinjA _ (n' : R.comap j).2 (fun h' => hn'0B (Subtype.ext h')) _ _ (congrArg Subtype.val h)))
    have hle : (LinearMap.range (LinearMap.mulLeft ℤ (n' : R.comap j))).toAddSubgroup ≤ I := by
      rintro _ ⟨z, rfl⟩
      exact hIr _ hn'I z
    haveI : (LinearMap.range (LinearMap.mulLeft ℤ (n' : R.comap j))).toAddSubgroup.FiniteIndex :=
      ⟨by rw [hidx]; exact Int.natAbs_ne_zero.2 hdet⟩
    have hIidx : I.index ≠ 0 := (AddSubgroup.finiteIndex_of_le hle).index_ne_zero
    obtain ⟨x, ⟨r0, hr0R, hr0⟩, hx0, hxdiv⟩ := hNA I hIr hIidx
    have hx0' : (x : A) ≠ 0 := fun h' => hx0 (Subtype.ext h')
    obtain ⟨γx, hγx⟩ := hσ x x.2 hx0'
    obtain ⟨y, hyB, r, hr, hay⟩ := hap a ha n' hn'0
    have hyI : (⟨y, hyB⟩ : R.comap j) ∈ I := by
      refine ⟨1 - a' * n' * r, R.sub_mem R.one_mem (R.mul_mem hn'R2 hr), ?_⟩
      show j y = a * (1 - a' * n' * r)
      rw [mul_sub, mul_one, ← mul_assoc, ← mul_assoc, haa', one_mul, hay]
      abel
    obtain ⟨z, hz⟩ := hxdiv _ hyI
    obtain ⟨z', hz'⟩ := hxdiv _ hn'I
    have hz1 : (N : M) * j y = j (σ γx) * j (z : A) := by
      have h2 := congrArg (fun w : R.comap j => j (w : A)) hz
      simp only [Subring.coe_mul, Subring.coe_natCast, map_mul, map_natCast] at h2
      rw [hγx]
      exact h2
    have hz2 : (N : M) * (n' : M) = j (σ γx) * j (z' : A) := by
      have h2 := congrArg (fun w : R.comap j => j (w : A)) hz'
      simp only [Subring.coe_mul, Subring.coe_natCast, map_mul, map_natCast] at h2
      rw [hγx]
      exact h2
    refine ⟨γ1⁻¹ * γx, ι γx⁻¹ * (ι γ1 * g), ⟨?_, ?_⟩, ?_⟩
    · rw [mul_inv_rev, map_inv ι, inv_inv, map_mul, hι, hγx, hr0, ← mul_assoc, ha'a, one_mul]
      exact hr0R
    · rw [map_mul, hι]
      have h3 : (N : M) * (j (σ γx⁻¹) * a) = j (z : A) + j (z' : A) * r := by
        calc (N : M) * (j (σ γx⁻¹) * a) = j (σ γx⁻¹) * ((N : M) * a) := by
              rw [← mul_assoc, Nat.cast_comm, mul_assoc]
          _ = j (σ γx⁻¹) * (j (σ γx) * (j (z : A) + j (z' : A) * r)) := by
              congr 1
              rw [hay, mul_add, hz1, ← mul_assoc (N : M) (n' : M) r, hz2, mul_add, mul_assoc]
          _ = _ := by rw [← mul_assoc, (hjunit γx).2, one_mul]
      rw [h3]
      exact R.add_mem z.2 (R.mul_mem z'.2 hr)
    · rw [map_mul, map_inv, map_inv]
      group
  have hN0B : ((N : R.comap j)) ≠ 0 := by
    intro h
    apply hN0
    have h2 := congrArg Subtype.val h
    simpa using h2
  obtain ⟨hKidx, hKdet⟩ := index_range_mulLeft_eq_natAbs_det_and_det_ne_zero (N : R.comap j) (fun z z' h =>
    Subtype.ext (hinjA _ (N : R.comap j).2 (fun h' => hN0B (Subtype.ext h')) _ _ (congrArg Subtype.val h)))
  set K := (LinearMap.range (LinearMap.mulLeft ℤ (N : R.comap j))).toAddSubgroup with hKd
  haveI : K.FiniteIndex := ⟨by rw [hKidx]; exact Int.natAbs_ne_zero.2 hKdet⟩
  haveI : Finite (R.comap j ⧸ K) := AddSubgroup.finite_quotient_of_finiteIndex
  let φ : G → Set (R.comap j ⧸ K) := fun k =>
    (QuotientAddGroup.mk : R.comap j → R.comap j ⧸ K) '' {y | ∃ r ∈ R, j (y : A) = r * ρ k⁻¹}
  have hsub : ∀ s k, good s → good k → φ s ⊆ φ k → ρ (s⁻¹ * k) ∈ R := by
    rintro s k ⟨hs1, hs2⟩ ⟨hk1, hk2⟩ hφ
    obtain ⟨y, hyB, r, hr, hcy⟩ := hap (ρ s⁻¹) hs1 N hN0
    have hyJ : (⟨y, hyB⟩ : R.comap j) ∈ {y : R.comap j | ∃ r ∈ R, j (y : A) = r * ρ s⁻¹} := by
      refine ⟨1 - r * ((N : M) * ρ s), R.sub_mem R.one_mem (R.mul_mem hr hs2), ?_⟩
      show j y = (1 - r * ((N : M) * ρ s)) * ρ s⁻¹
      rw [sub_mul, one_mul, mul_assoc, mul_assoc, (hρinv s).1, mul_one, hcy, Nat.cast_comm]
      abel
    obtain ⟨y', ⟨r', hr', hy'⟩, hyy'⟩ := hφ ⟨_, hyJ, rfl⟩
    obtain ⟨w, hw⟩ := (QuotientAddGroup.eq (s := K)).1 hyy'
    have hw' : j y = j (y' : A) + (N : M) * j (w : A) := by
      have h2 := congrArg (fun v : R.comap j => j (v : A)) hw
      simp only [LinearMap.mulLeft_apply, Subring.coe_mul, Subring.coe_natCast, Subring.coe_add,
        Subring.coe_neg, map_mul, map_natCast, map_add, map_neg] at h2
      rw [h2]
      abel
    have e1 : j (w : A) * ((N : M) * ρ k) * ρ k⁻¹ = (N : M) * j (w : A) := by
      rw [mul_assoc, mul_assoc, (hρinv k).1, mul_one, Nat.cast_comm]
    have e2 : r * ((N : M) * ρ k) * ρ k⁻¹ = (N : M) * r := by
      rw [mul_assoc, mul_assoc, (hρinv k).1, mul_one, Nat.cast_comm]
    have key : ρ s⁻¹ = (r' + j (w : A) * ((N : M) * ρ k) + r * ((N : M) * ρ k)) * ρ k⁻¹ := by
      rw [add_mul, add_mul, e1, e2, ← hy', ← hw', hcy]
    rw [map_mul, key, mul_assoc, (hρinv k).2, mul_one]
    exact R.add_mem (R.add_mem hr' (R.mul_mem w.2 hk2)) (R.mul_mem hr hk2)
  have hfin : (φ '' {k | good k}).Finite := Set.toFinite _
  refine ⟨hfin.toFinset.image (fun v => if h : ∃ k, good k ∧ φ k = v then Classical.choose h else 1),
    fun g => ?_⟩
  obtain ⟨γ, k, hk, rfl⟩ := hstep g
  have hex : ∃ k', good k' ∧ φ k' = φ k := ⟨k, hk, rfl⟩
  have hs := Classical.choose_spec hex
  refine ⟨γ, Classical.choose hex, ?_, (Classical.choose hex)⁻¹ * k, ?_, by group⟩
  · rw [Finset.mem_image]
    refine ⟨φ k, hfin.mem_toFinset.2 ⟨k, hk, rfl⟩, ?_⟩
    rw [dif_pos hex]
  · apply hU
    · exact hsub _ k hs.1 hk hs.2.le
    · rw [mul_inv_rev, inv_inv]
      exact hsub k _ hk hs.1 hs.2.ge

/- English proof (translation)
Take `⟨S, hS⟩` from `hS`. Use `haveI : (U'.subgroupOf U).FiniteIndex := ⟨h⟩`. Use `haveI : Finite (U ⧸ U'.subgroupOf U) := Subgroup.finite_quotient_of_finiteIndex`. Use `letI := Fintype.ofFinite (U ⧸ U'.subgroupOf U)`. Use `⟨(S ×ˢ (Finset.univ.image (fun q : U ⧸ U'.subgroupOf U => ((Quotient.out q : U) : G)))).image (fun p => p.1 * p.2), fun g => ?_⟩` and prove the remaining obligations.

Take `⟨γ, s, hs, u, hu, rfl⟩` from `hS g`. Take `⟨k, hk⟩` from `QuotientGroup.mk_out_eq_mul (U'.subgroupOf U) (⟨u, hu⟩ : U)`. Use `⟨γ, s * ((Quotient.out (QuotientGroup.mk (⟨u, hu⟩ : U) : U ⧸ U'.subgroupOf U) : U) : G), ?_, ((k : U) : G)⁻¹, ?_, ?_⟩` and prove the remaining obligations. Conclude with `Finset.mem_image.2 ⟨(s, _), Finset.mem_product.2 ⟨hs, Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩⟩, rfl⟩`. Conclude with `U'.inv_mem (Subgroup.mem_subgroupOf.1 k.2)`.

Rewrite using `[hk]`. Simplify using `[mul_assoc]`.
-/
theorem cls_of_relIndex {Γ G : Type} [Group Γ] [Group G] (ι : Γ →* G) (U U' : Subgroup G) (h : U'.relIndex U ≠ 0)
    (hS : ∃ S : Finset G, ∀ g, ∃ γ, ∃ s ∈ S, ∃ u ∈ U, g = ι γ * s * u) :
    ∃ S : Finset G, ∀ g, ∃ γ, ∃ s ∈ S, ∃ u ∈ U', g = ι γ * s * u := by
  classical
  obtain ⟨S, hS⟩ := hS
  haveI : (U'.subgroupOf U).FiniteIndex := ⟨h⟩
  haveI : Finite (U ⧸ U'.subgroupOf U) := Subgroup.finite_quotient_of_finiteIndex
  letI := Fintype.ofFinite (U ⧸ U'.subgroupOf U)
  refine ⟨(S ×ˢ (Finset.univ.image (fun q : U ⧸ U'.subgroupOf U => ((Quotient.out q : U) : G)))).image
    (fun p => p.1 * p.2), fun g => ?_⟩
  obtain ⟨γ, s, hs, u, hu, rfl⟩ := hS g
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (U'.subgroupOf U) (⟨u, hu⟩ : U)
  refine ⟨γ, s * ((Quotient.out (QuotientGroup.mk (⟨u, hu⟩ : U) : U ⧸ U'.subgroupOf U) : U) : G), ?_,
    ((k : U) : G)⁻¹, ?_, ?_⟩
  · exact Finset.mem_image.2 ⟨(s, _), Finset.mem_product.2 ⟨hs, Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩⟩, rfl⟩
  · exact U'.inv_mem (Subgroup.mem_subgroupOf.1 k.2)
  · rw [hk]
    simp [mul_assoc]

/- English proof (translation)
Establish `hC : (⨅ v : S, Subgroup.comap (P.p v) (U' v)).relIndex (P.box U) ≠ 0`. Use `Subgroup.relIndex_iInf_ne_zero (fun v => ?_)` and prove the remaining obligations. Rewrite using `[Subgroup.relIndex_comap]`. Establish `hle : Subgroup.map (P.p v) (P.box U) ≤ U v`. Rewrite using `[Subgroup.map_le_iff_le_comap]`.

Conclude with `iInf_le (fun w => Subgroup.comap (P.p w) (U w)) (v : I)`. Use `Subgroup.relIndex_ne_zero_trans (h1 v v.2) ?_` and prove the remaining obligations. Rewrite using `[Subgroup.relIndex_eq_one.mpr hle]`. Conclude with `one_ne_zero`. Establish `hX : (⨅ v : S, Subgroup.comap (P.p v) (U' v)) ⊓ P.box U ≤ P.box U'`.

Introduce `x hx`. Rewrite `hx` using `[Subgroup.mem_inf]`. Take `⟨hx1, hx2⟩` from `hx`. Simplify using `only [RPG.box, Subgroup.mem_iInf, Subgroup.mem_comap] at hx1 hx2 ⊢`. Introduce `v`.

Distinguish the cases in `hv : v ∈ S`. Conclude with `hx1 ⟨v, hv⟩`. Conclude with `h2 v hv (hx2 v)`. Use `Subgroup.relIndex_ne_zero_trans (K := (⨅ v : S, Subgroup.comap (P.p v) (U' v)) ⊓ P.box U) ?_ ?_` and prove the remaining obligations. Rewrite using `[Subgroup.relIndex_eq_one.mpr hX]`.

Conclude with `one_ne_zero`. Use `Subgroup.relIndex_inf_ne_zero hC ?_` and prove the remaining obligations. Rewrite using `[Subgroup.relIndex_eq_one.mpr le_rfl]`. Conclude with `one_ne_zero`.
-/
theorem box_relIndex {I G : Type} [Group G] {Gv : I → Type} [∀ v, Group (Gv v)] {K : ∀ v, Subgroup (Gv v)} (P : RPG G Gv K)
    (U U' : ∀ v, Subgroup (Gv v)) (S : Finset I) (h1 : ∀ v ∈ S, (U' v).relIndex (U v) ≠ 0) (h2 : ∀ v ∉ S, U v ≤ U' v) :
    (P.box U').relIndex (P.box U) ≠ 0 := by
  classical
  have hC : (⨅ v : S, Subgroup.comap (P.p v) (U' v)).relIndex (P.box U) ≠ 0 := by
    refine Subgroup.relIndex_iInf_ne_zero (fun v => ?_)
    rw [Subgroup.relIndex_comap]
    have hle : Subgroup.map (P.p v) (P.box U) ≤ U v := by
      rw [Subgroup.map_le_iff_le_comap]
      exact iInf_le (fun w => Subgroup.comap (P.p w) (U w)) (v : I)
    refine Subgroup.relIndex_ne_zero_trans (h1 v v.2) ?_
    rw [Subgroup.relIndex_eq_one.mpr hle]
    exact one_ne_zero
  have hX : (⨅ v : S, Subgroup.comap (P.p v) (U' v)) ⊓ P.box U ≤ P.box U' := by
    intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hx1, hx2⟩ := hx
    simp only [RPG.box, Subgroup.mem_iInf, Subgroup.mem_comap] at hx1 hx2 ⊢
    intro v
    by_cases hv : v ∈ S
    · exact hx1 ⟨v, hv⟩
    · exact h2 v hv (hx2 v)
  refine Subgroup.relIndex_ne_zero_trans (K := (⨅ v : S, Subgroup.comap (P.p v) (U' v)) ⊓ P.box U) ?_ ?_
  · rw [Subgroup.relIndex_eq_one.mpr hX]
    exact one_ne_zero
  · refine Subgroup.relIndex_inf_ne_zero hC ?_
    rw [Subgroup.relIndex_eq_one.mpr le_rfl]
    exact one_ne_zero

end UpperTheory.V.Z.Sym.Glob
