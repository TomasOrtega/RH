import Mathlib
open CategoryTheory Limits

namespace GlobalTheory

/- English proof (translation)
Take `⟨⟨a, ha⟩, hat⟩` from `(Submodule.mem_torsion_iff t).1 ht`. Establish `ha0 : a ≠ 0` using `nonZeroDivisors.ne_zero ha`. Express the relevant statement in the definitionally equal form `a • t = 0 at hat`. Use `set n := a.natAbs with hn`. Establish `hn0 : n ≠ 0` using `Int.natAbs_ne_zero.2 ha0`.

Establish `hnt : (n : ℤ) • t = 0`. Break down `Int.natAbs_eq a with h | h` into its components or cases. Rewrite using `[← h]`. Conclude with `hat`. Establish `: a = -(n : ℤ)` using `h`.

Rewrite `hat` using `[this, neg_smul, neg_eq_zero]`. Conclude with `hat`. Establish `hpow : ∀ k : ℕ, ∀ y : M, ((p : ℤ) ^ k) • y = 0 → y = 0`. Introduce `k`. Proceed by induction on `k with`.

Consider the case `zero => intro y hy`. Simplify using `using hy`. Consider the case `succ k ih`. Introduce `y hy`. Rewrite `hy` using `[pow_succ, mul_smul]`.

Conclude with `hM y (ih _ hy)`. Use `set k := n.factorization p`. Use `set m := n / p ^ k`. Establish `hnm : p ^ k * m = n` using `Nat.ordProj_mul_ordCompl_eq_self n p`. Establish `hmt : (m : ℤ) • t = 0`.

Apply `hpow k` to reduce the goal to its premises. Rewrite using `[← mul_smul]`. Establish `: ((p : ℤ) ^ k * (m : ℤ)) = (n : ℤ)` using `by exact_mod_cast hnm`. Rewrite using `[this, hnt]`. Establish `hndvd : ¬ p ∣ m` using `Nat.not_dvd_ordCompl hp.out hn0`.

Establish `hcop : Nat.Coprime p m` using `(Nat.Prime.coprime_iff_not_dvd hp.out).2 hndvd`. Establish `hic : IsCoprime (p : ℤ) (m : ℤ)`. Rewrite using `[Int.isCoprime_iff_gcd_eq_one]`. Simplify `hcop` using `[Int.gcd_natCast_natCast]`. Take `⟨u, v, huv⟩` from `hic`.

Use `⟨u • t, Submodule.smul_mem _ _ ht, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[add_smul, mul_smul, mul_smul, hmt, smul_zero, add_zero, smul_comm]`.
-/
theorem exists_torsion_eq_prime_smul_of_noPTorsion {M : Type*} [AddCommGroup M] (p : ℕ)
    [hp : Fact p.Prime] (hM : ∀ x : M, (p : ℤ) • x = 0 → x = 0) (t : M)
    (ht : t ∈ Submodule.torsion ℤ M) :
    ∃ s ∈ Submodule.torsion ℤ M, t = (p : ℤ) • s := by
  obtain ⟨⟨a, ha⟩, hat⟩ := (Submodule.mem_torsion_iff t).1 ht
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
  change a • t = 0 at hat
  set n := a.natAbs with hn
  have hn0 : n ≠ 0 := Int.natAbs_ne_zero.2 ha0
  have hnt : (n : ℤ) • t = 0 := by
    rcases Int.natAbs_eq a with h | h
    · rw [← h]; exact hat
    · have : a = -(n : ℤ) := h
      rw [this, neg_smul, neg_eq_zero] at hat; exact hat
  have hpow : ∀ k : ℕ, ∀ y : M, ((p : ℤ) ^ k) • y = 0 → y = 0 := by
    intro k
    induction k with
    | zero => intro y hy; simpa using hy
    | succ k ih =>
      intro y hy
      rw [pow_succ, mul_smul] at hy
      exact hM y (ih _ hy)
  set k := n.factorization p
  set m := n / p ^ k
  have hnm : p ^ k * m = n := Nat.ordProj_mul_ordCompl_eq_self n p
  have hmt : (m : ℤ) • t = 0 := by
    apply hpow k
    rw [← mul_smul]
    have : ((p : ℤ) ^ k * (m : ℤ)) = (n : ℤ) := by exact_mod_cast hnm
    rw [this, hnt]
  have hndvd : ¬ p ∣ m := Nat.not_dvd_ordCompl hp.out hn0
  have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp.out).2 hndvd
  have hic : IsCoprime (p : ℤ) (m : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    simpa [Int.gcd_natCast_natCast] using hcop
  obtain ⟨u, v, huv⟩ := hic
  refine ⟨u • t, Submodule.smul_mem _ _ ht, ?_⟩
  calc t = ((u * p + v * m : ℤ)) • t := by rw [huv, one_smul]
    _ = (p : ℤ) • (u • t) := by
      rw [add_smul, mul_smul, mul_smul, hmt, smul_zero, add_zero, smul_comm]

/- English proof (translation)
Use `subsingleton_of_forall_eq 0 fun z => ?_` and prove the remaining obligations. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => rfl`. Consider the case `tmul c t`. Take `⟨s, hs, hts⟩` from `exists_torsion_eq_prime_smul_of_noPTorsion p hM t.1 t.2`.

Establish `: t = (p : ℤ) • (⟨s, hs⟩ : Submodule.torsion ℤ M)` using `Subtype.ext hts`. Rewrite using `[this, ← TensorProduct.smul_tmul]`. Establish `hc : (p : ℤ) • c = 0`. Rewrite using `[zsmul_eq_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul]`. Rewrite using `[hc, TensorProduct.zero_tmul]`.

Consider the case `add x y hx hy => rw [hx, hy, add_zero]`.
-/
theorem subsingleton_zmod_tensor_torsion {M : Type*} [AddCommGroup M] (p : ℕ) [Fact p.Prime]
    (hM : ∀ x : M, (p : ℤ) • x = 0 → x = 0) :
    Subsingleton (TensorProduct ℤ (ZMod p) (Submodule.torsion ℤ M)) := by
  refine subsingleton_of_forall_eq 0 fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => rfl
  | tmul c t =>
    obtain ⟨s, hs, hts⟩ := exists_torsion_eq_prime_smul_of_noPTorsion p hM t.1 t.2
    have : t = (p : ℤ) • (⟨s, hs⟩ : Submodule.torsion ℤ M) := Subtype.ext hts
    rw [this, ← TensorProduct.smul_tmul]
    have hc : (p : ℤ) • c = 0 := by
      rw [zsmul_eq_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul]
    rw [hc, TensorProduct.zero_tmul]
  | add x y hx hy => rw [hx, hy, add_zero]

/- English proof (translation)
Take `rfl : inst = AddCommGroup.toIntModule M` from `Subsingleton.elim _ _`. Use `set T := Submodule.torsion ℤ M`. Use `haveI : Module.Free ℤ (M ⧸ T) := Module.free_of_finite_type_torsion_free'`. Use `haveI := subsingleton_zmod_tensor_torsion p hM`. Set `g` to `LinearMap.baseChange (ZMod p) T.mkQ`.

Establish `hg : ⇑g = ⇑(LinearMap.lTensor (ZMod p) T.mkQ)` using `LinearMap.baseChange_eq_ltensor _`. Establish `hex` using `lTensor_exact (ZMod p) (LinearMap.exact_subtype_mkQ T) (Submodule.mkQ_surjective T)`. Establish `hinj : Function.Injective g`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `y hy`.

Establish `hy' : LinearMap.lTensor (ZMod p) T.mkQ y = 0` using `by rw [← hg]; exact hy`. Take `⟨z, rfl⟩` from `(hex y).1 hy'`. Rewrite using `[Subsingleton.elim z 0, map_zero]`. Establish `hsurj : Function.Surjective g`. Rewrite using `[hg]`.

Conclude with `LinearMap.lTensor_surjective _ (Submodule.mkQ_surjective T)`. Rewrite using `[(LinearEquiv.ofBijective g ⟨hinj, hsurj⟩).finrank_eq, Module.finrank_baseChange, finrank_quotient_eq_of_le_torsion le_rfl]`.
-/
theorem finrank_zmod_tensor_eq_finrank_of_noPTorsion (M : Type*) [AddCommGroup M] [inst : Module ℤ M]
    [Module.Finite ℤ M] (p : ℕ) [Fact p.Prime] (hM : ∀ x : M, (p : ℤ) • x = 0 → x = 0) :
    Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) M) = Module.finrank ℤ M := by
  obtain rfl : inst = AddCommGroup.toIntModule M := Subsingleton.elim _ _
  set T := Submodule.torsion ℤ M
  haveI : Module.Free ℤ (M ⧸ T) := Module.free_of_finite_type_torsion_free'
  haveI := subsingleton_zmod_tensor_torsion p hM
  let g := LinearMap.baseChange (ZMod p) T.mkQ
  have hg : ⇑g = ⇑(LinearMap.lTensor (ZMod p) T.mkQ) := LinearMap.baseChange_eq_ltensor _
  have hex := lTensor_exact (ZMod p) (LinearMap.exact_subtype_mkQ T) (Submodule.mkQ_surjective T)
  have hinj : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have hy' : LinearMap.lTensor (ZMod p) T.mkQ y = 0 := by rw [← hg]; exact hy
    obtain ⟨z, rfl⟩ := (hex y).1 hy'
    rw [Subsingleton.elim z 0, map_zero]
  have hsurj : Function.Surjective g := by
    rw [hg]; exact LinearMap.lTensor_surjective _ (Submodule.mkQ_surjective T)
  rw [(LinearEquiv.ofBijective g ⟨hinj, hsurj⟩).finrank_eq, Module.finrank_baseChange,
    finrank_quotient_eq_of_le_torsion le_rfl]

/- English proof (translation)
Introduce `C p _ hC _`. Set `f : C.homology 0 ⟶ C.X 0` to `C.isoHomologyπ₀.inv ≫ C.iCycles 0`. Establish `hinj : Function.Injective (ConcreteCategory.hom f)` using `(ModuleCat.mono_iff_injective f).1 inferInstance`. Apply `finrank_zmod_tensor_eq_finrank_of_noPTorsion` to reduce the goal to its premises. Introduce `x hx`.

Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_zero]`. Apply `hC` to reduce the goal to its premises. Rewrite using `[← map_zsmul, hx, map_zero]`.
-/
theorem finrank_zmod_tensor_homology_zero :
    ∀ (C : CochainComplex (ModuleCat.{0} ℤ) ℕ) (p : ℕ) [Fact p.Prime],
      (∀ (x : C.X 0), (p : ℤ) • x = 0 → x = 0) → Module.Finite ℤ (C.homology 0) →
      Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) (C.homology 0)) =
        Module.finrank ℤ (C.homology 0) := by
  intro C p _ hC _
  let f : C.homology 0 ⟶ C.X 0 := C.isoHomologyπ₀.inv ≫ C.iCycles 0
  have hinj : Function.Injective (ConcreteCategory.hom f) :=
    (ModuleCat.mono_iff_injective f).1 inferInstance
  apply finrank_zmod_tensor_eq_finrank_of_noPTorsion
  intro x hx
  apply hinj
  rw [map_zero]
  apply hC
  rw [← map_zsmul, hx, map_zero]

end GlobalTheory
