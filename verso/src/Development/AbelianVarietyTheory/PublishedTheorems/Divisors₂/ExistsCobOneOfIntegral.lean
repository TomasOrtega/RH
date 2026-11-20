import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonneAt
import ReciprocityTheory.DualLattices.ExistsPrimitiveRoot

noncomputable section

open CategoryTheory WittVector Ideal TensorProduct Coalgebra

namespace GlobalTheory.PrismModel

open GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.Published

section Eps

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih => rw [← add_assoc, pow_succ', pow_mul, zeta_succ_pow, ih]`.
-/
private theorem zeta_add_pow_p_pow_eq_zeta (ε : PreTilt O p) (n k : ℕ) :
    zeta ε (n + k) ^ p ^ k = zeta ε n := by
  induction k with
  | zero => simp
  | succ k ih => rw [← add_assoc, pow_succ', pow_mul, zeta_succ_pow, ih]

/- English proof (translation)
Introduce `n`. Consider the cases of `n with`. Consider the case `zero`. Rewrite using `[pow_zero, IsPrimitiveRoot.one_right_iff]`. Establish `h0` using `zeta_add_pow_p_pow_eq_zeta ε 0 1`.

Rewrite `h0` using `[zero_add, pow_one]`. Rewrite using `[← h0, h.pow_eq_one]`. Consider the case `succ n`. Establish `h1 : zeta ε (n + 1) ^ p ^ n = zeta ε 1`. Establish `h2` using `zeta_add_pow_p_pow_eq_zeta ε 1 n`.

Rewrite `h2` using `[add_comm 1 n]`. Then use the resulting hypothesis. Rewrite using `[IsPrimitiveRoot.iff_orderOf]`. Apply `orderOf_eq_prime_pow` to reduce the goal to its premises. Rewrite using `[h1]`. Conclude with `h.ne_one (Fact.out : p.Prime).one_lt`.

Rewrite using `[pow_succ, pow_mul, h1, h.pow_eq_one]`.
-/
theorem isPrimitiveSystem_of_one {ε : PreTilt O p} (h : IsPrimitiveRoot (zeta ε 1) p) :
    IsPrimitiveSystem ε := by
  intro n
  cases n with
  | zero =>
    rw [pow_zero, IsPrimitiveRoot.one_right_iff]
    have h0 := zeta_add_pow_p_pow_eq_zeta ε 0 1
    rw [zero_add, pow_one] at h0
    rw [← h0, h.pow_eq_one]
  | succ n =>
    have h1 : zeta ε (n + 1) ^ p ^ n = zeta ε 1 := by
      have h2 := zeta_add_pow_p_pow_eq_zeta ε 1 n
      rwa [add_comm 1 n] at h2
    rw [IsPrimitiveRoot.iff_orderOf]
    apply orderOf_eq_prime_pow
    · rw [h1]
      exact h.ne_one (Fact.out : p.Prime).one_lt
    · rw [pow_succ, pow_mul, h1, h.pow_eq_one]

/- English proof (translation)
Establish `key : frobenius (Sandwich.nu ε) = Sandwich.mu ε`. Rewrite using `[Sandwich.nu, map_sub, map_one, frobenius_eq_map_frobenius, map_teichmuller, Sandwich.root, frobenius_apply_frobeniusEquiv_symm]`. Both sides reduce to the same expression. Use `conv_lhs => rw [← xi_mul_nu ε]`. Rewrite using `[map_mul, key]`.
-/
theorem frobenius_mu (ε : PreTilt O p) :
    frobenius (Sandwich.mu ε) = frobenius (xi ε) * Sandwich.mu ε := by
  have key : frobenius (Sandwich.nu ε) = Sandwich.mu ε := by
    rw [Sandwich.nu, map_sub, map_one, frobenius_eq_map_frobenius, map_teichmuller, Sandwich.root,
      frobenius_apply_frobeniusEquiv_symm]
    rfl
  conv_lhs => rw [← xi_mul_nu ε]
  rw [map_mul, key]

/- English proof (translation)
Establish `h1` using `hε 1`. Rewrite `h1` using `[pow_one]`. Rewrite using `[xi, map_sum]`. Simplify using `only [map_pow, fontaineTheta_teichmuller]`. Conclude with `h1.geom_sum_eq_zero (Fact.out : p.Prime).one_lt`.
-/
theorem theta_xi [IsDomain O] {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) :
    fontaineTheta O p (xi ε) = 0 := by
  have h1 := hε 1
  rw [pow_one] at h1
  rw [xi, map_sum]
  simp only [map_pow, fontaineTheta_teichmuller]
  exact h1.geom_sum_eq_zero (Fact.out : p.Prime).one_lt

end Eps

/- English proof (translation)
Establish `hI` using `PadicComplexInt.integers p`. Use `⟨hI.hom_inj, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[PadicComplex.norm_eq_norm]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, rfl⟩`.

Conclude with `Valued.toNormedField.norm_le_one_iff.2 (hI.map_le_one a)`. Introduce `hx`. Conclude with `hI.exists_of_le_one (Valued.toNormedField.norm_le_one_iff.1 hx)`.
-/
theorem isIntegers_padicComplex (p : ℕ) [Fact p.Prime] : IsIntegers 𝓞_ℂ_[p] ℂ_[p] := by
  have hI := PadicComplexInt.integers p
  refine ⟨hI.hom_inj, fun x => ?_⟩
  rw [PadicComplex.norm_eq_norm]
  constructor
  · rintro ⟨a, rfl⟩
    exact Valued.toNormedField.norm_le_one_iff.2 (hI.map_le_one a)
  · intro hx
    exact hI.exists_of_le_one (Valued.toNormedField.norm_le_one_iff.1 hx)

/- English proof (translation)
Establish `: IsUltrametricDist C` using `IsUltrametricDist.of_normedAlgebra ℚ_[p]`. Establish `: CharZero C` using `(RingHom.charZero_iff (algebraMap ℚ_[p] C).injective).mp inferInstance`. Establish `hv : (NormedField.valuation (K` using `C)).Integers O := { hom_inj := H.inj map_le_one := fun a => by`. Rewrite using `[NormedField.valuation_apply, ← NNReal.coe_le_one, coe_nnnorm]`. Conclude with `(H.mem_iff _).1 ⟨a, rfl⟩`.

Use `exists_of_le_one := fun r hr => by`. Rewrite `hr` using `[NormedField.valuation_apply, ← NNReal.coe_le_one, coe_nnnorm]`. Conclude with `(H.mem_iff r).2 hr }`. Take `⟨ε, hε⟩` from `ReciprocityTheory.PGsh.exists_eps (p := p) C NormedField.valuation O hv`. Conclude with `⟨ε, isPrimitiveSystem_of_one hε⟩`.
-/
theorem exists_system (p : ℕ) [Fact p.Prime] (C : Type) [NontriviallyNormedField C]
    [NormedAlgebra ℚ_[p] C] [IsAlgClosed C] (O : Type) [CommRing O] [Algebra O C]
    (H : IsIntegers O C) [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O] :
    ∃ ε : PreTilt O p, IsPrimitiveSystem ε := by
  have : IsUltrametricDist C := IsUltrametricDist.of_normedAlgebra ℚ_[p]
  have : CharZero C := (RingHom.charZero_iff (algebraMap ℚ_[p] C).injective).mp inferInstance
  have hv : (NormedField.valuation (K := C)).Integers O :=
    { hom_inj := H.inj
      map_le_one := fun a => by
        rw [NormedField.valuation_apply, ← NNReal.coe_le_one, coe_nnnorm]
        exact (H.mem_iff _).1 ⟨a, rfl⟩
      exists_of_le_one := fun r hr => by
        rw [NormedField.valuation_apply, ← NNReal.coe_le_one, coe_nnnorm] at hr
        exact (H.mem_iff r).2 hr }
  obtain ⟨ε, hε⟩ := ReciprocityTheory.PGsh.exists_eps (p := p) C NormedField.valuation O hv
  exact ⟨ε, isPrimitiveSystem_of_one hε⟩

/- English proof (translation)
Establish `H` using `isIntegers_padicComplex p`. Establish `i1 : Fact ¬IsUnit (p : 𝓞_ℂ_[p])` using `⟨IsIntegers.not_isUnit (p := p) H⟩`. Establish `i2 : IsAdicComplete (span {(p : 𝓞_ℂ_[p])}) 𝓞_ℂ_[p]` using `IsIntegers.isAdicComplete (p := p) H`. Take `⟨ε, hε⟩` from `exists_system p ℂ_[p] 𝓞_ℂ_[p] H`. Conclude with `⟨i1, i2, ε, hε, h p ℂ_[p] 𝓞_ℂ_[p] H ε hε⟩`.
-/
theorem at_padicComplex (h : PrismaticDieudonne) (p : ℕ) [Fact p.Prime] :
    ∃ (_ : Fact ¬IsUnit (p : 𝓞_ℂ_[p])) (_ : IsAdicComplete (span {(p : 𝓞_ℂ_[p])}) 𝓞_ℂ_[p])
      (ε : PreTilt 𝓞_ℂ_[p] p) (hε : IsPrimitiveSystem ε), PrismaticDieudonneAt hε := by
  have H := isIntegers_padicComplex p
  have i1 : Fact ¬IsUnit (p : 𝓞_ℂ_[p]) := ⟨IsIntegers.not_isUnit (p := p) H⟩
  have i2 : IsAdicComplete (span {(p : 𝓞_ℂ_[p])}) 𝓞_ℂ_[p] := IsIntegers.isAdicComplete (p := p) H
  obtain ⟨ε, hε⟩ := exists_system p ℂ_[p] 𝓞_ℂ_[p] H
  exact ⟨i1, i2, ε, hε, h p ℂ_[p] 𝓞_ℂ_[p] H ε hε⟩

section Mu

variable {O A : Type} [CommRing O] [CommRing A] [Bialgebra O A]

/- English proof (translation)
Rewrite using `[LinearMap.lTensor_tmul]`. Both sides reduce to the same expression.
-/
private theorem lTensor_rid_one_tmul_eq_one_tmul_rid (s : A →ₗ[O] O) (c : A ⊗[O] A) :
    LinearMap.lTensor A ((TensorProduct.rid O A).toLinearMap ∘ₗ s.lTensor A) (1 ⊗ₜ c) =
      1 ⊗ₜ TensorProduct.rid O A (s.lTensor A c) := by
  rw [LinearMap.lTensor_tmul]
  rfl

/- English proof (translation)
Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul u v => simp [TensorProduct.tmul_smul]`. Consider the case `add t₁ t₂ h₁ h₂ => rw [TensorProduct.add_tmul, map_add, map_add, h₁, h₂, smul_add]`.
-/
private theorem lTensor_rid_assoc_tmul_eq_smul (s : A →ₗ[O] O) (t : A ⊗[O] A) (y : A) :
    LinearMap.lTensor A ((TensorProduct.rid O A).toLinearMap ∘ₗ s.lTensor A)
      (TensorProduct.assoc O A A A (t ⊗ₜ y)) = s y • t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul u v => simp [TensorProduct.tmul_smul]
  | add t₁ t₂ h₁ h₂ => rw [TensorProduct.add_tmul, map_add, map_add, h₁, h₂, smul_add]

/- English proof (translation)
Proceed by induction on `c using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x y`. Rewrite using `[LinearMap.rTensor_tmul, lTensor_rid_assoc_tmul_eq_smul]`. Simplify using the standard rewrite rules.

Consider the case `add c₁ c₂ h₁ h₂ => simp only [map_add, h₁, h₂]`.
-/
private theorem lTensor_rid_assoc_rTensor_comul_eq_comul_rid (s : A →ₗ[O] O) (c : A ⊗[O] A) :
    LinearMap.lTensor A ((TensorProduct.rid O A).toLinearMap ∘ₗ s.lTensor A)
      (TensorProduct.assoc O A A A (comul.rTensor A c)) =
      comul (TensorProduct.rid O A (s.lTensor A c)) := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    rw [LinearMap.rTensor_tmul, lTensor_rid_assoc_tmul_eq_smul]
    simp
  | add c₁ c₂ h₁ h₂ => simp only [map_add, h₁, h₂]

/- English proof (translation)
Proceed by induction on `c using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x y`. Rewrite using `[LinearMap.lTensor_tmul, LinearMap.lTensor_tmul]`. Simplify using `only [LinearMap.comp_apply, LinearEquiv.coe_coe]`.

Rewrite using `[hs]`. Simplify using `[TensorProduct.tmul_smul, TensorProduct.smul_tmul']`. Consider the case `add c₁ c₂ h₁ h₂ => simp only [map_add, h₁, h₂, TensorProduct.add_tmul]`.
-/
private theorem lTensor_rid_assoc_lTensor_comul_eq_tmul_one (s : A →ₗ[O] O)
    (hs : ∀ a, TensorProduct.rid O A (s.lTensor A (comul a)) = s a • 1) (c : A ⊗[O] A) :
    LinearMap.lTensor A ((TensorProduct.rid O A).toLinearMap ∘ₗ s.lTensor A)
      (comul.lTensor A c) = TensorProduct.rid O A (s.lTensor A c) ⊗ₜ 1 := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    rw [LinearMap.lTensor_tmul, LinearMap.lTensor_tmul]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hs]
    simp [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  | add c₁ c₂ h₁ h₂ => simp only [map_add, h₁, h₂, TensorProduct.add_tmul]

/- English proof (translation)
Proceed by induction on `c using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x y => simp [h1]`. Consider the case `add c₁ c₂ h₁ h₂ => simp only [map_add, h₁, h₂]`.
-/
private theorem lTensor_rid_flip_one_eq_self_of_apply_one (s : A →ₗ[O] O) (h1 : s 1 = 1) (c : A ⊗[O] A) :
    LinearMap.lTensor A ((TensorProduct.rid O A).toLinearMap ∘ₗ s.lTensor A)
      (((TensorProduct.mk O A A).flip 1).lTensor A c) = c := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [h1]
  | add c₁ c₂ h₁ h₂ => simp only [map_add, h₁, h₂]

/- English proof (translation)
Use `⟨-(TensorProduct.rid O A (s.lTensor A c)), ?_⟩` and prove the remaining obligations. Establish `key` using `congrArg (LinearMap.lTensor A ((TensorProduct.rid O A).toLinearMap ∘ₗ s.lTensor A)) hc`. Rewrite `key` using `[map_zero, cobTwo_apply, map_sub, map_add, map_sub, lTensor_rid_one_tmul_eq_one_tmul_rid, lTensor_rid_assoc_rTensor_comul_eq_comul_rid, lTensor_rid_assoc_lTensor_comul_eq_tmul_one s hs, lTensor_rid_flip_one_eq_self_of_apply_one s h1, sub_eq_zero]`. Rewrite using `[map_neg, cobOne_apply]`. Use `Eq.trans ?_ key` and prove the remaining obligations.

Normalize the expressions using the abelian group laws.
-/
theorem exists_cobOne_of_integral (s : A →ₗ[O] O) (h1 : s 1 = 1)
    (hs : ∀ a, TensorProduct.rid O A (s.lTensor A (comul a)) = s a • 1)
    {c : A ⊗[O] A} (hc : cobTwo O A c = 0) : ∃ b, cobOne O A b = c := by
  refine ⟨-(TensorProduct.rid O A (s.lTensor A c)), ?_⟩
  have key := congrArg (LinearMap.lTensor A ((TensorProduct.rid O A).toLinearMap ∘ₗ s.lTensor A)) hc
  rw [map_zero, cobTwo_apply, map_sub, map_add, map_sub, lTensor_rid_one_tmul_eq_one_tmul_rid, lTensor_rid_assoc_rTensor_comul_eq_comul_rid,
    lTensor_rid_assoc_lTensor_comul_eq_tmul_one s hs, lTensor_rid_flip_one_eq_self_of_apply_one s h1, sub_eq_zero] at key
  rw [map_neg, cobOne_apply]
  refine Eq.trans ?_ key
  abel

variable {p : ℕ} [Fact p.Prime]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private theorem coeff_zero_one_eq_one (n : ℕ) :
    (Finsupp.lapply (0 : ZMod (p ^ n)) ∘ₗ (AddMonoidAlgebra.coeffLinearEquiv O).toLinearMap :
      (PDivGroup.mu p O).A n →ₗ[O] O) 1 = 1 := by
  simp

/- English proof (translation)
Proceed by induction on `a using AddMonoidAlgebra.induction_linear with`. Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [map_add, ha, hb, add_smul]`. Consider the case `single g r`. Distinguish the cases in `hg : g = 0`.

Substitute `hg` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[AddMonoidAlgebra.one_def, AddMonoidAlgebra.smul_single', mul_one]`. Simplify using `[hg]`.
-/
private theorem coeff_zero_lTensor_comul_eq_smul_one (n : ℕ) (a : (PDivGroup.mu p O).A n) :
    TensorProduct.rid O _ ((Finsupp.lapply (0 : ZMod (p ^ n)) ∘ₗ (AddMonoidAlgebra.coeffLinearEquiv O).toLinearMap :
      (PDivGroup.mu p O).A n →ₗ[O] O).lTensor _ (comul a)) =
      (Finsupp.lapply (0 : ZMod (p ^ n)) ∘ₗ (AddMonoidAlgebra.coeffLinearEquiv O).toLinearMap :
      (PDivGroup.mu p O).A n →ₗ[O] O) a • 1 := by
  induction a using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb, add_smul]
  | single g r =>
    by_cases hg : g = 0
    · subst hg
      simp
      rw [AddMonoidAlgebra.one_def, AddMonoidAlgebra.smul_single', mul_one]
    · simp [hg]

/- English proof (translation)
Establish `hb : ∀ c : (PDivGroup.mu p O).cocycles, ∀ n, ∃ b : (PDivGroup.mu p O).A n, cobOne O _ b = c.1 n` using `fun c n => exists_cobOne_of_integral (A := (PDivGroup.mu p O).A n) (Finsupp.lapply (0 : ZMod (p ^ n)) ∘ₗ (AddMonoidAlgebra.coeffLinearEquiv O).toLinearMap) (coeff_zero_one_eq_one n) (coeff_zero_lTensor_comul_eq_smul_one n) (mem_symCocycles.1 (c.2 n).1).1`. Establish `hsurj : ∀ c : (PDivGroup.mu p O).cocycles, c ∈ LinearMap.range (PDivGroup.mu p O).cob`. Introduce `c`. Use `choose b hb' using hb c`. Establish `hres : ∀ n, (PDivGroup.mu p O).res n (b (n + 1)) = b n`.

Introduce `n`. Rewrite using `[← sub_eq_zero]`. Apply `(PDivGroup.mu p O).eq_zero_of_cobOne_eq_zero hp n` to reduce the goal to its premises. Rewrite using `[map_sub, ← pullTwo_cobOne, hb', hb', (c.2 n).2, sub_self]`. Conclude with `⟨⟨b, hres⟩, Subtype.ext (funext fun n => hb' n)⟩`.

Use `⟨fun x y => ?_⟩` and prove the remaining obligations. Proceed by induction on `x using Submodule.Quotient.induction_on with`. Consider the case `H x`. Proceed by induction on `y using Submodule.Quotient.induction_on with`. Consider the case `H y`.

Conclude with `(Submodule.Quotient.eq _).2 (hsurj _)`.
-/
theorem subsingleton_vecExt_mu [IsDomain O] (hp : (p : O) ≠ 0) :
    Subsingleton (PDivGroup.mu p O).VecExt := by
  have hb : ∀ c : (PDivGroup.mu p O).cocycles, ∀ n,
      ∃ b : (PDivGroup.mu p O).A n, cobOne O _ b = c.1 n := fun c n =>
    exists_cobOne_of_integral (A := (PDivGroup.mu p O).A n)
      (Finsupp.lapply (0 : ZMod (p ^ n)) ∘ₗ (AddMonoidAlgebra.coeffLinearEquiv O).toLinearMap)
      (coeff_zero_one_eq_one n) (coeff_zero_lTensor_comul_eq_smul_one n) (mem_symCocycles.1 (c.2 n).1).1
  have hsurj : ∀ c : (PDivGroup.mu p O).cocycles, c ∈ LinearMap.range (PDivGroup.mu p O).cob := by
    intro c
    choose b hb' using hb c
    have hres : ∀ n, (PDivGroup.mu p O).res n (b (n + 1)) = b n := by
      intro n
      rw [← sub_eq_zero]
      apply (PDivGroup.mu p O).eq_zero_of_cobOne_eq_zero hp n
      rw [map_sub, ← pullTwo_cobOne, hb', hb', (c.2 n).2, sub_self]
    exact ⟨⟨b, hres⟩, Subtype.ext (funext fun n => hb' n)⟩
  refine ⟨fun x y => ?_⟩
  induction x using Submodule.Quotient.induction_on with
  | H x =>
  induction y using Submodule.Quotient.induction_on with
  | H y =>
  exact (Submodule.Quotient.eq _).2 (hsurj _)

/- English proof (translation)
Establish `hd` using `toSpanSingleton_dlogT_bijective p O`. Use `subsingleton_vecExt_mu hp` as an intermediate fact. Use `⟨((PDivGroup.mu p O).rigOfOmega_injective hp).comp hd.1, fun x => ?_⟩` and prove the remaining obligations. Take `⟨w, hw⟩` from `((PDivGroup.mu p O).exact_rigOfOmega_rigToExt x).1 (Subsingleton.elim _ _)`. Take `⟨a, rfl⟩` from `hd.2 w`.

Conclude with `⟨a, hw⟩`.
-/
theorem rigExt_mu_bijective [IsDomain O] [IsAdicComplete (span {(p : O)}) O] (hp : (p : O) ≠ 0) :
    Function.Bijective
      ((PDivGroup.mu p O).rigOfOmega ∘ₗ LinearMap.toSpanSingleton O _ (dlogT p O)) := by
  have hd := toSpanSingleton_dlogT_bijective p O
  have := subsingleton_vecExt_mu hp
  refine ⟨((PDivGroup.mu p O).rigOfOmega_injective hp).comp hd.1, fun x => ?_⟩
  obtain ⟨w, hw⟩ := ((PDivGroup.mu p O).exact_rigOfOmega_rigToExt x).1 (Subsingleton.elim _ _)
  obtain ⟨a, rfl⟩ := hd.2 w
  exact ⟨a, hw⟩

end Mu

end GlobalTheory.PrismModel
