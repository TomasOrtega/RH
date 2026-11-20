import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemCycAlgOfPow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTowerUnionZetaDerivationModIntegralClosure
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CyclotomicDvdOfAevalPrimitiveRootInertiaFixedStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.RecOne GlobalTheory.AlmostEt
open scoped Matrix NNReal

noncomputable section

namespace GlobalTheory.RecOne.ZetaDer

open Polynomial

section Gen
variable {R S M : Type} [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M] [Module S M]

/- English proof (translation)
Set `e : R[X] → S` to `fun Q => aeval z Q`. Set `D : S → M` to `fun x => aeval z (derivative (Function.invFun e x)) • μ`. Establish `key : ∀ f : R[X], D (aeval z f) = aeval z (derivative f) • μ`. Introduce `f`. Establish `h1 : e (Function.invFun e (e f)) = e f` using `Function.invFun_eq ⟨f, rfl⟩`.

Establish `h2` using `hwd (Function.invFun e (e f) - f) (by rw [map_sub]; exact sub_eq_zero.2 h1)`. Rewrite `h2` using `[derivative_sub, map_sub, sub_smul, sub_eq_zero]`. Conclude with `h2`. Establish `hm : ∀ x ∈ Algebra.adjoin R {z}, ∃ f : R[X], aeval z f = x`. Introduce `x hx`.

Rewrite `hx` using `[Algebra.adjoin_singleton_eq_range_aeval]`. Conclude with `hx`. Use `⟨D, ⟨?_, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `x hx y hy`. Take `⟨f, rfl⟩` from `hm x hx`.

Take `⟨g, rfl⟩` from `hm y hy`. Rewrite using `[← map_add, key, key, key, derivative_add, map_add, add_smul]`. Introduce `x hx y hy`. Take `⟨f, rfl⟩` from `hm x hx`. Take `⟨g, rfl⟩` from `hm y hy`.

Rewrite using `[← map_mul, key, key, key, derivative_mul, map_add, add_smul, map_mul, map_mul, smul_smul, smul_smul, add_comm, mul_comm (aeval z (derivative f))]`. Introduce `a`. Establish `: algebraMap R S a = aeval z (C a)` using `by simp`. Rewrite using `[this, key]`. Simplify using the standard rewrite rules.

Establish `: z = aeval z (X : R[X])` using `by simp conv_lhs => rw [this]`. Rewrite using `[key]`. Simplify using the standard rewrite rules.
-/
theorem exists_der_one (z : S) (μ : M)
    (hwd : ∀ Q : R[X], aeval z Q = 0 → aeval z (derivative Q) • μ = 0) :
    ∃ D : S → M, IsDerOn (Algebra.adjoin R {z}) D ∧ D z = μ := by
  classical
  let e : R[X] → S := fun Q => aeval z Q
  let D : S → M := fun x => aeval z (derivative (Function.invFun e x)) • μ
  have key : ∀ f : R[X], D (aeval z f) = aeval z (derivative f) • μ := by
    intro f
    have h1 : e (Function.invFun e (e f)) = e f := Function.invFun_eq ⟨f, rfl⟩
    have h2 := hwd (Function.invFun e (e f) - f) (by rw [map_sub]; exact sub_eq_zero.2 h1)
    rw [derivative_sub, map_sub, sub_smul, sub_eq_zero] at h2
    exact h2
  have hm : ∀ x ∈ Algebra.adjoin R {z}, ∃ f : R[X], aeval z f = x := by
    intro x hx
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hx
    exact hx
  refine ⟨D, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro x hx y hy
    obtain ⟨f, rfl⟩ := hm x hx
    obtain ⟨g, rfl⟩ := hm y hy
    rw [← map_add, key, key, key, derivative_add, map_add, add_smul]
  · intro x hx y hy
    obtain ⟨f, rfl⟩ := hm x hx
    obtain ⟨g, rfl⟩ := hm y hy
    rw [← map_mul, key, key, key, derivative_mul, map_add, add_smul, map_mul, map_mul, smul_smul, smul_smul,
      add_comm, mul_comm (aeval z (derivative f))]
  · intro a
    have : algebraMap R S a = aeval z (C a) := by simp
    rw [this, key]
    simp
  · have : z = aeval z (X : R[X]) := by simp
    conv_lhs => rw [this]
    rw [key]
    simp

end Gen

variable {Ω : Type} [Field Ω]

/- English proof (translation)
Rewrite using `[← Submodule.Quotient.mk_smul]`. Both sides reduce to the same expression.
-/
theorem frac_smul_mk {A : ValuationSubring Ω} (s : A) (x : Ω) :
    s • (Submodule.Quotient.mk x : FracA A) = Submodule.Quotient.mk ((s : Ω) * x) := by
  rw [← Submodule.Quotient.mk_smul]; rfl

/- English proof (translation)
Rewrite using `[Submodule.Quotient.mk_eq_zero]`. Conclude with `⟨s, rfl⟩`.
-/
theorem frac_mk_eq_zero {A : ValuationSubring Ω} (s : A) :
    (Submodule.Quotient.mk (s : Ω) : FracA A) = 0 := by
  rw [Submodule.Quotient.mk_eq_zero]
  exact ⟨s, rfl⟩

/- English proof (translation)
Establish `hp1 : 1 < p` using `hp.out.one_lt`. Establish `hpos : 0 < p ^ (m + 1)` using `pow_pos hp.out.pos _`. Establish `hp0 : (p : Ω) ≠ 0` using `by exact_mod_cast hp.out.ne_zero`. Establish `hzA : IsPrimitiveRoot z (p ^ (m + 1))` using `IsPrimitiveRoot.of_map_of_injective (f := A.subtype) hz Subtype.val_injective`. Establish `hξ : IsPrimitiveRoot ((z : Ω) ^ p ^ m) p`.

Use `hz.pow_of_dvd (pow_ne_zero m hp.out.ne_zero) (pow_dvd_pow p (Nat.le_succ m))` as an intermediate fact. Simplify `this` using `[pow_succ, Nat.mul_div_cancel_left _ (pow_pos hp.out.pos m)]`. Use `set gS : A := ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range i, (z ^ p ^ m) ^ j`. Establish `hgval : (gS : Ω) = ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range i, ((z : Ω) ^ p ^ m) ^ j`. Simplify using `[gS]`.

Establish `hg : (gS : Ω) * ((z : Ω) ^ p ^ m - 1) = - p`. Rewrite using `[hgval, Finset.sum_mul]`. Repeatedly rewrite using `[geom_sum_mul]`. Rewrite using `[Finset.sum_sub_distrib, hξ.geom_sum_eq_zero hp1]`. Simplify using the standard rewrite rules.

Establish `hroot : aeval z (cyclotomic (p ^ (m + 1)) R) = 0`. Rewrite using `[aeval_def, eval₂_eq_eval_map, map_cyclotomic]`. Conclude with `hzA.isRoot_cyclotomic hpos`. Establish `hid` using `congrArg (fun f => aeval z (derivative f)) (cyclotomic_prime_pow_mul_X_pow_sub_one R p m)`. Simplify using `only [derivative_mul, derivative_sub, derivative_X_pow, derivative_one, map_add, map_mul, map_sub, hroot, zero_mul, add_zero, sub_zero] at hid`.

Rewrite using `[frac_smul_mk]`. Use `set F := aeval z (derivative (cyclotomic (p ^ (m + 1)) R))`. Establish `hζ1 : (z : Ω) ^ p ^ (m + 1) = 1` using `hz.pow_eq_one`. Establish `hF : (F : Ω) * ((z : Ω) ^ p ^ m - 1) * z = (p : Ω) ^ (m + 1)`. Establish `h2 : F * (z ^ p ^ m - 1) = (p : A) ^ (m + 1) * z ^ (p ^ (m + 1) - 1)`.

Simplify `hid` using `[map_natCast]`. Establish `h3 : (F : Ω) * ((z : Ω) ^ p ^ m - 1) = (p : Ω) ^ (m + 1) * (z : Ω) ^ (p ^ (m + 1) - 1)`. Use `congrArg (A.subtype) h2` as an intermediate fact. Simplify using `using this`. Rewrite using `[h3, mul_assoc, pow_sub_one_mul (pow_ne_zero _ hp.out.ne_zero), hζ1, mul_one]`.

Establish `hξ1 : (z : Ω) ^ p ^ m - 1 ≠ 0` using `sub_ne_zero.2 (hξ.ne_one hp1)`. Establish `key : (F : Ω) * ((z : Ω) * p / (p : Ω) ^ (m + 1)) = ((-gS : A) : Ω)`. Apply `mul_right_cancel₀ hξ1` to reduce the goal to its premises. Use `push_cast`. Rewrite using `[neg_mul, hg, neg_neg]`.

Establish `hpm : (p : Ω) ^ (m + 1) ≠ 0` using `pow_ne_zero _ hp0`. Rewrite using `[div_eq_mul_inv]`. Take the linear combination `((p : Ω) * ((p : Ω) ^ (m + 1))⁻¹) * hF + (p : Ω) * mul_inv_cancel₀ hpm`. Rewrite using `[key, frac_mk_eq_zero]`.
-/
theorem cyc_rel [CharZero Ω] {p : ℕ} [hp : Fact p.Prime] {A : ValuationSubring Ω} {R : Type} [CommRing R] [Algebra R A]
    (m : ℕ) (z : A) (hz : IsPrimitiveRoot (z : Ω) (p ^ (m + 1))) :
    (aeval z (derivative (cyclotomic (p ^ (m + 1)) R))) •
      (Submodule.Quotient.mk ((z : Ω) * p / (p : Ω) ^ (m + 1)) : FracA A) = 0 := by
  have hp1 : 1 < p := hp.out.one_lt
  have hpos : 0 < p ^ (m + 1) := pow_pos hp.out.pos _
  have hp0 : (p : Ω) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hzA : IsPrimitiveRoot z (p ^ (m + 1)) :=
    IsPrimitiveRoot.of_map_of_injective (f := A.subtype) hz Subtype.val_injective
  have hξ : IsPrimitiveRoot ((z : Ω) ^ p ^ m) p := by
    have := hz.pow_of_dvd (pow_ne_zero m hp.out.ne_zero) (pow_dvd_pow p (Nat.le_succ m))
    simpa [pow_succ, Nat.mul_div_cancel_left _ (pow_pos hp.out.pos m)] using this
  set gS : A := ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range i, (z ^ p ^ m) ^ j
  have hgval : (gS : Ω) = ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range i, ((z : Ω) ^ p ^ m) ^ j := by
    simp [gS]
  have hg : (gS : Ω) * ((z : Ω) ^ p ^ m - 1) = - p := by
    rw [hgval, Finset.sum_mul]
    simp_rw [geom_sum_mul]
    rw [Finset.sum_sub_distrib, hξ.geom_sum_eq_zero hp1]
    simp
  have hroot : aeval z (cyclotomic (p ^ (m + 1)) R) = 0 := by
    rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
    exact hzA.isRoot_cyclotomic hpos
  have hid := congrArg (fun f => aeval z (derivative f))
    (cyclotomic_prime_pow_mul_X_pow_sub_one R p m)
  simp only [derivative_mul, derivative_sub, derivative_X_pow, derivative_one, map_add, map_mul,
    map_sub, hroot, zero_mul, add_zero, sub_zero] at hid
  rw [frac_smul_mk]
  set F := aeval z (derivative (cyclotomic (p ^ (m + 1)) R))
  have hζ1 : (z : Ω) ^ p ^ (m + 1) = 1 := hz.pow_eq_one
  have hF : (F : Ω) * ((z : Ω) ^ p ^ m - 1) * z = (p : Ω) ^ (m + 1) := by
    have h2 : F * (z ^ p ^ m - 1) = (p : A) ^ (m + 1) * z ^ (p ^ (m + 1) - 1) := by
      simpa [map_natCast] using hid
    have h3 : (F : Ω) * ((z : Ω) ^ p ^ m - 1) = (p : Ω) ^ (m + 1) * (z : Ω) ^ (p ^ (m + 1) - 1) := by
      have := congrArg (A.subtype) h2
      simpa using this
    rw [h3, mul_assoc, pow_sub_one_mul (pow_ne_zero _ hp.out.ne_zero), hζ1, mul_one]
  have hξ1 : (z : Ω) ^ p ^ m - 1 ≠ 0 := sub_ne_zero.2 (hξ.ne_one hp1)
  have key : (F : Ω) * ((z : Ω) * p / (p : Ω) ^ (m + 1)) = ((-gS : A) : Ω) := by
    apply mul_right_cancel₀ hξ1
    push_cast
    rw [neg_mul, hg, neg_neg]
    have hpm : (p : Ω) ^ (m + 1) ≠ 0 := pow_ne_zero _ hp0
    rw [div_eq_mul_inv]
    linear_combination ((p : Ω) * ((p : Ω) ^ (m + 1))⁻¹) * hF + (p : Ω) * mul_inv_cancel₀ hpm
  rw [key, frac_mk_eq_zero]

/- English proof (translation)
Establish `hpos : 0 < p ^ (n + 1)` using `pow_pos hp.out.pos _`. Use `haveI : NeZero (p ^ (n + 1)) := ⟨hpos.ne'⟩`. Use `haveI : NeZero (p ^ n) := ⟨(pow_pos hp.out.pos _).ne'⟩`. Use `haveI : NeZero ((p ^ (n + 1) : ℕ) : Ω) := ⟨by exact_mod_cast hpos.ne'⟩`. Take `⟨ζ, hζ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot Ω (p ^ (n + 1))`.

Establish `h1 : IsPrimitiveRoot (ζ ^ p) (p ^ n)` using `hζ.pow hpos (by rw [pow_succ'])`. Take `⟨i, -, hi, hiz⟩` from `h1.isPrimitiveRoot_iff.1 hz`. Choose the witnesses or unpack the hypotheses as in `⟨j, hj, hjz⟩ : ∃ j : ℕ, j.Coprime (p ^ (n + 1)) ∧ (ζ ^ p) ^ j = z := by`. Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Use `⟨1, Nat.coprime_one_left _, ?_⟩` and prove the remaining obligations.

Establish `a1 : ζ ^ p = 1` using `by simpa using h1.pow_eq_one`. Establish `a2 : (z : Ω) = 1` using `by simpa using hz.pow_eq_one`. Rewrite using `[a1, a2, one_pow]`. Use `⟨i, ?_, hiz⟩` and prove the remaining obligations. Rewrite `hi` using `[Nat.coprime_pow_right_iff hn]`.

Conclude with `hi.pow_right _`. Establish `hw : IsPrimitiveRoot (ζ ^ j) (p ^ (n + 1))` using `hζ.pow_of_coprime j hj`. Establish `hmem : ζ ^ j ∈ A` using `mem_of_pow_mem A hpos.ne' (by rw [hw.pow_eq_one]; exact A.one_mem)`. Use `⟨⟨ζ ^ j, hmem⟩, hw, Subtype.ext ?_⟩` and prove the remaining obligations. Rewrite using `[← hjz]`.

Use `show (ζ ^ j) ^ p = _`. Rewrite using `[← pow_mul, ← pow_mul, mul_comm]`.
-/
theorem exists_root_succ [CharZero Ω] [IsAlgClosed Ω] {p : ℕ} [hp : Fact p.Prime] (A : ValuationSubring Ω)
    (n : ℕ) (z : A) (hz : IsPrimitiveRoot (z : Ω) (p ^ n)) :
    ∃ w : A, IsPrimitiveRoot (w : Ω) (p ^ (n + 1)) ∧ w ^ p = z := by
  have hpos : 0 < p ^ (n + 1) := pow_pos hp.out.pos _
  haveI : NeZero (p ^ (n + 1)) := ⟨hpos.ne'⟩
  haveI : NeZero (p ^ n) := ⟨(pow_pos hp.out.pos _).ne'⟩
  haveI : NeZero ((p ^ (n + 1) : ℕ) : Ω) := ⟨by exact_mod_cast hpos.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (p ^ (n + 1))
  have h1 : IsPrimitiveRoot (ζ ^ p) (p ^ n) := hζ.pow hpos (by rw [pow_succ'])
  obtain ⟨i, -, hi, hiz⟩ := h1.isPrimitiveRoot_iff.1 hz

  obtain ⟨j, hj, hjz⟩ : ∃ j : ℕ, j.Coprime (p ^ (n + 1)) ∧ (ζ ^ p) ^ j = z := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · refine ⟨1, Nat.coprime_one_left _, ?_⟩
      have a1 : ζ ^ p = 1 := by simpa using h1.pow_eq_one
      have a2 : (z : Ω) = 1 := by simpa using hz.pow_eq_one
      rw [a1, a2, one_pow]
    · refine ⟨i, ?_, hiz⟩
      rw [Nat.coprime_pow_right_iff hn] at hi
      exact hi.pow_right _
  have hw : IsPrimitiveRoot (ζ ^ j) (p ^ (n + 1)) := hζ.pow_of_coprime j hj
  have hmem : ζ ^ j ∈ A := mem_of_pow_mem A hpos.ne' (by rw [hw.pow_eq_one]; exact A.one_mem)
  refine ⟨⟨ζ ^ j, hmem⟩, hw, Subtype.ext ?_⟩
  rw [← hjz]
  show (ζ ^ j) ^ p = _
  rw [← pow_mul, ← pow_mul, mul_comm]

/- English proof (translation)
Use `choose f hf hf' using exists_root_succ (p := p) A`. Set `s : (k : ℕ) → {w : A // IsPrimitiveRoot (w : Ω) (p ^ (N + k))}` to `fun k => Nat.rec (motive := fun k => {w : A // IsPrimitiveRoot (w : Ω) (p ^ (N + k))}) ⟨z, hz⟩ (fun k w => ⟨f (N + k) w.1 w.2, hf (N + k) w.1 w.2⟩) k`. Conclude with `⟨fun k => (s k).1, rfl, fun k => (s k).2, fun k => hf' (N + k) (s k).1 (s k).2⟩`.
-/
theorem exists_seq [CharZero Ω] [IsAlgClosed Ω] {p : ℕ} [hp : Fact p.Prime] (A : ValuationSubring Ω)
    (N : ℕ) (z : A) (hz : IsPrimitiveRoot (z : Ω) (p ^ N)) :
    ∃ zs : ℕ → A, zs 0 = z ∧ (∀ k, IsPrimitiveRoot (zs k : Ω) (p ^ (N + k))) ∧ ∀ k, zs (k + 1) ^ p = zs k := by
  choose f hf hf' using exists_root_succ (p := p) A
  let s : (k : ℕ) → {w : A // IsPrimitiveRoot (w : Ω) (p ^ (N + k))} := fun k =>
    Nat.rec (motive := fun k => {w : A // IsPrimitiveRoot (w : Ω) (p ^ (N + k))}) ⟨z, hz⟩
      (fun k w => ⟨f (N + k) w.1 w.2, hf (N + k) w.1 w.2⟩) k
  exact ⟨fun k => (s k).1, rfl, fun k => (s k).2, fun k => hf' (N + k) (s k).1 (s k).2⟩

end GlobalTheory.RecOne.ZetaDer

namespace GlobalTheory.RecOne

open ZetaDer Polynomial

/- English proof (translation)
Introduce `p hp Ω _ _ hc A hO N z hz`. Use `haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective`. Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ`. Establish `hp0 : (p : Ω) ≠ 0` using `by exact_mod_cast hp.out.ne_zero`. Take `⟨zs, hz0, hprim, hpow⟩` from `exists_seq A N z hz`.

Set `B : ℕ → Subalgebra (fixA A) A` to `fun m => Algebra.adjoin (fixA A) {zs (m + 1)}`. Establish `hmem1 : ∀ m, zs (m + 1) ∈ B m` using `fun m => Algebra.subset_adjoin (Set.mem_singleton _)`. Establish `hmem0 : ∀ m, zs m ∈ B m` using `fun m => by rw [← hpow m]; exact pow_mem (hmem1 m) _`. Establish `hle1 : ∀ m, B m ≤ B (m + 1)` using `fun m => Algebra.adjoin_le (Set.singleton_subset_iff.2 (hmem0 (m + 1)))`. Establish `hlev : ∀ m : ℕ, ∃ D : A → FracA A, IsDerOn (B m) D ∧ D (zs (m + 1)) = Submodule.Quotient.mk ((zs (m + 1) : Ω) * p / (p : Ω) ^ (N + m + 1))`.

Introduce `m`. Use `exists_der_one (zs (m + 1)) _ fun Q hQ => ?_` and prove the remaining obligations. Take `⟨R, rfl⟩` from `GlobalTheory.T.cyclotomic_dvd_of_aeval_primitive_root_inertia_fixed p Ω A hO (N + m + 1) (zs (m + 1)) (hprim (m + 1)) Q hQ`. Establish `hzA : IsPrimitiveRoot (zs (m + 1)) (p ^ (N + m + 1))` using `IsPrimitiveRoot.of_map_of_injective (f := A.subtype) (hprim (m + 1)) Subtype.val_injective`. Establish `hroot : aeval (zs (m + 1)) (cyclotomic (p ^ (N + m + 1)) (fixA A)) = 0`.

Rewrite using `[aeval_def, eval₂_eq_eval_map, map_cyclotomic]`. Conclude with `hzA.isRoot_cyclotomic (pow_pos hp.out.pos _)`. Rewrite using `[derivative_mul, map_add, map_mul, map_mul, hroot, zero_mul, add_zero, mul_comm, mul_smul, cyc_rel (N + m) (zs (m + 1)) (hprim (m + 1)), smul_zero]`. Use `choose D hD hDz using hlev`. Establish `hval : ∀ m, D m (zs m) = Submodule.Quotient.mk ((zs m : Ω) * p / (p : Ω) ^ (N + m))`.

Introduce `m`. Establish `hc1 : ((zs m : A) : Ω) = (zs (m + 1) : Ω) ^ p` using `by rw [← hpow m]; rfl`. Rewrite using `[hc1]`. Use `conv_lhs => rw [← hpow m]`. Rewrite using `[(hD m).pow_der (hmem1 m) hp.out.pos, hDz m, ZetaDer.frac_smul_mk]`.

Use `congr 1`. Use `push_cast`. Rewrite using `[← pow_sub_one_mul hp.out.ne_zero (zs (m + 1) : Ω)]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Establish `hcompat : ∀ m, ∀ x ∈ B m, D (m + 1) x = D m x`. Introduce `m`. Use `IsDerOn.eq_on_adjoin (s := {zs (m + 1)}) ((hD (m + 1)).mono' (hle1 m)) (hD m) ?_` and prove the remaining obligations. Introduce `x hx`. Rewrite using `[Set.mem_singleton_iff.1 hx, hval (m + 1), hDz m]`.

Both sides reduce to the same expression. Establish `hmono : Monotone B` using `monotone_nat_of_le_succ hle1`. Take `⟨D', hD', hD'eq⟩` from `isDerOn_iSup_glue (fixA A) A (FracA A) B hmono D hD hcompat`. Establish `hle : cycAlg p A ≤ ⨆ m, B m`. Use `Algebra.adjoin_le ?_` and prove the remaining obligations.

Introduce and unpack `x ⟨n, hx⟩`. Use `haveI : NeZero (p ^ (N + n)) := ⟨(pow_pos hp.out.pos _).ne'⟩`. Establish `hzA : IsPrimitiveRoot (zs n) (p ^ (N + n))` using `IsPrimitiveRoot.of_map_of_injective (f := A.subtype) (hprim n) Subtype.val_injective`. Take `⟨i, -, rfl⟩` from `hzA.eq_pow_of_pow_eq_one (ξ := x) (by rw [pow_add, mul_comm, pow_mul, hx, one_pow])`. Conclude with `(le_iSup B n) (pow_mem (hmem0 n) i)`.

Use `⟨D', hD'.mono' hle, ?_⟩` and prove the remaining obligations. Rewrite using `[← hz0, hD'eq 0 _ (hmem0 0), hval 0]`. Both sides reduce to the same expression.
-/
theorem zeta_derivation_cyc : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (A : ValuationSubring Ω), OverL l A → ∀ (N : ℕ) (z : A), IsPrimitiveRoot (z : Ω) (l ^ N) →
    ∃ D : A → FracA A, IsDerOn (cycAlg l A) D ∧
      D z = Submodule.Quotient.mk ((z : Ω) * (l : Ω) / (l : Ω) ^ N) := by
  intro p hp Ω _ _ hc A hO N z hz
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hp0 : (p : Ω) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  obtain ⟨zs, hz0, hprim, hpow⟩ := exists_seq A N z hz
  let B : ℕ → Subalgebra (fixA A) A := fun m => Algebra.adjoin (fixA A) {zs (m + 1)}
  have hmem1 : ∀ m, zs (m + 1) ∈ B m := fun m => Algebra.subset_adjoin (Set.mem_singleton _)
  have hmem0 : ∀ m, zs m ∈ B m := fun m => by rw [← hpow m]; exact pow_mem (hmem1 m) _
  have hle1 : ∀ m, B m ≤ B (m + 1) := fun m =>
    Algebra.adjoin_le (Set.singleton_subset_iff.2 (hmem0 (m + 1)))
  have hlev : ∀ m : ℕ, ∃ D : A → FracA A, IsDerOn (B m) D ∧
      D (zs (m + 1)) = Submodule.Quotient.mk ((zs (m + 1) : Ω) * p / (p : Ω) ^ (N + m + 1)) := by
    intro m
    refine exists_der_one (zs (m + 1)) _ fun Q hQ => ?_
    obtain ⟨R, rfl⟩ := GlobalTheory.T.cyclotomic_dvd_of_aeval_primitive_root_inertia_fixed p Ω A hO (N + m + 1) (zs (m + 1)) (hprim (m + 1)) Q hQ
    have hzA : IsPrimitiveRoot (zs (m + 1)) (p ^ (N + m + 1)) :=
      IsPrimitiveRoot.of_map_of_injective (f := A.subtype) (hprim (m + 1)) Subtype.val_injective
    have hroot : aeval (zs (m + 1)) (cyclotomic (p ^ (N + m + 1)) (fixA A)) = 0 := by
      rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
      exact hzA.isRoot_cyclotomic (pow_pos hp.out.pos _)
    rw [derivative_mul, map_add, map_mul, map_mul, hroot, zero_mul, add_zero, mul_comm, mul_smul,
      cyc_rel (N + m) (zs (m + 1)) (hprim (m + 1)), smul_zero]
  choose D hD hDz using hlev
  have hval : ∀ m, D m (zs m) = Submodule.Quotient.mk ((zs m : Ω) * p / (p : Ω) ^ (N + m)) := by
    intro m
    have hc1 : ((zs m : A) : Ω) = (zs (m + 1) : Ω) ^ p := by rw [← hpow m]; rfl
    rw [hc1]
    conv_lhs => rw [← hpow m]
    rw [(hD m).pow_der (hmem1 m) hp.out.pos, hDz m, ZetaDer.frac_smul_mk]
    congr 1
    push_cast
    rw [← pow_sub_one_mul hp.out.ne_zero (zs (m + 1) : Ω)]
    field_simp
    ring
  have hcompat : ∀ m, ∀ x ∈ B m, D (m + 1) x = D m x := by
    intro m
    refine IsDerOn.eq_on_adjoin (s := {zs (m + 1)}) ((hD (m + 1)).mono' (hle1 m)) (hD m) ?_
    intro x hx
    rw [Set.mem_singleton_iff.1 hx, hval (m + 1), hDz m]
    rfl
  have hmono : Monotone B := monotone_nat_of_le_succ hle1
  obtain ⟨D', hD', hD'eq⟩ := isDerOn_iSup_glue (fixA A) A (FracA A) B hmono D hD hcompat
  have hle : cycAlg p A ≤ ⨆ m, B m := by
    refine Algebra.adjoin_le ?_
    rintro x ⟨n, hx⟩
    haveI : NeZero (p ^ (N + n)) := ⟨(pow_pos hp.out.pos _).ne'⟩
    have hzA : IsPrimitiveRoot (zs n) (p ^ (N + n)) :=
      IsPrimitiveRoot.of_map_of_injective (f := A.subtype) (hprim n) Subtype.val_injective
    obtain ⟨i, -, rfl⟩ := hzA.eq_pow_of_pow_eq_one (ξ := x) (by rw [pow_add, mul_comm, pow_mul, hx, one_pow])
    exact (le_iSup B n) (pow_mem (hmem0 n) i)
  refine ⟨D', hD'.mono' hle, ?_⟩
  rw [← hz0, hD'eq 0 _ (hmem0 0), hval 0]
  rfl

end GlobalTheory.RecOne
