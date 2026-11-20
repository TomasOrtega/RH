import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LengthEqKerAddRange

namespace GlobalTheory.HerbrandLength

open IsLocalRing

variable {A : Type} [CommRing A]

def Concl (b : A) (P : Finset (PrimeSpectrum A)) (M : Type) [AddCommGroup M] [Module A M] : Prop :=
  Module.length A (LinearMap.ker (LinearMap.lsmul A M b)) ≠ ⊤ ∧
  Module.length A (M ⧸ LinearMap.range (LinearMap.lsmul A M b)) =
    Module.length A (LinearMap.ker (LinearMap.lsmul A M b)) +
      ∑ p ∈ P, Module.length (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl M) * Module.length A (A ⧸ (p.asIdeal ⊔ Ideal.span {b}))

/- English proof (translation)
The claim follows from `Module.length_eq_add_of_exact (LocalizedModule.map p.primeCompl f) (LocalizedModule.map p.primeCompl g) (LocalizedModule.map_injective _ f hf) (LocalizedModule.map_surjective _ g hg) (LocalizedModule.map_exact _ f g H)`.
-/
theorem loc_exact (p : Ideal A) [p.IsPrime] {N M Q : Type} [AddCommGroup N] [Module A N]
    [AddCommGroup M] [Module A M] [AddCommGroup Q] [Module A Q] (f : N →ₗ[A] M) (g : M →ₗ[A] Q)
    (hf : Function.Injective f) (hg : Function.Surjective g) (H : Function.Exact f g) :
    Module.length (Localization.AtPrime p) (LocalizedModule p.primeCompl M) =
      Module.length (Localization.AtPrime p) (LocalizedModule p.primeCompl N) +
      Module.length (Localization.AtPrime p) (LocalizedModule p.primeCompl Q) :=
  Module.length_eq_add_of_exact (LocalizedModule.map p.primeCompl f)
    (LocalizedModule.map p.primeCompl g) (LocalizedModule.map_injective _ f hf)
    (LocalizedModule.map_surjective _ g hg) (LocalizedModule.map_exact _ f g H)

/- English proof (translation)
The claim follows from `Module.length_eq_zero_iff.2 ((IsLocalizedModule.subsingleton_iff p.primeCompl (LocalizedModule.mkLinearMap p.primeCompl M)).2 fun x => ⟨s, hs, hsM x⟩)`.
-/
theorem loc_zero_of_ann (p : Ideal A) [p.IsPrime] (M : Type) [AddCommGroup M] [Module A M]
    (s : A) (hs : s ∉ p) (hsM : ∀ x : M, s • x = 0) :
    Module.length (Localization.AtPrime p) (LocalizedModule p.primeCompl M) = 0 :=
  Module.length_eq_zero_iff.2 ((IsLocalizedModule.subsingleton_iff p.primeCompl
    (LocalizedModule.mkLinearMap p.primeCompl M)).2 fun x => ⟨s, hs, hsM x⟩)

/- English proof (translation)
Use `Module.length_eq_one_iff.2 (isSimpleModule_iff_toSpanSingleton_surjective.2 ⟨?_, ?_⟩)` and prove the remaining obligations. Rewrite using `[← not_subsingleton_iff_nontrivial, IsLocalizedModule.subsingleton_iff p.primeCompl (LocalizedModule.mkLinearMap p.primeCompl (A ⧸ p))]`. Introduce `h`. Take `⟨r, hr, hr0⟩` from `h 1`. Rewrite `hr0` using `[Algebra.smul_def, Ideal.Quotient.algebraMap_eq, mul_one, Ideal.Quotient.eq_zero_iff_mem]`.

Conclude with `hr hr0`. Introduce `x hx y`. Proceed by induction on `x using LocalizedModule.induction_on with`. Consider the case `h a s`. Proceed by induction on `y using LocalizedModule.induction_on with`.

Consider the case `h c t`. Take `⟨r, rfl⟩` from `Ideal.Quotient.mk_surjective a`. Take `⟨r', rfl⟩` from `Ideal.Quotient.mk_surjective c`. Establish `hr : r ∈ p.primeCompl`. Introduce `hrm`.

Apply `hx` to reduce the goal to its premises. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem.2 hrm, LocalizedModule.zero_mk]`. Use `⟨Localization.mk (r' * s) (⟨r, hr⟩ * t), ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.toSpanSingleton_apply, LocalizedModule.mk_smul_mk, LocalizedModule.mk_eq]`. Use `⟨1, ?_⟩` and prove the remaining obligations.

Simplify using `only [Submonoid.smul_def, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Submonoid.coe_mul, Submonoid.coe_one]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem loc_quot_self (p : Ideal A) [hp : p.IsPrime] :
    Module.length (Localization.AtPrime p) (LocalizedModule p.primeCompl (A ⧸ p)) = 1 := by
  refine Module.length_eq_one_iff.2 (isSimpleModule_iff_toSpanSingleton_surjective.2 ⟨?_, ?_⟩)
  · rw [← not_subsingleton_iff_nontrivial, IsLocalizedModule.subsingleton_iff p.primeCompl
      (LocalizedModule.mkLinearMap p.primeCompl (A ⧸ p))]
    intro h
    obtain ⟨r, hr, hr0⟩ := h 1
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, mul_one,
      Ideal.Quotient.eq_zero_iff_mem] at hr0
    exact hr hr0
  · intro x hx y
    induction x using LocalizedModule.induction_on with
    | h a s =>
    induction y using LocalizedModule.induction_on with
    | h c t =>
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨r', rfl⟩ := Ideal.Quotient.mk_surjective c
    have hr : r ∈ p.primeCompl := by
      intro hrm
      apply hx
      rw [Ideal.Quotient.eq_zero_iff_mem.2 hrm, LocalizedModule.zero_mk]
    refine ⟨Localization.mk (r' * s) (⟨r, hr⟩ * t), ?_⟩
    rw [LinearMap.toSpanSingleton_apply, LocalizedModule.mk_smul_mk, LocalizedModule.mk_eq]
    refine ⟨1, ?_⟩
    simp only [Submonoid.smul_def, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
      Submonoid.coe_mul, Submonoid.coe_one]
    congr 1
    ring

/- English proof (translation)
Establish `h1` using `Module.length_eq_add_of_exact (LinearMap.ker φ).subtype (LinearMap.ker φ).mkQ (Submodule.injective_subtype _) (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)`. Establish `h2` using `Module.length_eq_add_of_exact (LinearMap.range φ).subtype (LinearMap.range φ).mkQ (Submodule.injective_subtype _) (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)`. Rewrite `h1` using `[φ.quotKerEquivRange.length_eq]`. Establish `hR : Module.length A (LinearMap.range φ) ≠ ⊤` using `ne_top_of_le_ne_top h (le_self_add.trans_eq h2.symm)`. Conclude with `WithTop.add_left_cancel hR (h2.symm.trans (h1.trans (add_comm _ _)))`.
-/
theorem ker_eq_coker {M : Type} [AddCommGroup M] [Module A M] (φ : M →ₗ[A] M)
    (h : Module.length A M ≠ ⊤) :
    Module.length A (M ⧸ LinearMap.range φ) = Module.length A (LinearMap.ker φ) := by
  have h1 := Module.length_eq_add_of_exact (LinearMap.ker φ).subtype (LinearMap.ker φ).mkQ
    (Submodule.injective_subtype _) (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)
  have h2 := Module.length_eq_add_of_exact (LinearMap.range φ).subtype (LinearMap.range φ).mkQ
    (Submodule.injective_subtype _) (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)
  rw [φ.quotKerEquivRange.length_eq] at h1
  have hR : Module.length A (LinearMap.range φ) ≠ ⊤ :=
    ne_top_of_le_ne_top h (le_self_add.trans_eq h2.symm)
  exact WithTop.add_left_cancel hR (h2.symm.trans (h1.trans (add_comm _ _)))

/- English proof (translation)
Establish `hne : k₁ + k₃ ≠ ⊤` using `WithTop.add_ne_top.2 ⟨h₁, h₃⟩`. Establish `h : c₂ + (k₁ + k₃) = k₂ + (s₁ + s₃) + (k₁ + k₃)`. Rewrite using `[← add_assoc, e]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `WithTop.add_right_cancel hne h`.
-/
theorem enat_cancel {c₂ k₁ k₂ k₃ s₁ s₃ : ℕ∞} (h₁ : k₁ ≠ ⊤) (h₃ : k₃ ≠ ⊤)
    (e : c₂ + k₁ + k₃ = k₂ + (k₁ + s₁) + (k₃ + s₃)) : c₂ = k₂ + (s₁ + s₃) := by
  have hne : k₁ + k₃ ≠ ⊤ := WithTop.add_ne_top.2 ⟨h₁, h₃⟩
  have h : c₂ + (k₁ + k₃) = k₂ + (s₁ + s₃) + (k₁ + k₃) := by
    rw [← add_assoc, e]
    ring
  exact WithTop.add_right_cancel hne h

/- English proof (translation)
Take `⟨e, hle⟩` from `GlobalTheory.scalar_snake_length A M₁ M₂ M₃ f g hf hg hfg b`. Take `⟨k1, s1⟩` from `h₁`. Take `⟨k3, s3⟩` from `h₃`. Establish `hne` using `WithTop.add_ne_top.2 ⟨k1, k3⟩`. Use `⟨ne_top_of_le_ne_top hne hle, ?_⟩` and prove the remaining obligations.

Establish `hsum : ∑ p ∈ P, Module.length (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M₂) * Module.length A (A ⧸ (p.asIdeal ⊔ Ideal.span {b})) = (∑ p ∈ P, Module.length (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M₁) * Module.length A (A …`. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Rewrite using `[loc_exact p.asIdeal f g hf hg hfg, add_mul]`. Rewrite using `[hsum]`.

Rewrite `e` using `[s1, s3]`. Conclude with `enat_cancel k1 k3 e`.
-/
theorem concl_ext {M₁ M₂ M₃ : Type} [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
    [Module A M₁] [Module A M₂] [Module A M₃] (b : A) (P : Finset (PrimeSpectrum A))
    (f : M₁ →ₗ[A] M₂) (g : M₂ →ₗ[A] M₃) (hf : Function.Injective f)
    (hg : Function.Surjective g) (hfg : Function.Exact f g)
    (h₁ : Concl b P M₁) (h₃ : Concl b P M₃) : Concl b P M₂ := by
  obtain ⟨e, hle⟩ := GlobalTheory.scalar_snake_length A M₁ M₂ M₃ f g hf hg hfg b
  obtain ⟨k1, s1⟩ := h₁
  obtain ⟨k3, s3⟩ := h₃
  have hne := WithTop.add_ne_top.2 ⟨k1, k3⟩
  refine ⟨ne_top_of_le_ne_top hne hle, ?_⟩
  have hsum : ∑ p ∈ P, Module.length (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl M₂) * Module.length A (A ⧸ (p.asIdeal ⊔ Ideal.span {b})) =
      (∑ p ∈ P, Module.length (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl M₁) * Module.length A (A ⧸ (p.asIdeal ⊔ Ideal.span {b}))) +
      ∑ p ∈ P, Module.length (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl M₃) * Module.length A (A ⧸ (p.asIdeal ⊔ Ideal.span {b})) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [loc_exact p.asIdeal f g hf hg hfg, add_mul]
  rw [hsum]
  rw [s1, s3] at e
  exact enat_cancel k1 k3 e

/- English proof (translation)
Establish `hk : Module.length A (LinearMap.ker (LinearMap.lsmul A M b)) = 0` using `Module.length_eq_zero_iff.2 ⟨fun x y => Subtype.ext (Subsingleton.elim _ _)⟩`. Establish `hc : Module.length A (M ⧸ LinearMap.range (LinearMap.lsmul A M b)) = 0` using `Module.length_eq_zero_iff.2 ((Submodule.mkQ_surjective _).subsingleton)`. Use `⟨by rw [hk]; exact ENat.zero_ne_top, ?_⟩` and prove the remaining obligations. Rewrite using `[hk, hc, zero_add, eq_comm]`. Use `Finset.sum_eq_zero fun p _ => ?_` and prove the remaining obligations.

Rewrite using `[loc_zero_of_ann p.asIdeal M 1 (Ideal.IsPrime.ne_top' ∘ (Ideal.eq_top_of_isUnit_mem _ · isUnit_one)) (fun x => Subsingleton.elim _ _), zero_mul]`.
-/
theorem concl_subsingleton (b : A) (P : Finset (PrimeSpectrum A)) (M : Type) [AddCommGroup M]
    [Module A M] [Subsingleton M] : Concl b P M := by
  have hk : Module.length A (LinearMap.ker (LinearMap.lsmul A M b)) = 0 :=
    Module.length_eq_zero_iff.2 ⟨fun x y => Subtype.ext (Subsingleton.elim _ _)⟩
  have hc : Module.length A (M ⧸ LinearMap.range (LinearMap.lsmul A M b)) = 0 :=
    Module.length_eq_zero_iff.2 ((Submodule.mkQ_surjective _).subsingleton)
  refine ⟨by rw [hk]; exact ENat.zero_ne_top, ?_⟩
  rw [hk, hc, zero_add, eq_comm]
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [loc_zero_of_ann p.asIdeal M 1 (Ideal.IsPrime.ne_top' ∘ (Ideal.eq_top_of_isUnit_mem _ · isUnit_one))
    (fun x => Subsingleton.elim _ _), zero_mul]

/- English proof (translation)
The claim follows from `concl_ext (M₃ := PUnit) b P e.toLinearMap 0 e.injective (Function.surjective_to_subsingleton _) ((e.exact_zero_iff_surjective _).2 e.surjective) h (concl_subsingleton b P PUnit)`.
-/
theorem concl_equiv {M N : Type} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (b : A) (P : Finset (PrimeSpectrum A)) (e : M ≃ₗ[A] N) (h : Concl b P M) : Concl b P N :=
  concl_ext (M₃ := PUnit) b P e.toLinearMap 0 e.injective (Function.surjective_to_subsingleton _)
    ((e.exact_zero_iff_surjective _).2 e.surjective) h (concl_subsingleton b P PUnit)

/- English proof (translation)
Introduce `hpm`. Use `letI := Ideal.Quotient.field (maximalIdeal A)`. Establish `h0 : ringKrullDim (A ⧸ maximalIdeal A) = 0` using `ringKrullDim_eq_zero_of_field (A ⧸ maximalIdeal A)`. Rewrite `h0` using `[← hpm, h]`. Conclude with `one_ne_zero h0`.
-/
theorem ne_max [IsLocalRing A] (p : PrimeSpectrum A) (h : ringKrullDim (A ⧸ p.asIdeal) = 1) :
    p.asIdeal ≠ maximalIdeal A := by
  intro hpm
  letI := Ideal.Quotient.field (maximalIdeal A)
  have h0 : ringKrullDim (A ⧸ maximalIdeal A) = 0 := ringKrullDim_eq_zero_of_field (A ⧸ maximalIdeal A)
  rw [← hpm, h] at h0
  exact one_ne_zero h0

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Establish `hlt : p.asIdeal < q.asIdeal` using `lt_of_le_of_ne hle (fun h => hne (PrimeSpectrum.ext h))`. Establish `hqm : q.asIdeal < maximalIdeal A` using `lt_of_le_of_ne (IsLocalRing.le_maximalIdeal q.isPrime.ne_top) (ne_max q hq)`. Set `a : PrimeSpectrum.zeroLocus (R` to `A) p.asIdeal := ⟨p, fun _ h => h⟩`. Set `c : PrimeSpectrum.zeroLocus (R` to `A) p.asIdeal := ⟨q, fun _ h => hle h⟩`.

Set `d : PrimeSpectrum.zeroLocus (R` to `A) p.asIdeal := ⟨⟨maximalIdeal A, inferInstance⟩, fun _ h => (hle.trans hqm.le) h⟩`. Establish `hac : a < c` using `Subtype.mk_lt_mk.2 ((PrimeSpectrum.asIdeal_lt_asIdeal _ _).1 hlt)`. Establish `hcd : c < d` using `Subtype.mk_lt_mk.2 ((PrimeSpectrum.asIdeal_lt_asIdeal _ _).1 hqm)`. Apply the tactic sequence `let s : LTSeries (PrimeSpectrum.zeroLocus (R := A) p.asIdeal) := ⟨2, ![a, c, d], fun i => by fin_cases i <;> first | exact hac | exact hcd | simp [hac, hcd]⟩`. Establish `hs` using `Order.LTSeries.length_le_krullDim s`.

Rewrite `hs` using `[← ringKrullDim_quotient, hp]`. Establish `h2 : s.length = 2` using `rfl`. Rewrite `hs` using `[h2]`. Conclude with `absurd hs (by decide)`.
-/
theorem eq_of_le [IsLocalRing A] (p q : PrimeSpectrum A) (hp : ringKrullDim (A ⧸ p.asIdeal) = 1)
    (hq : ringKrullDim (A ⧸ q.asIdeal) = 1) (hle : p.asIdeal ≤ q.asIdeal) : p = q := by
  by_contra hne
  have hlt : p.asIdeal < q.asIdeal := lt_of_le_of_ne hle (fun h => hne (PrimeSpectrum.ext h))
  have hqm : q.asIdeal < maximalIdeal A :=
    lt_of_le_of_ne (IsLocalRing.le_maximalIdeal q.isPrime.ne_top) (ne_max q hq)
  let a : PrimeSpectrum.zeroLocus (R := A) p.asIdeal := ⟨p, fun _ h => h⟩
  let c : PrimeSpectrum.zeroLocus (R := A) p.asIdeal := ⟨q, fun _ h => hle h⟩
  let d : PrimeSpectrum.zeroLocus (R := A) p.asIdeal :=
    ⟨⟨maximalIdeal A, inferInstance⟩, fun _ h => (hle.trans hqm.le) h⟩
  have hac : a < c := Subtype.mk_lt_mk.2 ((PrimeSpectrum.asIdeal_lt_asIdeal _ _).1 hlt)
  have hcd : c < d := Subtype.mk_lt_mk.2 ((PrimeSpectrum.asIdeal_lt_asIdeal _ _).1 hqm)
  let s : LTSeries (PrimeSpectrum.zeroLocus (R := A) p.asIdeal) :=
    ⟨2, ![a, c, d], fun i => by fin_cases i <;> first | exact hac | exact hcd | simp [hac, hcd]⟩
  have hs := Order.LTSeries.length_le_krullDim s
  rw [← ringKrullDim_quotient, hp] at hs
  have h2 : s.length = 2 := rfl
  rw [h2] at hs
  exact absurd hs (by decide)

/- English proof (translation)
Establish `hb : b ∉ p.asIdeal` using `(hP p hpP).2`. Establish `hker : LinearMap.ker (LinearMap.lsmul A (A ⧸ p.asIdeal) b) = ⊥`. Rewrite using `[LinearMap.ker_eq_bot']`. Introduce `x hx`. Rewrite `hx` using `[LinearMap.lsmul_apply, Algebra.smul_def, Ideal.Quotient.algebraMap_eq]`.

Conclude with `(mul_eq_zero.1 hx).resolve_left (fun h => hb (Ideal.Quotient.eq_zero_iff_mem.1 h))`. Establish `hrange : LinearMap.range (LinearMap.lsmul A (A ⧸ p.asIdeal) b) = Submodule.map p.asIdeal.mkQ (Ideal.span {b})`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩`.

Take `⟨a, rfl⟩` from `Submodule.mkQ_surjective _ y`. Conclude with `⟨b * a, Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self b), by rw [LinearMap.lsmul_apply, ← LinearMap.map_smul, smul_eq_mul]⟩`. Introduce and unpack `⟨a, ha, rfl⟩`. Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.1 ha`. Conclude with `⟨p.asIdeal.mkQ c, by rw [LinearMap.lsmul_apply, ← LinearMap.map_smul, smul_eq_mul, mul_comm]⟩`.

Establish `hcok : Module.length A ((A ⧸ p.asIdeal) ⧸ LinearMap.range (LinearMap.lsmul A (A ⧸ p.asIdeal) b)) = Module.length A (A ⧸ (p.asIdeal ⊔ Ideal.span {b}))` using `((Submodule.quotEquivOfEq _ _ hrange).trans (Submodule.quotientQuotientEquivQuotientSup p.asIdeal (Ideal.span {b}))).length_eq`. Establish `hk0 : Module.length A (LinearMap.ker (LinearMap.lsmul A (A ⧸ p.asIdeal) b)) = 0`. Rewrite using `[hker]`. Conclude with `Module.length_eq_zero_iff.2 inferInstance`. Use `⟨by rw [hk0]; exact ENat.zero_ne_top, ?_⟩` and prove the remaining obligations.

Rewrite using `[hcok, hk0, zero_add, Finset.sum_eq_single p, loc_quot_self, one_mul]`. Introduce `q hq hqp`. Establish `hnle : ¬ p.asIdeal ≤ q.asIdeal` using `fun h => hqp (eq_of_le p q (hP p hpP).1 (hP q hq).1 h).symm`. Take `⟨s, hsp, hsq⟩` from `SetLike.not_le_iff_exists.1 hnle`. Rewrite using `[loc_zero_of_ann q.asIdeal _ s hsq (fun x => ?_), zero_mul]`.

Take `⟨y, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Rewrite using `[Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `Ideal.mul_mem_right _ _ hsp`. Introduce `h`. Conclude with `absurd hpP h`.
-/
theorem concl_prime [IsLocalRing A] (b : A) (P : Finset (PrimeSpectrum A))
    (hP : ∀ p ∈ P, ringKrullDim (A ⧸ p.asIdeal) = 1 ∧ b ∉ p.asIdeal) (p : PrimeSpectrum A)
    (hpP : p ∈ P) : Concl b P (A ⧸ p.asIdeal) := by
  have hb : b ∉ p.asIdeal := (hP p hpP).2
  have hker : LinearMap.ker (LinearMap.lsmul A (A ⧸ p.asIdeal) b) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    rw [LinearMap.lsmul_apply, Algebra.smul_def, Ideal.Quotient.algebraMap_eq] at hx
    exact (mul_eq_zero.1 hx).resolve_left (fun h => hb (Ideal.Quotient.eq_zero_iff_mem.1 h))
  have hrange : LinearMap.range (LinearMap.lsmul A (A ⧸ p.asIdeal) b) =
      Submodule.map p.asIdeal.mkQ (Ideal.span {b}) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective _ y
      exact ⟨b * a, Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self b),
        by rw [LinearMap.lsmul_apply, ← LinearMap.map_smul, smul_eq_mul]⟩
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      exact ⟨p.asIdeal.mkQ c, by rw [LinearMap.lsmul_apply, ← LinearMap.map_smul, smul_eq_mul, mul_comm]⟩
  have hcok : Module.length A ((A ⧸ p.asIdeal) ⧸ LinearMap.range (LinearMap.lsmul A (A ⧸ p.asIdeal) b)) =
      Module.length A (A ⧸ (p.asIdeal ⊔ Ideal.span {b})) :=
    ((Submodule.quotEquivOfEq _ _ hrange).trans
      (Submodule.quotientQuotientEquivQuotientSup p.asIdeal (Ideal.span {b}))).length_eq
  have hk0 : Module.length A (LinearMap.ker (LinearMap.lsmul A (A ⧸ p.asIdeal) b)) = 0 := by
    rw [hker]; exact Module.length_eq_zero_iff.2 inferInstance
  refine ⟨by rw [hk0]; exact ENat.zero_ne_top, ?_⟩
  rw [hcok, hk0, zero_add, Finset.sum_eq_single p, loc_quot_self, one_mul]
  · intro q hq hqp
    have hnle : ¬ p.asIdeal ≤ q.asIdeal := fun h => hqp (eq_of_le p q (hP p hpP).1 (hP q hq).1 h).symm
    obtain ⟨s, hsp, hsq⟩ := SetLike.not_le_iff_exists.1 hnle
    rw [loc_zero_of_ann q.asIdeal _ s hsq (fun x => ?_), zero_mul]
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_right _ _ hsp
  · intro h; exact absurd hpP h

/- English proof (translation)
Establish `hlen : Module.length A (A ⧸ maximalIdeal A) = 1` using `Module.length_eq_one_iff.2 (isSimpleModule_iff_isCoatom.2 (inferInstance : (maximalIdeal A).IsMaximal).out)`. Establish `hfin : Module.length A (A ⧸ maximalIdeal A) ≠ ⊤` using `by rw [hlen]; exact ENat.one_ne_top`. Use `⟨ne_top_of_le_ne_top hfin (Module.length_le_of_injective (LinearMap.ker _).subtype (Submodule.injective_subtype _)), ?_⟩` and prove the remaining obligations. Rewrite using `[ker_eq_coker _ hfin, Finset.sum_eq_zero, add_zero]`. Introduce `p hp`.

Establish `hnle : ¬ maximalIdeal A ≤ p.asIdeal` using `fun h => ne_max p (hP p hp).1 (le_antisymm (IsLocalRing.le_maximalIdeal p.isPrime.ne_top) h)`. Take `⟨s, hsm, hsp⟩` from `SetLike.not_le_iff_exists.1 hnle`. Rewrite using `[loc_zero_of_ann p.asIdeal _ s hsp (fun x => ?_), zero_mul]`. Take `⟨y, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Rewrite using `[Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]`.

Conclude with `Ideal.mul_mem_right _ _ hsm`.
-/
theorem concl_max [IsLocalRing A] (b : A) (P : Finset (PrimeSpectrum A))
    (hP : ∀ p ∈ P, ringKrullDim (A ⧸ p.asIdeal) = 1 ∧ b ∉ p.asIdeal) :
    Concl b P (A ⧸ maximalIdeal A) := by
  have hlen : Module.length A (A ⧸ maximalIdeal A) = 1 :=
    Module.length_eq_one_iff.2
      (isSimpleModule_iff_isCoatom.2 (inferInstance : (maximalIdeal A).IsMaximal).out)
  have hfin : Module.length A (A ⧸ maximalIdeal A) ≠ ⊤ := by rw [hlen]; exact ENat.one_ne_top
  refine ⟨ne_top_of_le_ne_top hfin
    (Module.length_le_of_injective (LinearMap.ker _).subtype (Submodule.injective_subtype _)), ?_⟩
  rw [ker_eq_coker _ hfin, Finset.sum_eq_zero, add_zero]
  intro p hp
  have hnle : ¬ maximalIdeal A ≤ p.asIdeal := fun h =>
    ne_max p (hP p hp).1 (le_antisymm (IsLocalRing.le_maximalIdeal p.isPrime.ne_top) h)
  obtain ⟨s, hsm, hsp⟩ := SetLike.not_le_iff_exists.1 hnle
  rw [loc_zero_of_ann p.asIdeal _ s hsp (fun x => ?_), zero_mul]
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mul_mem_right _ _ hsm

end GlobalTheory.HerbrandLength

open GlobalTheory.HerbrandLength in

/- English proof (translation)
Introduce `A _ _ _ b P hP M _ _ hfin hM`. Use `revert hM`. Proceed by induction on `hfin using IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime A with`. Consider the case `subsingleton N => intro _`. Conclude with `concl_subsingleton b P N`.

Consider the case `quotient N p e`. Introduce `hN`. Establish `hpN : p ∈ Module.support A N`. Rewrite using `[e.support_eq, Module.mem_support_iff_of_finite]`. Introduce `r hr`.

Establish `h1` using `Module.mem_annihilator.1 hr 1`. Rewrite `h1` using `[Algebra.smul_def, Ideal.Quotient.algebraMap_eq, mul_one, Ideal.Quotient.eq_zero_iff_mem]`. Then use the resulting hypothesis. Break down `hN p hpN with hpP | hpm` into its components or cases. Conclude with `concl_equiv b P e.symm (concl_prime b P hP p hpP)`. Conclude with `concl_equiv b P ((Submodule.quotEquivOfEq _ _ hpm).symm.trans e.symm) (concl_max b P hP)`.

Consider the case `exact N₁ N₂ N₃ f g hf hg hfg h₁ h₃`. Introduce `hN`. Conclude with `concl_ext b P f g hf hg hfg (h₁ fun q hq => hN q (Module.support_subset_of_injective f hf hq)) (h₃ fun q hq => hN q (Module.support_subset_of_surjective g hg hq))`.
-/
theorem GlobalTheory.length_coker_lsmul_eq_length_ker_add_sum : ∀ (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] (b : A) (P : Finset (PrimeSpectrum A)), (∀ p ∈ P, ringKrullDim (A ⧸ p.asIdeal) = 1 ∧ b ∉ p.asIdeal) → ∀ (M : Type) [AddCommGroup M] [Module A M] [Module.Finite A M], (∀ p ∈ Module.support A M, p ∈ P ∨ p.asIdeal = IsLocalRing.maximalIdeal A) → Module.length A (LinearMap.ker (LinearMap.lsmul A M b)) ≠ ⊤ ∧ Module.length A (M ⧸ LinearMap.range (LinearMap.lsmul A M b)) = Module.length A (LinearMap.ker (LinearMap.lsmul A M b)) + ∑ p ∈ P, Module.length (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M) * Module.length A (A ⧸ (p.asIdeal ⊔ Ideal.span {b})) := by
  intro A _ _ _ b P hP M _ _ hfin hM
  revert hM
  induction hfin using IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime A with
  | subsingleton N => intro _; exact concl_subsingleton b P N
  | quotient N p e =>
    intro hN
    have hpN : p ∈ Module.support A N := by
      rw [e.support_eq, Module.mem_support_iff_of_finite]
      intro r hr
      have h1 := Module.mem_annihilator.1 hr 1
      rwa [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, mul_one,
        Ideal.Quotient.eq_zero_iff_mem] at h1
    rcases hN p hpN with hpP | hpm
    · exact concl_equiv b P e.symm (concl_prime b P hP p hpP)
    · exact concl_equiv b P ((Submodule.quotEquivOfEq _ _ hpm).symm.trans e.symm) (concl_max b P hP)
  | exact N₁ N₂ N₃ f g hf hg hfg h₁ h₃ =>
    intro hN
    exact concl_ext b P f g hf hg hfg
      (h₁ fun q hq => hN q (Module.support_subset_of_injective f hf hq))
      (h₃ fun q hq => hN q (Module.support_subset_of_surjective g hg hq))
