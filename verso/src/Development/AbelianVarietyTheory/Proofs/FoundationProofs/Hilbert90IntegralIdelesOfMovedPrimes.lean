import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsDual
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseOneAddPreservingAdelicCompletion
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.AfsplitB

noncomputable section

namespace GlobalTheory.NormSum.VacInt

open Matrix TensorProduct NumberField IsDedekindDomain Formalism.UG Formalism.UG.P
open scoped Pointwise

section Local

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Establish `hmax : (Ideal.span {(q : ℤ)}).IsMaximal` using `(Ideal.span_singleton_prime (by exact_mod_cast hq.ne_zero)).2 (Nat.prime_iff_prime_int.1 hq) |>.isMaximal (by simpa using hq.ne_zero)`. Establish `hov : ∀ R : Ideal (𝓞 E), R.IsPrime → (q : 𝓞 E) ∈ R → R.LiesOver (Ideal.span {(q : ℤ)})`. Introduce `R hR hqR`. Use `⟨hmax.eq_of_le (Ideal.IsPrime.under ℤ R).ne_top ?_⟩` and prove the remaining obligations. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff]`.

Use `show algebraMap ℤ (𝓞 E) (q : ℤ) ∈ R`. Simplify using `using hqR`. Use `haveI := hov P hP hqP`. Use `haveI := hov Q hQ hqQ`. Take `⟨g, rfl⟩` from `Ideal.exists_smul_eq_of_isGaloisGroup (Ideal.span {(q : ℤ)}) P Q (E ≃ₐ[ℚ] E)`.

Introduce `h'`. Rewrite `h'` using `[smul_smul, hc, mul_smul]`. Conclude with `h (smul_left_cancel g h')`.
-/
theorem moves_all [IsGalois ℚ E] (c : E ≃ₐ[ℚ] E) (hc : ∀ g : E ≃ₐ[ℚ] E, c * g = g * c) {q : ℕ} (hq : q.Prime)
    {P Q : Ideal (𝓞 E)} (hP : P.IsPrime) (hQ : Q.IsPrime) (hqP : (q : 𝓞 E) ∈ P) (hqQ : (q : 𝓞 E) ∈ Q)
    (h : c • P ≠ P) : c • Q ≠ Q := by
  have hmax : (Ideal.span {(q : ℤ)}).IsMaximal :=
    (Ideal.span_singleton_prime (by exact_mod_cast hq.ne_zero)).2 (Nat.prime_iff_prime_int.1 hq)
      |>.isMaximal (by simpa using hq.ne_zero)
  have hov : ∀ R : Ideal (𝓞 E), R.IsPrime → (q : 𝓞 E) ∈ R → R.LiesOver (Ideal.span {(q : ℤ)}) := by
    intro R hR hqR
    refine ⟨hmax.eq_of_le (Ideal.IsPrime.under ℤ R).ne_top ?_⟩
    rw [Ideal.span_le, Set.singleton_subset_iff]
    show algebraMap ℤ (𝓞 E) (q : ℤ) ∈ R
    simpa using hqR
  haveI := hov P hP hqP
  haveI := hov Q hQ hqQ
  obtain ⟨g, rfl⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (Ideal.span {(q : ℤ)}) P Q (E ≃ₐ[ℚ] E)
  intro h'
  rw [smul_smul, hc, mul_smul] at h'
  exact h (smul_left_cancel g h')

/- English proof (translation)
Establish `hq0 : (q : 𝓞 E) ≠ 0` using `Nat.cast_ne_zero.2 hq`. Establish `hI : Ideal.span {(q : 𝓞 E)} ≠ ⊥` using `by simpa using hq`. Establish `hinv : ∀ x : 𝓞 E, c • c • x = x` using `fun x => by rw [smul_smul, hcc, one_smul]`. Establish `hinvI : ∀ x : Ideal (𝓞 E), c • c • x = x` using `fun x => by rw [smul_smul, hcc, one_smul]`. Establish `hmem : ∀ (P : Ideal (𝓞 E)) (x : 𝓞 E), c • x ∈ P ↔ x ∈ c • P`.

Introduce `P x`. Use `conv_lhs => rw [← hinvI P]`. Conclude with `Ideal.smul_mem_pointwise_smul_iff`. Establish `hcq : c • (q : 𝓞 E) = q` using `map_natCast (MulSemiringAction.toRingHom _ (𝓞 E) c) q`. Take `⟨o, -⟩` from `exists_wellOrder (Ideal (𝓞 E))`.

Set `lt : Ideal (𝓞 E) → Ideal (𝓞 E) → Prop` to `o.lt`. Set `T : Finset (HeightOneSpectrum (𝓞 E))` to `(Ideal.finite_factors hI).toFinset`. Establish `hT : ∀ P : Ideal (𝓞 E), (hP : P.IsPrime) → (hqP : (q : 𝓞 E) ∈ P) → ∃ v ∈ T, v.asIdeal = P`. Introduce `P hP hqP`. Use `⟨⟨P, hP, fun h0 => hq0 (by simpa [h0] using hqP)⟩, ?_, rfl⟩` and prove the remaining obligations.

Simplify using `[T, Ideal.dvd_span_singleton, hqP]`. Take `⟨a, ha⟩` from `IsDedekindDomain.exists_forall_sub_mem_ideal (s := T) (fun v => v.asIdeal) (fun _ => 1) (fun v _ => v.prime) (fun v _ w _ hvw h => hvw (HeightOneSpectrum.ext h)) (fun v => if lt v.1.asIdeal (c • v.1.asIdeal) then 1 else 0)`. Establish `ha' : ∀ P : Ideal (𝓞 E), P.IsPrime → (q : 𝓞 E) ∈ P → a - (if lt P (c • P) then 1 else 0) ∈ P`. Introduce `P hP hqP`. Take `⟨v, hv, rfl⟩` from `hT P hP hqP`.

Simplify using `using ha v hv`. Establish `key : ∀ P : Ideal (𝓞 E), P.IsPrime → (q : 𝓞 E) ∈ P → (a - 1 ∈ P ∧ c • a ∈ P) ∨ (a ∈ P ∧ c • a - 1 ∈ P)`. Introduce `P hP hqP`. Establish `h1` using `ha' P hP hqP`. Establish `h2` using `ha' (c • P) (Ideal.IsPrime.smul c) (by rw [← hmem, hcq]; exact hqP)`.

Rewrite `h2` using `[hinvI, ← hmem, smul_sub]`. Break down `@lt_trichotomy _ o P (c • P) with hl | hl | hl` into its components or cases. Use `left`. Rewrite `h1` using `[if_pos hl]`. Rewrite `h2` using `[if_neg (@not_lt_of_gt _ o.toPreorder _ _ hl), smul_zero, sub_zero]`.

Conclude with `⟨h1, h2⟩`. Conclude with `absurd hl.symm (h P hP hqP)`. Use `right`. Rewrite `h1` using `[if_neg (@not_lt_of_gt _ o.toPreorder _ _ hl), sub_zero]`. Rewrite `h2` using `[if_pos hl, smul_one]`.

Conclude with `⟨h1, h2⟩`. Establish `hrad : a * c • a ∈ (Ideal.span {(q : 𝓞 E)}).radical`. Rewrite using `[Ideal.radical_eq_sInf, Submodule.mem_sInf]`. Introduce and unpack `P ⟨hle, hP⟩`. Break down `key P hP (hle (Ideal.mem_span_singleton_self _)) with h | h` into its components or cases.

Conclude with `Ideal.mul_mem_left _ _ h.2`. Conclude with `Ideal.mul_mem_right _ _ h.1`. Take `⟨n, hn⟩` from `hrad`. Take `⟨r, hr⟩` from `Ideal.mem_span_singleton.1 (Ideal.pow_mem_of_pow_mem _ hn (Nat.le_succ n))`. Establish `hcop : Ideal.span {(q : 𝓞 E), a ^ (n + 1) + (c • a) ^ (n + 1)} = ⊤`.

Assume the negation of the conclusion as `hne`. Take `⟨P, hP, hle⟩` from `Ideal.exists_le_maximal _ hne`. Establish `hqP : (q : 𝓞 E) ∈ P` using `hle (Ideal.subset_span (by simp))`. Establish `ht : a ^ (n + 1) + (c • a) ^ (n + 1) ∈ P` using `hle (Ideal.subset_span (by simp))`. Establish `aux : ∀ x y : 𝓞 E, x - 1 ∈ P → y ∈ P → x ^ (n + 1) + y ^ (n + 1) ∈ P → False`.

Introduce `x y hx hy hxy`. Establish `h1 : x ^ (n + 1) ∈ P`. Use `P.sub_mem hxy (P.pow_mem_of_mem hy _ (Nat.succ_pos n))` as an intermediate fact. Simplify using `using this`. Establish `h2` using `P.sub_mem (hP.isPrime.mem_of_pow_mem _ h1) hx`.

Conclude with `hP.ne_top (P.eq_top_iff_one.2 (by simpa using h2))`. Break down `key P hP.isPrime hqP with h | h` into its components or cases. Conclude with `aux _ _ h.1 h.2 ht`. Conclude with `aux _ _ h.2 h.1 (by rwa [add_comm])`. Take `⟨u, b, hub⟩` from `Ideal.mem_span_pair.1 (hcop ▸ Submodule.mem_top : (1 : 𝓞 E) ∈ _)`.

Establish `hub'` using `congrArg (fun x => c • x) hub`. Simplify using `only [smul_add, smul_mul', smul_pow', hinv, hcq, smul_one] at hub'`. Use `⟨a ^ (n + 1) * b, r * b * c • b, -u + (c • a) ^ (n + 1) * (u * c • b - (c • u) * b), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_mul', smul_pow']`. Rewrite `hr` using `[mul_pow, Nat.succ_eq_add_one]`.

Take the linear combination `(b * c • b) * hr`. Rewrite using `[smul_mul', smul_pow']`. Take the linear combination `hub + (c • a) ^ (n + 1) * (b * hub' - c • b * hub)`.
-/
theorem exists_half (c : E ≃ₐ[ℚ] E) (hcc : c * c = 1) {q : ℕ} (hq : q ≠ 0)
    (h : ∀ P : Ideal (𝓞 E), P.IsPrime → (q : 𝓞 E) ∈ P → c • P ≠ P) :
    ∃ a r s : 𝓞 E, a * c • a = q * r ∧ a + c • a = 1 + q * s := by
  classical
  have hq0 : (q : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 hq
  have hI : Ideal.span {(q : 𝓞 E)} ≠ ⊥ := by simpa using hq
  have hinv : ∀ x : 𝓞 E, c • c • x = x := fun x => by rw [smul_smul, hcc, one_smul]
  have hinvI : ∀ x : Ideal (𝓞 E), c • c • x = x := fun x => by rw [smul_smul, hcc, one_smul]
  have hmem : ∀ (P : Ideal (𝓞 E)) (x : 𝓞 E), c • x ∈ P ↔ x ∈ c • P := by
    intro P x
    conv_lhs => rw [← hinvI P]
    exact Ideal.smul_mem_pointwise_smul_iff
  have hcq : c • (q : 𝓞 E) = q := map_natCast (MulSemiringAction.toRingHom _ (𝓞 E) c) q
  obtain ⟨o, -⟩ := exists_wellOrder (Ideal (𝓞 E))
  let lt : Ideal (𝓞 E) → Ideal (𝓞 E) → Prop := o.lt
  let T : Finset (HeightOneSpectrum (𝓞 E)) := (Ideal.finite_factors hI).toFinset
  have hT : ∀ P : Ideal (𝓞 E), (hP : P.IsPrime) → (hqP : (q : 𝓞 E) ∈ P) →
      ∃ v ∈ T, v.asIdeal = P := by
    intro P hP hqP
    refine ⟨⟨P, hP, fun h0 => hq0 (by simpa [h0] using hqP)⟩, ?_, rfl⟩
    simp [T, Ideal.dvd_span_singleton, hqP]
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := T) (fun v => v.asIdeal) (fun _ => 1)
    (fun v _ => v.prime) (fun v _ w _ hvw h => hvw (HeightOneSpectrum.ext h))
    (fun v => if lt v.1.asIdeal (c • v.1.asIdeal) then 1 else 0)
  have ha' : ∀ P : Ideal (𝓞 E), P.IsPrime → (q : 𝓞 E) ∈ P →
      a - (if lt P (c • P) then 1 else 0) ∈ P := by
    intro P hP hqP
    obtain ⟨v, hv, rfl⟩ := hT P hP hqP
    simpa using ha v hv
  have key : ∀ P : Ideal (𝓞 E), P.IsPrime → (q : 𝓞 E) ∈ P →
      (a - 1 ∈ P ∧ c • a ∈ P) ∨ (a ∈ P ∧ c • a - 1 ∈ P) := by
    intro P hP hqP
    have h1 := ha' P hP hqP
    have h2 := ha' (c • P) (Ideal.IsPrime.smul c) (by rw [← hmem, hcq]; exact hqP)
    rw [hinvI, ← hmem, smul_sub] at h2
    rcases @lt_trichotomy _ o P (c • P) with hl | hl | hl
    · left
      rw [if_pos hl] at h1
      rw [if_neg (@not_lt_of_gt _ o.toPreorder _ _ hl), smul_zero, sub_zero] at h2
      exact ⟨h1, h2⟩
    · exact absurd hl.symm (h P hP hqP)
    · right
      rw [if_neg (@not_lt_of_gt _ o.toPreorder _ _ hl), sub_zero] at h1
      rw [if_pos hl, smul_one] at h2
      exact ⟨h1, h2⟩
  have hrad : a * c • a ∈ (Ideal.span {(q : 𝓞 E)}).radical := by
    rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
    rintro P ⟨hle, hP⟩
    rcases key P hP (hle (Ideal.mem_span_singleton_self _)) with h | h
    · exact Ideal.mul_mem_left _ _ h.2
    · exact Ideal.mul_mem_right _ _ h.1
  obtain ⟨n, hn⟩ := hrad
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.1 (Ideal.pow_mem_of_pow_mem _ hn (Nat.le_succ n))
  have hcop : Ideal.span {(q : 𝓞 E), a ^ (n + 1) + (c • a) ^ (n + 1)} = ⊤ := by
    by_contra hne
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
    have hqP : (q : 𝓞 E) ∈ P := hle (Ideal.subset_span (by simp))
    have ht : a ^ (n + 1) + (c • a) ^ (n + 1) ∈ P := hle (Ideal.subset_span (by simp))
    have aux : ∀ x y : 𝓞 E, x - 1 ∈ P → y ∈ P → x ^ (n + 1) + y ^ (n + 1) ∈ P → False := by
      intro x y hx hy hxy
      have h1 : x ^ (n + 1) ∈ P := by
        have := P.sub_mem hxy (P.pow_mem_of_mem hy _ (Nat.succ_pos n))
        simpa using this
      have h2 := P.sub_mem (hP.isPrime.mem_of_pow_mem _ h1) hx
      exact hP.ne_top (P.eq_top_iff_one.2 (by simpa using h2))
    rcases key P hP.isPrime hqP with h | h
    · exact aux _ _ h.1 h.2 ht
    · exact aux _ _ h.2 h.1 (by rwa [add_comm])
  obtain ⟨u, b, hub⟩ := Ideal.mem_span_pair.1 (hcop ▸ Submodule.mem_top : (1 : 𝓞 E) ∈ _)
  have hub' := congrArg (fun x => c • x) hub
  simp only [smul_add, smul_mul', smul_pow', hinv, hcq, smul_one] at hub'
  refine ⟨a ^ (n + 1) * b, r * b * c • b, -u + (c • a) ^ (n + 1) * (u * c • b - (c • u) * b), ?_, ?_⟩
  · rw [smul_mul', smul_pow']
    rw [mul_pow, Nat.succ_eq_add_one] at hr
    linear_combination (b * c • b) * hr
  · rw [smul_mul', smul_pow']
    linear_combination hub + (c • a) ^ (n + 1) * (b * hub' - c • b * hub)

end Local

section Adelic

local notation "𝔸" => FiniteAdeleRing (𝓞 ℚ) ℚ

def pr (v : HeightOneSpectrum (𝓞 ℚ)) : ℕ := Rat.HeightOneSpectrum.natGenerator v

/- English proof (translation)
The claim follows from `Rat.HeightOneSpectrum.prime_natGenerator v`.
-/
theorem pr_prime (v : HeightOneSpectrum (𝓞 ℚ)) : (pr v).Prime := Rat.HeightOneSpectrum.prime_natGenerator v

/- English proof (translation)
Rewrite using `[pr, Rat.HeightOneSpectrum.natGenerator_dvd_iff, ← map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) n, Ideal.apply_mem_of_equiv_iff]`.
-/
theorem pr_dvd_iff (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) : pr v ∣ n ↔ (n : 𝓞 ℚ) ∈ v.asIdeal := by
  rw [pr, Rat.HeightOneSpectrum.natGenerator_dvd_iff, ← map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) n,
    Ideal.apply_mem_of_equiv_iff]

/- English proof (translation)
Rewrite `h` using `[pr_dvd_iff]`. Establish `h1` using `(v.valuation_eq_one_iff_notMem (K := ℚ)).mpr h`. Establish `h2` using `v.valuedAdicCompletion_eq_valuation' (K := ℚ) ((n : ℕ) : ℚ)`. Establish `h3 : (algebraMap ℚ (v.adicCompletion ℚ)) ((n : ℕ) : ℚ) = ((n : ℕ) : v.adicCompletion ℚ)` using `map_natCast _ _`. Rewrite using `[← h3]`.

Establish `h4 : (((n : ℕ) : 𝓞 ℚ) : ℚ) = ((n : ℕ) : ℚ)` using `map_natCast (algebraMap (𝓞 ℚ) ℚ) _`. Conclude with `h2.trans (h4 ▸ h1)`.
-/
theorem val_natCast_eq_one (v : HeightOneSpectrum (𝓞 ℚ)) {n : ℕ} (h : ¬ pr v ∣ n) :
    Valued.v ((n : ℕ) : v.adicCompletion ℚ) = 1 := by
  rw [pr_dvd_iff] at h
  have h1 := (v.valuation_eq_one_iff_notMem (K := ℚ)).mpr h
  have h2 := v.valuedAdicCompletion_eq_valuation' (K := ℚ) ((n : ℕ) : ℚ)
  have h3 : (algebraMap ℚ (v.adicCompletion ℚ)) ((n : ℕ) : ℚ) =
    ((n : ℕ) : v.adicCompletion ℚ) := map_natCast _ _
  rw [← h3]
  have h4 : (((n : ℕ) : 𝓞 ℚ) : ℚ) = ((n : ℕ) : ℚ) :=
    map_natCast (algebraMap (𝓞 ℚ) ℚ) _
  exact h2.trans (h4 ▸ h1)

def mkInt (f : ∀ v : HeightOneSpectrum (𝓞 ℚ), v.adicCompletion ℚ) (h : ∀ v, f v ∈ v.adicCompletionIntegers ℚ) : 𝔸 :=
  ⟨f, Filter.Eventually.of_forall h⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mkInt_apply (f h v) : mkInt f h v = f v := rfl

/- English proof (translation)
The claim follows from `h`.
-/
theorem mkInt_mem (f h) : mkInt f h ∈ intAd ℚ := h

variable {E : Type} [Field E] [NumberField E]

local notation "𝒜" => E ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "𝒮" => tensInt (F := ℚ) (FiniteAdeleRing (𝓞 ℚ) ℚ) (intOE E) (intAd ℚ)

/- English proof (translation)
The claim follows from `sub_eq_zero.1 (afsplit_inj _ fun v => by rw [map_sub, h v, sub_self])`.
-/
theorem ext_prV {x y : 𝒜} (h : ∀ v, prV (E := E) v x = prV (E := E) v y) : x = y :=
  sub_eq_zero.1 (afsplit_inj _ fun v => by rw [map_sub, h v, sub_self])

/- English proof (translation)
The claim follows from `DFunLike.congr_fun (afsplit_prV_comp_sigR σ v) x`.
-/
theorem prV_sig (σ : E →ₐ[ℚ] E) (v : HeightOneSpectrum (𝓞 ℚ)) (x : 𝒜) :
    prV (E := E) v (sigR σ 𝔸 x) = sigR σ (v.adicCompletion ℚ) (prV (E := E) v x) :=
  DFunLike.congr_fun (afsplit_prV_comp_sigR σ v) x

/- English proof (translation)
Use `levelaf_tmul_mem (E := E) 1 hy` as an intermediate fact. Rewrite `this` using `[map_one]`. Then use the resulting hypothesis.
-/
theorem one_tmul_mem {y : 𝔸} (hy : y ∈ intAd ℚ) : (1 : E) ⊗ₜ[ℚ] y ∈ 𝒮 := by
  have := levelaf_tmul_mem (E := E) 1 hy
  rwa [map_one] at this

/- English proof (translation)
Set `b` to `Module.finBasis ℤ (𝓞 E)`. Use `⟨∑ j, algebraMap (𝓞 E) E (b j) ⊗ₜ[ℚ] mkInt (fun v => ((b.repr (a v) j : ℤ) : v.adicCompletion ℚ)) (fun v => intCast_mem _ _), sum_mem fun j _ => levelaf_tmul_mem _ (mkInt_mem _ _), fun v => ?_⟩` and prove the remaining obligations. Rewrite using `[map_sum]`. Use `conv_rhs => rw [← b.sum_repr (a v)]`. Rewrite using `[show ∀ x : 𝓞 E, (x : E) = algebraMap (𝓞 E) E x from fun _ => rfl, map_sum, map_sum]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[afsplit_prV_tmul, mkInt_apply, map_zsmul, ← zsmul_one, ← TensorProduct.smul_tmul]`. Both sides reduce to the same expression.
-/
theorem exists_asm (a : HeightOneSpectrum (𝓞 ℚ) → 𝓞 E) :
    ∃ x ∈ 𝒮, ∀ v, prV (E := E) v x = inclE (F := ℚ) (v.adicCompletion ℚ) (a v : E) := by
  let b := Module.finBasis ℤ (𝓞 E)
  refine ⟨∑ j, algebraMap (𝓞 E) E (b j) ⊗ₜ[ℚ] mkInt (fun v => ((b.repr (a v) j : ℤ) : v.adicCompletion ℚ))
    (fun v => intCast_mem _ _), sum_mem fun j _ => levelaf_tmul_mem _ (mkInt_mem _ _), fun v => ?_⟩
  rw [map_sum]
  conv_rhs => rw [← b.sum_repr (a v)]
  rw [show ∀ x : 𝓞 E, (x : E) = algebraMap (𝓞 E) E x from fun _ => rfl, map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [afsplit_prV_tmul, mkInt_apply, map_zsmul, ← zsmul_one, ← TensorProduct.smul_tmul]
  rfl

def unif : 𝔸 := mkInt (fun v => (pr v : v.adicCompletion ℚ)) (fun _ => natCast_mem _ _)

/- English proof (translation)
The claim follows from `map_natCast (Algebra.TensorProduct.includeRight : _ →ₐ[ℚ] E ⊗[ℚ] v.adicCompletion ℚ) (pr v)`.
-/
theorem prV_unif (v : HeightOneSpectrum (𝓞 ℚ)) : prV (E := E) v ((1 : E) ⊗ₜ[ℚ] unif) = pr v :=
  map_natCast (Algebra.TensorProduct.includeRight : _ →ₐ[ℚ] E ⊗[ℚ] v.adicCompletion ℚ) (pr v)

/- English proof (translation)
Set `φ : intAd ℚ →+* 𝒮` to `((Algebra.TensorProduct.includeRight : 𝔸 →ₐ[ℚ] 𝒜).toRingHom.comp (intAd ℚ).subtype).codRestrict _ fun y => one_tmul_mem y.2`. Set `ψ : 𝓞 E →+* 𝒮` to `((inclE (F := ℚ) 𝔸).comp (algebraMap (𝓞 E) E)).codRestrict _ fun y => adelstab_incl_int y`. Establish `hint : φ.IsIntegral`. Use `letI := φ.toAlgebra`. Introduce and unpack `⟨x, hx⟩`.

Take `⟨r, hr, rfl⟩` from `levelaf_decomp (fun j => Module.finBasis ℤ (𝓞 E) j) (Module.Basis.span_eq _) hx`. Establish `e : (⟨_, hx⟩ : 𝒮) = ∑ j, (φ ⟨r j, hr j⟩ * ψ (Module.finBasis ℤ (𝓞 E) j) : 𝒮)`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[AddSubmonoidClass.coe_finset_sum]`. Simplify using `only`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Use `show _ = ((1 : E) ⊗ₜ[ℚ] r j) * (algebraMap (𝓞 E) E (Module.finBasis ℤ (𝓞 E) j) ⊗ₜ[ℚ] (1 : 𝔸))`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]`. Use `show IsIntegral (intAd ℚ) (⟨_, hx⟩ : 𝒮)`. Rewrite using `[e]`.

Use `IsIntegral.sum _ fun j _ => IsIntegral.mul isIntegral_algebraMap ?_` and prove the remaining obligations. Conclude with `(map_isIntegral_int ψ (RingOfIntegers.isIntegral _)).tower_top`. Establish `hj : (⟨unif, mkInt_mem _ _⟩ : intAd ℚ) ∈ Ideal.jacobson (⊥ : Ideal (intAd ℚ))` using `GlobalTheory.UnRep.Nakayama.mem_jacobson ℚ ⟨unif, mkInt_mem _ _⟩ fun v => GlobalTheory.UnRep.Nakayama.valuation_natCast_lt_one ℚ _ v ((pr_dvd_iff v _).1 dvd_rfl)`. Establish `hj' : φ ⟨unif, mkInt_mem _ _⟩ ∈ Ideal.jacobson (⊥ : Ideal 𝒮)`. Rewrite `hj`, the goal using `[Ideal.jacobson, Ideal.mem_sInf]`.

Introduce and unpack `M ⟨-, hM⟩`. Conclude with `hj (I := M.comap φ) ⟨bot_le, Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' φ hint M⟩`. Take `⟨t, ht⟩` from `(Ideal.mem_jacobson_bot.1 hj' ⟨s, hs⟩).exists_right_inv`. Use `⟨t, t.2, ?_⟩` and prove the remaining obligations. Rewrite using `[add_comm]`.

Conclude with `congrArg Subtype.val ht`.
-/
theorem exists_inv_one_add {s : 𝒜} (hs : s ∈ 𝒮) : ∃ t ∈ 𝒮, (1 + (1 : E) ⊗ₜ[ℚ] unif * s) * t = 1 := by
  let φ : intAd ℚ →+* 𝒮 := ((Algebra.TensorProduct.includeRight : 𝔸 →ₐ[ℚ] 𝒜).toRingHom.comp
    (intAd ℚ).subtype).codRestrict _ fun y => one_tmul_mem y.2
  let ψ : 𝓞 E →+* 𝒮 := ((inclE (F := ℚ) 𝔸).comp (algebraMap (𝓞 E) E)).codRestrict _ fun y => adelstab_incl_int y
  have hint : φ.IsIntegral := by
    letI := φ.toAlgebra
    rintro ⟨x, hx⟩
    obtain ⟨r, hr, rfl⟩ := levelaf_decomp (fun j => Module.finBasis ℤ (𝓞 E) j) (Module.Basis.span_eq _) hx
    have e : (⟨_, hx⟩ : 𝒮) = ∑ j, (φ ⟨r j, hr j⟩ * ψ (Module.finBasis ℤ (𝓞 E) j) : 𝒮) := by
      apply Subtype.ext
      rw [AddSubmonoidClass.coe_finset_sum]
      dsimp only
      refine Finset.sum_congr rfl fun j _ => ?_
      show _ = ((1 : E) ⊗ₜ[ℚ] r j) * (algebraMap (𝓞 E) E (Module.finBasis ℤ (𝓞 E) j) ⊗ₜ[ℚ] (1 : 𝔸))
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    show IsIntegral (intAd ℚ) (⟨_, hx⟩ : 𝒮)
    rw [e]
    refine IsIntegral.sum _ fun j _ => IsIntegral.mul isIntegral_algebraMap ?_
    exact (map_isIntegral_int ψ (RingOfIntegers.isIntegral _)).tower_top
  have hj : (⟨unif, mkInt_mem _ _⟩ : intAd ℚ) ∈ Ideal.jacobson (⊥ : Ideal (intAd ℚ)) :=
    GlobalTheory.UnRep.Nakayama.mem_jacobson ℚ ⟨unif, mkInt_mem _ _⟩ fun v =>
      GlobalTheory.UnRep.Nakayama.valuation_natCast_lt_one ℚ _ v ((pr_dvd_iff v _).1 dvd_rfl)
  have hj' : φ ⟨unif, mkInt_mem _ _⟩ ∈ Ideal.jacobson (⊥ : Ideal 𝒮) := by
    rw [Ideal.jacobson, Ideal.mem_sInf] at hj ⊢
    rintro M ⟨-, hM⟩
    exact hj (I := M.comap φ) ⟨bot_le, Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' φ hint M⟩
  obtain ⟨t, ht⟩ := (Ideal.mem_jacobson_bot.1 hj' ⟨s, hs⟩).exists_right_inv
  refine ⟨t, t.2, ?_⟩
  rw [add_comm]
  exact congrArg Subtype.val ht

open Classical in

def idem (P : ℕ → Prop) : 𝔸 := mkInt (fun v => if P (pr v) then 1 else 0) fun v => by
  split_ifs
  · exact one_mem _
  · exact zero_mem _

variable (E) in

def eps (P : ℕ → Prop) : 𝒜 := (1 : E) ⊗ₜ[ℚ] idem P

/- English proof (translation)
The claim follows from `one_tmul_mem (mkInt_mem _ _)`.
-/
theorem eps_mem (P : ℕ → Prop) : eps E P ∈ 𝒮 := one_tmul_mem (mkInt_mem _ _)

open Classical in
/- English proof (translation)
Rewrite using `[eps, afsplit_prV_tmul, idem, mkInt_apply]`. Use `split_ifs`. Both sides reduce to the same expression. Conclude with `TensorProduct.tmul_zero _ _`.
-/
theorem prV_eps (P : ℕ → Prop) (v : HeightOneSpectrum (𝓞 ℚ)) :
    prV (E := E) v (eps E P) = if P (pr v) then 1 else 0 := by
  rw [eps, afsplit_prV_tmul, idem, mkInt_apply]
  split_ifs
  · rfl
  · exact TensorProduct.tmul_zero _ _

/- English proof (translation)
The claim follows from `ext_prV fun v => by rw [map_mul, prV_eps]; split_ifs <;> simp`.
-/
theorem eps_idem (P : ℕ → Prop) : eps E P * eps E P = eps E P :=
  ext_prV fun v => by rw [map_mul, prV_eps]; split_ifs <;> simp

/- English proof (translation)
The claim follows from `ext_prV fun v => by rw [map_sub, map_one, prV_eps, prV_eps] by_cases h : P (pr v) <;> simp [h]`.
-/
theorem one_sub_eps (P : ℕ → Prop) : 1 - eps E P = eps E (fun q => ¬ P q) :=
  ext_prV fun v => by
    rw [map_sub, map_one, prV_eps, prV_eps]
    by_cases h : P (pr v) <;> simp [h]

/- English proof (translation)
Simplify using `[sigR, eps]`.
-/
theorem sig_eps (σ : E →ₐ[ℚ] E) (P : ℕ → Prop) : sigR σ 𝔸 (eps E P) = eps E P := by
  simp [sigR, eps]

/- English proof (translation)
Establish `hv : ∀ v, P (pr v) → Valued.v (((q ^ k : ℕ) : v.adicCompletion ℚ)) = 1` using `fun v hv => val_natCast_eq_one v fun hd => h (((Nat.prime_dvd_prime_iff_eq (pr_prime v) hq).1 ((pr_prime v).dvd_of_dvd_pow hd)) ▸ hv)`. Use `⟨(1 : E) ⊗ₜ[ℚ] mkInt (fun v => if P (pr v) then ((q ^ k : ℕ) : v.adicCompletion ℚ)⁻¹ else 0) fun v => ?_, one_tmul_mem (mkInt_mem _ _), ?_⟩` and prove the remaining obligations. Use `split_ifs with hP`. Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hv v hP, inv_one]`. Conclude with `zero_mem _`.

Use `ext_prV fun v => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_pow, map_natCast, prV_eps, afsplit_prV_tmul, mkInt_apply]`. Use `split_ifs with hP`. Establish `h0 : ((q ^ k : ℕ) : v.adicCompletion ℚ) ≠ 0` using `fun h0 => by`. Use `hv v hP` as an intermediate fact.

Rewrite `this` using `[h0, map_zero]`. Conclude with `zero_ne_one this`. Use `congrArg (Algebra.TensorProduct.includeRight : _ →ₐ[ℚ] E ⊗[ℚ] v.adicCompletion ℚ) (mul_inv_cancel₀ h0)` as an intermediate fact. Rewrite `this` using `[map_mul, map_natCast, map_one, Nat.cast_pow]`. Conclude with `this.symm`.

Simplify using the standard rewrite rules.
-/
theorem eps_dvd (P : ℕ → Prop) {q : ℕ} (hq : q.Prime) (h : ¬ P q) (k : ℕ) :
    ∃ s ∈ 𝒮, eps E P = (q : 𝒜) ^ k * s := by
  classical
  have hv : ∀ v, P (pr v) → Valued.v (((q ^ k : ℕ) : v.adicCompletion ℚ)) = 1 := fun v hv =>
    val_natCast_eq_one v fun hd => h
      (((Nat.prime_dvd_prime_iff_eq (pr_prime v) hq).1 ((pr_prime v).dvd_of_dvd_pow hd)) ▸ hv)
  refine ⟨(1 : E) ⊗ₜ[ℚ] mkInt (fun v => if P (pr v) then ((q ^ k : ℕ) : v.adicCompletion ℚ)⁻¹ else 0) fun v => ?_,
    one_tmul_mem (mkInt_mem _ _), ?_⟩
  · split_ifs with hP
    · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hv v hP, inv_one]
    · exact zero_mem _
  · refine ext_prV fun v => ?_
    rw [map_mul, map_pow, map_natCast, prV_eps, afsplit_prV_tmul, mkInt_apply]
    split_ifs with hP
    · have h0 : ((q ^ k : ℕ) : v.adicCompletion ℚ) ≠ 0 := fun h0 => by
        have := hv v hP
        rw [h0, map_zero] at this
        exact zero_ne_one this
      have := congrArg (Algebra.TensorProduct.includeRight : _ →ₐ[ℚ] E ⊗[ℚ] v.adicCompletion ℚ) (mul_inv_cancel₀ h0)
      rw [map_mul, map_natCast, map_one, Nat.cast_pow] at this
      exact this.symm
    · simp

/- English proof (translation)
Establish `loc : ∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ a r s : 𝓞 E, (¬ P (pr v) → a = 0) ∧ a * c • a = pr v * r ∧ a + c • a = (if P (pr v) then 1 else 0) + pr v * s`. Introduce `v`. Distinguish the cases in `hv : P (pr v)`. Take `⟨a, r, s, h1, h2⟩` from `exists_half c hcc (pr_prime v).ne_zero (h _ (pr_prime v) hv)`. Conclude with `⟨a, r, s, fun h => absurd hv h, h1, by rw [if_pos hv, h2]⟩`.

Conclude with `⟨0, 0, 0, fun _ => rfl, by simp, by simp [hv]⟩`. Use `choose a r s h0 h1 h2 using loc`. Take `⟨a', ha', ha⟩` from `exists_asm a`. Take `⟨r', hr', hr⟩` from `exists_asm r`. Take `⟨s', hs', hs⟩` from `exists_asm s`.

Establish `hσ : ∀ v, prV (E` using `E) v (sigR (c : E →ₐ[ℚ] E) 𝔸 a') = inclE (F := ℚ) (v.adicCompletion ℚ) ((c • a v : 𝓞 E) : E) := fun v => by`. Rewrite using `[prV_sig, ha]`. Both sides reduce to the same expression. Use `⟨a', ha', r', hr', s', hs', ext_prV fun v => ?_, ext_prV fun v => ?_, ext_prV fun v => ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, prV_eps] split_ifs with hv`.

Rewrite using `[one_mul]`. Rewrite using `[ha, h0 v hv]`. Simplify using the standard rewrite rules. Use `congrArg ((inclE (F := ℚ) (v.adicCompletion ℚ)).comp (algebraMap (𝓞 E) E)) (h1 v)` as an intermediate fact. Rewrite `this` using `[map_mul, map_mul, map_natCast]`.

Rewrite using `[map_mul, map_mul, hσ, ha, hr, prV_unif]`. Conclude with `this`. Use `congrArg ((inclE (F := ℚ) (v.adicCompletion ℚ)).comp (algebraMap (𝓞 E) E)) (h2 v)` as an intermediate fact. Rewrite `this` using `[map_add, map_add, map_mul, map_natCast, apply_ite ((inclE (F := ℚ) (v.adicCompletion ℚ)).comp _), map_one, map_zero]`. Rewrite using `[map_add, map_add, map_mul, hσ, ha, hs, prV_unif, prV_eps]`.

Conclude with `this`.
-/
theorem exists_half_adele (c : E ≃ₐ[ℚ] E) (hcc : c * c = 1) (P : ℕ → Prop)
    (h : ∀ q : ℕ, q.Prime → P q → ∀ I : Ideal (𝓞 E), I.IsPrime → (q : 𝓞 E) ∈ I → c • I ≠ I) :
    ∃ a ∈ 𝒮, ∃ r ∈ 𝒮, ∃ s ∈ 𝒮, eps E P * a = a ∧ a * sigR (c : E →ₐ[ℚ] E) 𝔸 a = (1 : E) ⊗ₜ[ℚ] unif * r ∧
      a + sigR (c : E →ₐ[ℚ] E) 𝔸 a = eps E P + (1 : E) ⊗ₜ[ℚ] unif * s := by
  classical
  have loc : ∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ a r s : 𝓞 E, (¬ P (pr v) → a = 0) ∧ a * c • a = pr v * r ∧
      a + c • a = (if P (pr v) then 1 else 0) + pr v * s := by
    intro v
    by_cases hv : P (pr v)
    · obtain ⟨a, r, s, h1, h2⟩ := exists_half c hcc (pr_prime v).ne_zero (h _ (pr_prime v) hv)
      exact ⟨a, r, s, fun h => absurd hv h, h1, by rw [if_pos hv, h2]⟩
    · exact ⟨0, 0, 0, fun _ => rfl, by simp, by simp [hv]⟩
  choose a r s h0 h1 h2 using loc
  obtain ⟨a', ha', ha⟩ := exists_asm a
  obtain ⟨r', hr', hr⟩ := exists_asm r
  obtain ⟨s', hs', hs⟩ := exists_asm s
  have hσ : ∀ v, prV (E := E) v (sigR (c : E →ₐ[ℚ] E) 𝔸 a') =
      inclE (F := ℚ) (v.adicCompletion ℚ) ((c • a v : 𝓞 E) : E) := fun v => by
    rw [prV_sig, ha]; rfl
  refine ⟨a', ha', r', hr', s', hs', ext_prV fun v => ?_, ext_prV fun v => ?_, ext_prV fun v => ?_⟩
  · rw [map_mul, prV_eps]
    split_ifs with hv
    · rw [one_mul]
    · rw [ha, h0 v hv]; simp
  · have := congrArg ((inclE (F := ℚ) (v.adicCompletion ℚ)).comp (algebraMap (𝓞 E) E)) (h1 v)
    rw [map_mul, map_mul, map_natCast] at this
    rw [map_mul, map_mul, hσ, ha, hr, prV_unif]
    exact this
  · have := congrArg ((inclE (F := ℚ) (v.adicCompletion ℚ)).comp (algebraMap (𝓞 E) E)) (h2 v)
    rw [map_add, map_add, map_mul, map_natCast, apply_ite ((inclE (F := ℚ) (v.adicCompletion ℚ)).comp _),
      map_one, map_zero] at this
    rw [map_add, map_add, map_mul, hσ, ha, hs, prV_unif, prV_eps]
    exact this

/- English proof (translation)
Take `⟨a, ha, r, hr, s, hs', h0, h1, h2⟩` from `exists_half_adele c hcc P h`. Establish `hσσ : ∀ z : 𝒜, sigR (c : E →ₐ[ℚ] E) 𝔸 (sigR (c : E →ₐ[ℚ] E) 𝔸 z) = z`. Introduce `z`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul x y`. Establish `: c (c x) = x` using `DFunLike.congr_fun hcc x`. Simplify using `[sigR, this]`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`. Establish `hε` using `sig_eps (c : E →ₐ[ℚ] E) P`.

Establish `hεε` using `eps_idem (E := E) P`. Establish `hεm` using `eps_mem (E := E) P`. Establish `h0'` using `congrArg (sigR (c : E →ₐ[ℚ] E) 𝔸) h0`. Rewrite `h0'` using `[map_mul, hε]`. Establish `hπ : (1 : E) ⊗ₜ[ℚ] unif ∈ 𝒮` using `one_tmul_mem (mkInt_mem _ _)`.

Establish `ha'` using `csDual_sig_mem (c : E →ₐ[ℚ] E) ha`. Establish `hu'` using `csDual_sig_mem (c : E →ₐ[ℚ] E) hu`. Use `set σ := sigR (c : E →ₐ[ℚ] E) 𝔸`. Use `set ε := eps E P`. Use `set π := (1 : E) ⊗ₜ[ℚ] unif`.

Take `⟨t, ht, e⟩` from `exists_inv_one_add (s := 2 * ε * s + π * s * s + (u + σ u - 2) * r) (add_mem (add_mem (mul_mem (mul_mem (ofNat_mem _ 2) hεm) hs') (mul_mem (mul_mem hπ hs') hs')) (mul_mem (sub_mem (add_mem hu hu') (ofNat_mem _ 2)) hr))`. Establish `hxy : (a + u * σ a + (1 - ε)) * ((a + σ u * σ a + (1 - ε)) * t) = 1`. Use `Eq.trans ?_ e` and prove the remaining obligations. Rewrite using `[← mul_assoc]`. Use `congrArg (· * t) (show _ = 1 + π * _ from ?_)` and prove the remaining obligations.

Take the linear combination `(σ a * σ a) * hn + (u + σ u - 2) * h1 + (a + σ a + ε + π * s) * h2 - 2 * h0 - (u + σ u) * h0' + 2 * hεε`. Use `⟨Units.mkOfMulEqOne _ _ hxy, add_mem (add_mem ha (mul_mem hu ha')) (sub_mem (one_mem _) hεm), mul_mem (add_mem (add_mem ha (mul_mem hu' ha')) (sub_mem (one_mem _) hεm)) ht, ?_, a + u * σ a - 1, sub_mem (add_mem ha (mul_mem hu ha')) (one_mem _), ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_mkOfMulEqOne, map_add, map_add, map_mul, map_sub, map_one, hσσ, hε]`. Take the linear combination `(-a) * hn + hs`. Rewrite using `[Units.val_mkOfMulEqOne]`.

Take the linear combination `- h0 - u * h0'`.
-/
theorem hilbert90_integral_ideles_of_moved_primes (c : E ≃ₐ[ℚ] E) (hcc : c * c = 1) (P : ℕ → Prop)
    (h : ∀ q : ℕ, q.Prime → P q → ∀ I : Ideal (𝓞 E), I.IsPrime → (q : 𝓞 E) ∈ I → c • I ≠ I)
    {u : 𝒜} (hu : u ∈ 𝒮) (hn : u * sigR (c : E →ₐ[ℚ] E) 𝔸 u = 1) (hs : eps E P * (u - 1) = u - 1) :
    ∃ x : (𝒜)ˣ, (x : 𝒜) ∈ 𝒮 ∧ ((x⁻¹ : (𝒜)ˣ) : 𝒜) ∈ 𝒮 ∧ (x : 𝒜) = u * sigR (c : E →ₐ[ℚ] E) 𝔸 x ∧
      ∃ y ∈ 𝒮, (x : 𝒜) - 1 = eps E P * y := by
  obtain ⟨a, ha, r, hr, s, hs', h0, h1, h2⟩ := exists_half_adele c hcc P h
  have hσσ : ∀ z : 𝒜, sigR (c : E →ₐ[ℚ] E) 𝔸 (sigR (c : E →ₐ[ℚ] E) 𝔸 z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      have : c (c x) = x := DFunLike.congr_fun hcc x
      simp [sigR, this]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hε := sig_eps (c : E →ₐ[ℚ] E) P
  have hεε := eps_idem (E := E) P
  have hεm := eps_mem (E := E) P
  have h0' := congrArg (sigR (c : E →ₐ[ℚ] E) 𝔸) h0
  rw [map_mul, hε] at h0'
  have hπ : (1 : E) ⊗ₜ[ℚ] unif ∈ 𝒮 := one_tmul_mem (mkInt_mem _ _)
  have ha' := csDual_sig_mem (c : E →ₐ[ℚ] E) ha
  have hu' := csDual_sig_mem (c : E →ₐ[ℚ] E) hu
  set σ := sigR (c : E →ₐ[ℚ] E) 𝔸
  set ε := eps E P
  set π := (1 : E) ⊗ₜ[ℚ] unif
  obtain ⟨t, ht, e⟩ := exists_inv_one_add (s := 2 * ε * s + π * s * s + (u + σ u - 2) * r)
    (add_mem (add_mem (mul_mem (mul_mem (ofNat_mem _ 2) hεm) hs') (mul_mem (mul_mem hπ hs') hs'))
      (mul_mem (sub_mem (add_mem hu hu') (ofNat_mem _ 2)) hr))
  have hxy : (a + u * σ a + (1 - ε)) * ((a + σ u * σ a + (1 - ε)) * t) = 1 := by
    refine Eq.trans ?_ e
    rw [← mul_assoc]
    refine congrArg (· * t) (show _ = 1 + π * _ from ?_)
    linear_combination (σ a * σ a) * hn + (u + σ u - 2) * h1 + (a + σ a + ε + π * s) * h2 - 2 * h0 - (u + σ u) * h0'
      + 2 * hεε
  refine ⟨Units.mkOfMulEqOne _ _ hxy, add_mem (add_mem ha (mul_mem hu ha')) (sub_mem (one_mem _) hεm),
    mul_mem (add_mem (add_mem ha (mul_mem hu' ha')) (sub_mem (one_mem _) hεm)) ht, ?_,
    a + u * σ a - 1, sub_mem (add_mem ha (mul_mem hu ha')) (one_mem _), ?_⟩
  · rw [Units.val_mkOfMulEqOne, map_add, map_add, map_mul, map_sub, map_one, hσσ, hε]
    linear_combination (-a) * hn + hs
  · rw [Units.val_mkOfMulEqOne]
    linear_combination - h0 - u * h0'

end Adelic

section Cut

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

def cutM (e : R) (he : e * e = e) : Matrix n n R →* Matrix n n R where
  toFun A := e • A + (1 - e) • (1 : Matrix n n R)
  map_one' := by rw [← add_smul]; simp
  map_mul' A B := by
    have h1 : e * (1 - e) = 0 := by linear_combination - he
    have h2 : (1 - e) * (1 - e) = 1 - e := by linear_combination he
    simp only [add_mul, mul_add, smul_mul_smul_comm, Matrix.mul_one, Matrix.one_mul, he, h1, h2,
      mul_comm (1 - e) e, zero_smul, add_zero, zero_add]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cutM_apply (e : R) (he : e * e = e) (A : Matrix n n R) (i j : n) :
    cutM e he A i j = e * A i j + (1 - e) * (1 : Matrix n n R) i j := rfl

/- English proof (translation)
Substitute `h` using the available equality. Establish `h1 : e * (1 - e) = 0` using `by linear_combination - he`. Use `show (e • A + (1 - e) • (1 : Matrix n n R)) * ((1 - e) • A + (1 - (1 - e)) • (1 : Matrix n n R)) = A`. Simplify using `only [sub_sub_cancel, add_mul, mul_add, smul_mul_smul_comm, Matrix.mul_one, Matrix.one_mul, he, h1, he', mul_comm (1 - e) e, zero_smul, add_zero, zero_add]`. Rewrite using `[← add_smul]`.

Simplify using the standard rewrite rules.
-/
theorem cutM_mul_compl (e e' : R) (he : e * e = e) (he' : e' * e' = e') (h : 1 - e = e') (A : Matrix n n R) :
    cutM e he A * cutM e' he' A = A := by
  subst h
  have h1 : e * (1 - e) = 0 := by linear_combination - he
  show (e • A + (1 - e) • (1 : Matrix n n R)) * ((1 - e) • A + (1 - (1 - e)) • (1 : Matrix n n R)) = A
  simp only [sub_sub_cancel, add_mul, mul_add, smul_mul_smul_comm, Matrix.mul_one, Matrix.one_mul, he, h1, he',
      mul_comm (1 - e) e, zero_smul, add_zero, zero_add]
  rw [← add_smul]; simp

/- English proof (translation)
Use extensionality with `i j`. Use `congrFun (congrFun (cT_one (n := n) σ) i) j` as an intermediate fact. Simplify using `only [cT, transpose_apply, Matrix.map_apply] at this`. Simplify using `only [cT, transpose_apply, Matrix.map_apply, cutM_apply, map_add, map_mul, map_sub, map_one, hσ, this]`.
-/
theorem cT_cutM (σ : R →+* R) (e : R) (he : e * e = e) (hσ : σ e = e) (A : Matrix n n R) :
    cT σ (cutM e he A) = cutM e he (cT σ A) := by
  ext i j
  have := congrFun (congrFun (cT_one (n := n) σ) i) j
  simp only [cT, transpose_apply, Matrix.map_apply] at this
  simp only [cT, transpose_apply, Matrix.map_apply, cutM_apply, map_add, map_mul, map_sub, map_one, hσ, this]

/- English proof (translation)
Establish `h0 : Ideal.Quotient.mk (Ideal.span {e}) e = 0` using `Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self e)`. Establish `h : (Ideal.Quotient.mk (Ideal.span {e})).mapMatrix (cutM e he A) = 1`. Use extensionality with `i j`. Rewrite using `[RingHom.mapMatrix_apply, Matrix.map_apply, cutM_apply, Matrix.one_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp [h0]`.

Establish `h2 : (cutM e he A).det - 1 ∈ Ideal.span {e}`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_sub, RingHom.map_det, h, det_one, map_one, sub_self]`. Take `⟨y, hy⟩` from `Ideal.mem_span_singleton.1 h2`. Rewrite using `[hy, ← mul_assoc, he]`.
-/
theorem det_cutM (e : R) (he : e * e = e) (A : Matrix n n R) :
    e * ((cutM e he A).det - 1) = (cutM e he A).det - 1 := by
  have h0 : Ideal.Quotient.mk (Ideal.span {e}) e = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self e)
  have h : (Ideal.Quotient.mk (Ideal.span {e})).mapMatrix (cutM e he A) = 1 := by
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, cutM_apply, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp [h0]
  have h2 : (cutM e he A).det - 1 ∈ Ideal.span {e} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, RingHom.map_det, h, det_one, map_one, sub_self]
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.1 h2
  rw [hy, ← mul_assoc, he]

/- English proof (translation)
Rewrite using `[Matrix.one_apply]`. Use `split_ifs`. Conclude with `one_mem _`. Conclude with `zero_mem _`.
-/
theorem one_entry_mem (S : Subring R) (i j : n) : (1 : Matrix n n R) i j ∈ S := by
  rw [Matrix.one_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

/- English proof (translation)
Rewrite using `[Matrix.det_apply']`. Conclude with `sum_mem fun σ _ => mul_mem (intCast_mem _ _) (prod_mem fun i _ => h _ _)`.
-/
theorem det_mem (S : Subring R) {A : Matrix n n R} (h : ∀ i j, A i j ∈ S) : A.det ∈ S := by
  rw [Matrix.det_apply']
  exact sum_mem fun σ _ => mul_mem (intCast_mem _ _) (prod_mem fun i _ => h _ _)

end Cut

open Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

/- English proof (translation)
Use `letI := D.host.isCMField_hostE`. Establish `h : ∀ x, D.host.conj x = IsCMField.complexConj D.host.E x` using `fun x => D.host.φ₀.injective (by`. Rewrite using `[NumberField.IsCMField.complexEmbedding_complexConj, D.host.toHostAx.conjE_apply])`. Use `ext1 x`. Apply `D.host.φ₀.injective` to reduce the goal to its premises.

Use `NumberField.IsCMField.complexEmbedding_complexConj D.host.E (D.host.φ₀.comp (g : D.host.E →+* D.host.E)) x` as an intermediate fact. Rewrite using `[AlgEquiv.mul_apply, AlgEquiv.mul_apply, h, h, NumberField.IsCMField.complexEmbedding_complexConj]`. Conclude with `this.symm`.
-/
theorem conj_comm (D : D7) (g : D.host.E ≃ₐ[ℚ] D.host.E) : D.host.conj * g = g * D.host.conj := by
  letI := D.host.isCMField_hostE
  have h : ∀ x, D.host.conj x = IsCMField.complexConj D.host.E x := fun x => D.host.φ₀.injective (by
    rw [NumberField.IsCMField.complexEmbedding_complexConj, D.host.toHostAx.conjE_apply])
  ext1 x
  apply D.host.φ₀.injective
  have := NumberField.IsCMField.complexEmbedding_complexConj D.host.E
    (D.host.φ₀.comp (g : D.host.E →+* D.host.E)) x
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, h, h, NumberField.IsCMField.complexEmbedding_complexConj]
  exact this.symm

/- English proof (translation)
Use `ext1 x`. Apply `D.host.φ₀.injective` to reduce the goal to its premises. Rewrite using `[AlgEquiv.mul_apply, D.host.toHostAx.conjE_apply, D.host.toHostAx.conjE_apply]`. Simplify using the standard rewrite rules.
-/
theorem conj_mul_self (D : D7) : D.host.conj * D.host.conj = 1 := by
  ext1 x
  apply D.host.φ₀.injective
  rw [AlgEquiv.mul_apply, D.host.toHostAx.conjE_apply, D.host.toHostAx.conjE_apply]
  simp

/- English proof (translation)
Use `haveI : IsGalois ℚ D.host.E := D.host.hostE_isGalois`. Unfold `InertQ at h`. Use `push Not at h`. Take `⟨P, hP, -, hqP, hne⟩` from `h`. Conclude with `moves_all _ (conj_comm D) hq hP hI hqP hqI hne`.
-/
theorem conj_smul_ne (D : D7) {q : ℕ} (hq : q.Prime) (h : ¬ InertQ D q) (I : Ideal (𝓞 D.host.E)) (hI : I.IsPrime)
    (hqI : (q : 𝓞 D.host.E) ∈ I) : D.host.conj • I ≠ I := by
  haveI : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  unfold InertQ at h
  push Not at h
  obtain ⟨P, hP, -, hqP, hne⟩ := h
  exact moves_all _ (conj_comm D) hq hP hI hqP hqI hne

/- English proof (translation)
Introduce `k`. Take `⟨d, hd0, hd⟩` from `levelaf_denom (F := ℚ) y`. Take `⟨z, rfl⟩ : ∃ z : ℤ, d = z` from `⟨Rat.ringOfIntegersEquiv d, by`. Apply `Rat.ringOfIntegersEquiv.injective` to reduce the goal to its premises. Use the proof step `simp⟩`.

Establish `hz : z.natAbs ≠ 0` using `by rintro h; apply hd0; simp [Int.natAbs_eq_zero.1 h]`. Establish `hC : levelafC (F` using `ℚ) D.host.E (z : 𝓞 ℚ) = (z : AE D) := by`. Rewrite using `[levelafC, map_intCast]`. Conclude with `map_intCast (Algebra.TensorProduct.includeRight : _ →ₐ[ℚ] AE D) z`. Establish `hd' : (z.natAbs : AE D) * y ∈ OhE D`.

Rewrite `hd` using `[hC]`. Break down `Int.natAbs_eq z with e | e` into its components or cases. Rewrite `hd` using `[e]`. Simplify `hd` using `[OhE]`. Rewrite `hd` using `[e]`.

Use `neg_mem hd` as an intermediate fact. Simplify `this` using `[OhE]`. Take `⟨j, m, hm, e⟩` from `Nat.exists_eq_pow_mul_and_not_dvd hz q hq.ne_one`. Take `⟨s, hs, es⟩` from `eps_dvd (E := D.host.E) P hq h (k + j)`. Use `⟨m, Nat.pos_of_ne_zero (by rintro rfl; simp at hm), ((Nat.Prime.coprime_iff_not_dvd hq).2 hm).symm, s * ((z.natAbs : AE D) * y), mul_mem hs hd', ?_⟩` and prove the remaining obligations.

Rewrite using `[es, e]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem zeroAt_eps_mul (D : D7) (P : ℕ → Prop) {q : ℕ} (hq : q.Prime) (h : ¬ P q) (y : AE D) :
    ZeroAt D q (eps D.host.E P * y) := by
  intro k
  obtain ⟨d, hd0, hd⟩ := levelaf_denom (F := ℚ) y
  obtain ⟨z, rfl⟩ : ∃ z : ℤ, d = z := ⟨Rat.ringOfIntegersEquiv d, by
    apply Rat.ringOfIntegersEquiv.injective; simp⟩
  have hz : z.natAbs ≠ 0 := by rintro h; apply hd0; simp [Int.natAbs_eq_zero.1 h]
  have hC : levelafC (F := ℚ) D.host.E (z : 𝓞 ℚ) = (z : AE D) := by
    rw [levelafC, map_intCast]
    exact map_intCast (Algebra.TensorProduct.includeRight : _ →ₐ[ℚ] AE D) z
  have hd' : (z.natAbs : AE D) * y ∈ OhE D := by
    rw [hC] at hd
    rcases Int.natAbs_eq z with e | e
    · rw [e] at hd; simpa [OhE] using hd
    · rw [e] at hd
      have := neg_mem hd
      simpa [OhE] using this
  obtain ⟨j, m, hm, e⟩ := Nat.exists_eq_pow_mul_and_not_dvd hz q hq.ne_one
  obtain ⟨s, hs, es⟩ := eps_dvd (E := D.host.E) P hq h (k + j)
  refine ⟨m, Nat.pos_of_ne_zero (by rintro rfl; simp at hm), ((Nat.Prime.coprime_iff_not_dvd hq).2 hm).symm,
    s * ((z.natAbs : AE D) * y), mul_mem hs hd', ?_⟩
  rw [es, e]
  push_cast
  ring

def part (D : D7) {N : ℕ} (P : ℕ → Prop) (g : GA D N) : GA D N :=
  ⟨Units.map (cutM (eps D.host.E P) (eps_idem P)) (g : GL (Fin N) (AE D)), by
    have hg : cT (sgA D) ((g : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) *
      (1 : Matrix (Fin N) (Fin N) D.host.E).map (inc D) * (g : GL (Fin N) (AE D)) = _ := g.2
    have h1 : (1 : Matrix (Fin N) (Fin N) D.host.E).map (inc D) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
    show cT (sgA D) (cutM _ _ _) * (1 : Matrix (Fin N) (Fin N) D.host.E).map (inc D) * cutM _ _ _ =
      (1 : Matrix (Fin N) (Fin N) D.host.E).map (inc D)
    change _ = (1 : Matrix (Fin N) (Fin N) D.host.E).map (inc D) at hg
    rw [h1, Matrix.mul_one] at hg ⊢
    rw [cT_cutM (sgA D) _ _ (sig_eps _ P), ← map_mul, hg, map_one]⟩

/- English proof (translation)
The claim follows from `Subtype.ext (Units.ext (cutM_mul_compl _ _ _ _ (one_sub_eps P) _))`.
-/
theorem part_mul_compl (D : D7) {N : ℕ} (P : ℕ → Prop) (g : GA D N) :
    part D P g * part D (fun q => ¬ P q) g = g :=
  Subtype.ext (Units.ext (cutM_mul_compl _ _ _ _ (one_sub_eps P) _))

/- English proof (translation)
Introduce `i j`. Use `zeroAt_eps_mul D P hq h (((g : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j - (1 : Matrix (Fin N) (Fin N) (AE D)) i j)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use `show cutM _ _ _ i j - _ = _`. Rewrite using `[cutM_apply]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem trivAt_part (D : D7) {N : ℕ} (P : ℕ → Prop) (g : GA D N) {q : ℕ} (hq : q.Prime) (h : ¬ P q) :
    TrivAt D q (part D P g : GL (Fin N) (AE D)) := by
  intro i j
  have := zeroAt_eps_mul D P hq h (((g : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j -
    (1 : Matrix (Fin N) (Fin N) (AE D)) i j)
  convert this using 1
  show cutM _ _ _ i j - _ = _
  rw [cutM_apply]
  ring

/- English proof (translation)
Introduce `i j` and use `⟨add_mem (mul_mem (eps_mem P) (hg i j).1) (mul_mem (sub_mem (one_mem _) (eps_mem P)) (one_entry_mem _ i j)), add_mem (mul_mem (eps_mem P) (hg i j).2) (mul_mem (sub_mem (one_mem _) (eps_mem P)) (one_entry_mem _ i j))⟩`.
-/
theorem intG_part (D : D7) {N : ℕ} (P : ℕ → Prop) {g : GA D N} (hg : IntG D (g : GL (Fin N) (AE D))) :
    IntG D (part D P g : GL (Fin N) (AE D)) := fun i j =>
  ⟨add_mem (mul_mem (eps_mem P) (hg i j).1) (mul_mem (sub_mem (one_mem _) (eps_mem P)) (one_entry_mem _ i j)),
    add_mem (mul_mem (eps_mem P) (hg i j).2) (mul_mem (sub_mem (one_mem _) (eps_mem P)) (one_entry_mem _ i j))⟩

/- English proof (translation)
Introduce `_ hq h` and use `trivAt_part D _ g hq (not_not.2 h)`.
-/
theorem suppSplit_part (D : D7) {N : ℕ} (g : GA D N) :
    SuppSplit D (part D (fun q => ¬ InertQ D q) g : GL (Fin N) (AE D)) :=
  fun _ hq h => trivAt_part D _ g hq (not_not.2 h)

/- English proof (translation)
Introduce `_ hq h` and use `trivAt_part D _ g hq (not_not.2 h)`.
-/
theorem suppInert_part (D : D7) {N : ℕ} (g : GA D N) :
    SuppInert D (part D (fun q => ¬ ¬ InertQ D q) g : GL (Fin N) (AE D)) :=
  fun _ hq h => trivAt_part D _ g hq (not_not.2 h)

/- English proof (translation)
Establish `hg : cT (sgA D) ((g : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) * (1 : Matrix (Fin N) (Fin N) D.host.E).map (inc D) * (g : GL (Fin N) (AE D)) = (1 : Matrix (Fin N) (Fin N) D.host.E).map (inc D)` using `g.2`. Rewrite `hg` using `[Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]`. Use `congrArg Matrix.det hg` as an intermediate fact. Rewrite `this` using `[det_mul, cT, det_transpose, det_one, ← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Rewrite using `[mul_comm, this]`.
-/
theorem det_mul_sg (D : D7) {N : ℕ} (g : GA D N) :
    ((g : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)).det *
      sgA D ((g : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)).det = 1 := by
  have hg : cT (sgA D) ((g : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) *
      (1 : Matrix (Fin N) (Fin N) D.host.E).map (inc D) * (g : GL (Fin N) (AE D)) =
      (1 : Matrix (Fin N) (Fin N) D.host.E).map (inc D) := g.2
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at hg
  have := congrArg Matrix.det hg
  rw [det_mul, cT, det_transpose, det_one, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at this
  rw [mul_comm, this]

/- English proof (translation)
Take `⟨x, h1, h2, h3, y, -, h4⟩` from `hilbert90_integral_ideles_of_moved_primes D.host.conj (conj_mul_self D) (fun q => ¬ InertQ D q) (fun q hq h => conj_smul_ne D hq h) (det_mem _ fun i j => (intG_part D (fun q => ¬ InertQ D q) hk i j).1) (det_mul_sg D _) (det_cutM _ _ _)`. Use `⟨x, ⟨h1, h2⟩, fun q hq h => ?_, Units.ext h3⟩` and prove the remaining obligations. Rewrite using `[h4]`. Conclude with `zeroAt_eps_mul D _ hq (not_not.2 h) y`.
-/
theorem exists_idele (D : D7) {N : ℕ} {k : GA D N} (hk : IntG D (k : GL (Fin N) (AE D))) :
    ∃ x : (AE D)ˣ, IntU D x ∧ (∀ q : ℕ, q.Prime → InertQ D q → ZeroAt D q ((x : AE D) - 1)) ∧
      x = Matrix.GeneralLinearGroup.det (part D (fun q => ¬ InertQ D q) k : GL (Fin N) (AE D)) * sgU D x := by
  obtain ⟨x, h1, h2, h3, y, -, h4⟩ := hilbert90_integral_ideles_of_moved_primes D.host.conj (conj_mul_self D) (fun q => ¬ InertQ D q)
    (fun q hq h => conj_smul_ne D hq h) (det_mem _ fun i j => (intG_part D (fun q => ¬ InertQ D q) hk i j).1)
    (det_mul_sg D _) (det_cutM _ _ _)
  refine ⟨x, ⟨h1, h2⟩, fun q hq h => ?_, Units.ext h3⟩
  rw [h4]
  exact zeroAt_eps_mul D _ hq (not_not.2 h) y

/- English proof (translation)
Establish `hmv : ∀ (M : Matrix (Fin N) (Fin N) (AE D)) (v : Fin N → AE D), (∀ i j, M i j ∈ OhE D) → (∀ i, v i ∈ OhE D) → ∀ i, (M *ᵥ v) i ∈ OhE D` using `fun M v hM hv i => by`. Simplify using `only [mulVec, dotProduct]`. Conclude with `sum_mem fun j _ => mul_mem (hM i j) (hv j)`. Introduce `x`. Rewrite using `[stdL, Submodule.mem_pi]`.

Prove the components needed by the constructor for the conclusion. Introduce `hx`. Use `hmv _ _ (fun i j => (hk i j).2) fun j => ?_` and prove the remaining obligations. Take `⟨b, hb⟩` from `Submodule.mem_one.1 (hx j (Set.mem_univ _))`. Rewrite using `[← hb]`.

Conclude with `adelstab_incl_int b`. Introduce `hx i _`. Use `hmv _ _ (fun i j => (hk i j).1) hx i` as an intermediate fact. Rewrite `this` using `[mulVec_mulVec, Units.mul_inv, one_mulVec]`. Conclude with `Submodule.mem_one.2 ⟨⟨x i, csGlob_int (F := ℚ) _ this⟩, rfl⟩`.
-/
theorem moves_std (D : D7) {N : ℕ} {k : GL (Fin N) (AE D)} (hk : IntG D k) : Moves D k (stdL D N) := by
  have hmv : ∀ (M : Matrix (Fin N) (Fin N) (AE D)) (v : Fin N → AE D), (∀ i j, M i j ∈ OhE D) →
      (∀ i, v i ∈ OhE D) → ∀ i, (M *ᵥ v) i ∈ OhE D := fun M v hM hv i => by
    simp only [mulVec, dotProduct]
    exact sum_mem fun j _ => mul_mem (hM i j) (hv j)
  intro x
  rw [stdL, Submodule.mem_pi]
  constructor
  · intro hx
    refine hmv _ _ (fun i j => (hk i j).2) fun j => ?_
    obtain ⟨b, hb⟩ := Submodule.mem_one.1 (hx j (Set.mem_univ _))
    rw [← hb]
    exact adelstab_incl_int b
  · intro hx i _
    have := hmv _ _ (fun i j => (hk i j).1) hx i
    rw [mulVec_mulVec, Units.mul_inv, one_mulVec] at this
    exact Submodule.mem_one.2 ⟨⟨x i, csGlob_int (F := ℚ) _ this⟩, rfl⟩

/- English proof (translation)
Use function extensionality and compare the values at `z`. Establish `ht : A.addSubgroupOf A = ⊤` using `AddSubgroup.addSubgroupOf_self A`. Use `haveI : Subsingleton (A ⧸ A.addSubgroupOf A) := by`. Rewrite using `[ht]`. Conclude with `QuotientAddGroup.subsingleton_quotient_top`.

Use `haveI : Unique (A ⧸ A.addSubgroupOf A) := ⟨⟨((0 : A) : A ⧸ A.addSubgroupOf A)⟩, fun _ => Subsingleton.elim _ _⟩`. Unfold `Iop`. Rewrite using `[finsum_unique, hG.2 _ (Subtype.prop _), ht]`. Simplify using the standard rewrite rules.
-/
theorem iop_self (D : D7) (T : Tor D) {N N' : ℕ} (A : AddSubgroup (VC D N N')) {G : VC D N N' → ℂ}
    (hG : G ∈ ThSp D T A) : Iop D T A A G = G := by
  funext z
  have ht : A.addSubgroupOf A = ⊤ := AddSubgroup.addSubgroupOf_self A
  haveI : Subsingleton (A ⧸ A.addSubgroupOf A) := by
    rw [ht]; exact QuotientAddGroup.subsingleton_quotient_top
  haveI : Unique (A ⧸ A.addSubgroupOf A) := ⟨⟨((0 : A) : A ⧸ A.addSubgroupOf A)⟩, fun _ => Subsingleton.elim _ _⟩
  unfold Iop
  rw [finsum_unique, hG.2 _ (Subtype.prop _), ht]
  simp

/- English proof (translation)
The claim follows from `Subtype.ext (Units.ext (map_one (cutM (n := Fin N) (eps D.host.E P) (eps_idem P))))`.
-/
theorem part_one (D : D7) {N : ℕ} (P : ℕ → Prop) : part D P (1 : GA D N) = 1 :=
  Subtype.ext (Units.ext (map_one (cutM (n := Fin N) (eps D.host.E P) (eps_idem P))))

/- English proof (translation)
Introduce `_` and use `⟨1, one_pos, by simp, 0, zero_mem _, by simp⟩`.
-/
theorem zeroAt_zero (D : D7) (q : ℕ) : ZeroAt D q 0 := fun _ => ⟨1, one_pos, by simp, 0, zero_mem _, by simp⟩

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {a d : ℕ} {e0 : VC D a d → ℂ}

/- English proof (translation)
Use `conv_lhs => rw [← part_mul_compl D (fun q => ¬ InertQ D q) k, ← part_mul_compl D (fun q => ¬ InertQ D q) k']`. Rewrite using `[W.mul _ _ _ _ _ hT, W.inert _ _ (intG_part D _ hk) (intG_part D _ hk') (suppInert_part D k) (suppInert_part D k'), W.split _ _ x x' _ _ (suppSplit_part D k) (suppSplit_part D k') (fun q hq h => ⟨h2 q hq h, h2' q hq h⟩) h3 h3' (moves_std D (intG_part D _ hk)) (moves_std D (intG_p …`. Rewrite using `[La0, iop_self D _ _ he]`. Both sides reduce to the same expression.
-/
theorem om_vac_of_ideles (he : e0 ∈ Th D (tor0 D cc δ) (stdL D a) (stdL D d)) (hT : e0 ∈ TT D (tor0 D cc δ) a d)
    (W : WeilO D cc δ a d e0) {k : GA D a} {k' : GA D d} (hk : IntG D (k : GL (Fin a) (AE D)))
    (hk' : IntG D (k' : GL (Fin d) (AE D))) (x x' : (AE D)ˣ)
    (h2 : ∀ q : ℕ, q.Prime → InertQ D q → ZeroAt D q ((x : AE D) - 1))
    (h2' : ∀ q : ℕ, q.Prime → InertQ D q → ZeroAt D q ((x' : AE D) - 1))
    (h3 : x = Matrix.GeneralLinearGroup.det (part D (fun q => ¬ InertQ D q) k : GL (Fin a) (AE D)) * sgU D x)
    (h3' : x' = Matrix.GeneralLinearGroup.det (part D (fun q => ¬ InertQ D q) k' : GL (Fin d) (AE D)) * sgU D x') :
    W.Om k k' e0 = ((W.chV.f x' ^ W.ep * W.chV'.f x ^ W.ep' : ℂˣ) : ℂ) • e0 := by
  conv_lhs => rw [← part_mul_compl D (fun q => ¬ InertQ D q) k, ← part_mul_compl D (fun q => ¬ InertQ D q) k']
  rw [W.mul _ _ _ _ _ hT, W.inert _ _ (intG_part D _ hk) (intG_part D _ hk') (suppInert_part D k) (suppInert_part D k'),
    W.split _ _ x x' _ _ (suppSplit_part D k) (suppSplit_part D k') (fun q hq h => ⟨h2 q hq h, h2' q hq h⟩) h3 h3'
      (moves_std D (intG_part D _ hk)) (moves_std D (intG_part D _ hk'))]
  rw [La0, iop_self D _ _ he]
  rfl

/- English proof (translation)
Take `⟨x, h1, h2, h3⟩` from `exists_idele D hk`. Take `⟨x', h1', h2', h3'⟩` from `exists_idele D hk'`. Conclude with `⟨x, x', h1, h1', om_vac_of_ideles he hT W hk hk' x x' h2 h2' h3 h3'⟩`.
-/
theorem om_vac_of_mem (he : e0 ∈ Th D (tor0 D cc δ) (stdL D a) (stdL D d)) (hT : e0 ∈ TT D (tor0 D cc δ) a d)
    (W : WeilO D cc δ a d e0) {k : GA D a} {k' : GA D d} (hk : IntG D (k : GL (Fin a) (AE D)))
    (hk' : IntG D (k' : GL (Fin d) (AE D))) :
    ∃ x x' : (AE D)ˣ, IntU D x ∧ IntU D x' ∧
      W.Om k k' e0 = ((W.chV.f x' ^ W.ep * W.chV'.f x ^ W.ep' : ℂˣ) : ℂ) • e0 := by
  obtain ⟨x, h1, h2, h3⟩ := exists_idele D hk
  obtain ⟨x', h1', h2', h3'⟩ := exists_idele D hk'
  exact ⟨x, x', h1, h1', om_vac_of_ideles he hT W hk hk' x x' h2 h2' h3 h3'⟩

/- English proof (translation)
Introduce `i j` and use `⟨one_entry_mem _ i j, one_entry_mem _ i j⟩`.
-/
theorem intG_one (D : D7) (N : ℕ) : IntG D ((1 : GA D N) : GL (Fin N) (AE D)) := fun i j =>
  ⟨one_entry_mem _ i j, one_entry_mem _ i j⟩

/- English proof (translation)
Take `⟨x, h1, h2, h3⟩` from `exists_idele D hk`. Use `⟨x, h1, ?_⟩` and prove the remaining obligations. Rewrite using `[om_vac_of_ideles he hT W hk (intG_one D d) x 1 h2 (fun q _ _ => by simpa using zeroAt_zero D q) h3 (by rw [part_one]; simp), map_one, _root_.one_zpow, one_mul]`.
-/
theorem om_vac_left (he : e0 ∈ Th D (tor0 D cc δ) (stdL D a) (stdL D d)) (hT : e0 ∈ TT D (tor0 D cc δ) a d)
    (W : WeilO D cc δ a d e0) {k : GA D a} (hk : IntG D (k : GL (Fin a) (AE D))) :
    ∃ x : (AE D)ˣ, IntU D x ∧ W.Om k 1 e0 = ((W.chV'.f x ^ W.ep' : ℂˣ) : ℂ) • e0 := by
  obtain ⟨x, h1, h2, h3⟩ := exists_idele D hk
  refine ⟨x, h1, ?_⟩
  rw [om_vac_of_ideles he hT W hk (intG_one D d) x 1 h2 (fun q _ _ => by simpa using zeroAt_zero D q) h3
    (by rw [part_one]; simp), map_one, _root_.one_zpow, one_mul]

/- English proof (translation)
Take `⟨x, h1, h2, h3⟩` from `exists_idele D hk'`. Use `⟨x, h1, ?_⟩` and prove the remaining obligations. Rewrite using `[om_vac_of_ideles he hT W (intG_one D a) hk' 1 x (fun q _ _ => by simpa using zeroAt_zero D q) h2 (by rw [part_one]; simp) h3, map_one, _root_.one_zpow, mul_one]`.
-/
theorem om_vac_right (he : e0 ∈ Th D (tor0 D cc δ) (stdL D a) (stdL D d)) (hT : e0 ∈ TT D (tor0 D cc δ) a d)
    (W : WeilO D cc δ a d e0) {k' : GA D d} (hk' : IntG D (k' : GL (Fin d) (AE D))) :
    ∃ x' : (AE D)ˣ, IntU D x' ∧ W.Om 1 k' e0 = ((W.chV.f x' ^ W.ep : ℂˣ) : ℂ) • e0 := by
  obtain ⟨x, h1, h2, h3⟩ := exists_idele D hk'
  refine ⟨x, h1, ?_⟩
  rw [om_vac_of_ideles he hT W (intG_one D a) hk' 1 x (fun q _ _ => by simpa using zeroAt_zero D q) h2
    (by rw [part_one]; simp) h3, map_one, _root_.one_zpow, mul_one]

end GlobalTheory.NormSum.VacInt
