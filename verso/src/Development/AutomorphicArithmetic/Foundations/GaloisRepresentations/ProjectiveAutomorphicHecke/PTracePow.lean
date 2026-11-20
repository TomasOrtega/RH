import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.MapWopWmap
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PProjTrace

open Module
universe u v

/- English proof (translation)
Introduce `F _ _ W _ _ _ q s hq hq0 hqs hinj j₀`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Establish `hU : ∀ x ∈ LinearMap.range q, s x ∈ LinearMap.range q`. Introduce and unpack `_ ⟨y, rfl⟩`.

Use `⟨s y, ?_⟩` and prove the remaining obligations. Use `LinearMap.congr_fun hqs.eq y` as an intermediate fact. Simplify `this` using `[Module.End.mul_apply]`. Establish `hUp : ∀ j : ℕ, ∀ x ∈ LinearMap.range q, (s ^ j) x ∈ LinearMap.range q`. Introduce `j`.

Proceed by induction on `j with`. Consider the case `zero => intro x hx`. Simplify using `using hx`. Consider the case `succ n ih`. Introduce `x hx`.

Rewrite using `[pow_succ', Module.End.mul_apply]`. Conclude with `hU _ (ih x hx)`. Use `set t : Module.End F (LinearMap.range q) := s.restrict hU with ht`. Establish `hres : ∀ j : ℕ, (s ^ j).restrict (hUp j) = t ^ j`. Introduce `j`.

Proceed by induction on `j with`. Consider the case `zero => ext x`. Simplify using the standard rewrite rules. Consider the case `succ n ih`. Use extensionality with `x`.

Rewrite using `[pow_succ' t, Module.End.mul_apply, ← ih]`. Simplify using `[LinearMap.restrict_apply, pow_succ', Module.End.mul_apply, ht]`. Establish `hproj : LinearMap.IsProj (LinearMap.range q) q`. Use `⟨fun x => ⟨x, rfl⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨y, rfl⟩`.

Use `LinearMap.congr_fun hq.eq y` as an intermediate fact. Simplify `this` using `[Module.End.mul_apply]`. Use `set a : ℕ → F := fun j => LinearMap.trace F (LinearMap.range q) (t ^ j) with ha`. Establish `htr : ∀ j, LinearMap.trace F W (q * s ^ j) = a j`. Introduce `j`.

Rewrite using `[LinearMap.trace_mul_comm, pProjTrace_holds F W _ q (s ^ j) hproj (hUp j), hres j]`. Establish `hzero : ∀ j, j₀ ≤ j → a j = 0` using `fun j hj => by rw [← htr j]; exact hcon j hj`. Establish `htinj : Function.Injective t`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce and unpack `⟨x, y, rfl⟩ hx`.

Establish `h1 : s (q y) = 0`. Use `congrArg Subtype.val hx` as an intermediate fact. Simplify `this` using `[ht, LinearMap.restrict_apply]`. Conclude with `Subtype.ext (by simpa using hinj y h1)`. Use `set P := minpoly F t with hP`.

Establish `hc0 : P.coeff 0 ≠ 0` using `LinearMap.minpoly_coeff_zero_of_injective htinj`. Establish `hrec : ∀ j, ∑ k ∈ Finset.range (P.natDegree + 1), P.coeff k * a (k + j) = 0`. Introduce `j`. Establish `h0 : Polynomial.aeval t P = 0` using `minpoly.aeval F t`. Rewrite `h0` using `[Polynomial.aeval_eq_sum_range]`.

Establish `h1` using `congrArg (fun f => LinearMap.trace F (LinearMap.range q) (f * t ^ j)) h0`. Simplify using `only [Finset.sum_mul, map_sum, zero_mul, map_zero, smul_mul_assoc, map_smul, ← pow_add, smul_eq_mul] at h1`. Simplify `h1` using `[ha]`. Establish `hall : ∀ n j, j₀ ≤ j + n → a j = 0`. Introduce `n`.

Proceed by induction on `n with`. Consider the case `zero => intro j hj; exact hzero j (by simpa using hj)`. Consider the case `succ n ih`. Introduce `j hj`. Establish `h` using `hrec j`.

Rewrite `h` using `[Finset.sum_range_succ']`. Establish `hs : ∑ k ∈ Finset.range P.natDegree, P.coeff (k + 1) * a (k + 1 + j) = 0`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Rewrite using `[ih (k + 1 + j) (by omega), mul_zero]`. Rewrite `h` using `[hs, zero_add, zero_add]`.

Conclude with `(mul_eq_zero.mp h).resolve_left hc0`. Establish `ha0 : a 0 = 0` using `hall j₀ 0 (by omega)`. Establish `hne : LinearMap.range q ≠ ⊥` using `fun h => hq0 (LinearMap.range_eq_bot.mp h)`. Establish `hpos : Module.finrank F (LinearMap.range q) ≠ 0` using `fun h => hne (Submodule.finrank_eq_zero.mp h)`. Simplify using `only [ha, pow_zero, LinearMap.trace_one] at ha0`.

Conclude with `(Nat.cast_ne_zero.mpr hpos) ha0`.
-/
theorem UpperTheory.Gal.CertificateRingHomMap.pTracePow_holds :
    UpperTheory.Gal.CertificateRingHomMap.TracePow.{u} := by
  intro F _ _ W _ _ _ q s hq hq0 hqs hinj j₀
  by_contra hcon
  push_neg at hcon
  have hU : ∀ x ∈ LinearMap.range q, s x ∈ LinearMap.range q := by
    rintro _ ⟨y, rfl⟩
    refine ⟨s y, ?_⟩
    have := LinearMap.congr_fun hqs.eq y
    simpa [Module.End.mul_apply] using this
  have hUp : ∀ j : ℕ, ∀ x ∈ LinearMap.range q, (s ^ j) x ∈ LinearMap.range q := by
    intro j
    induction j with
    | zero => intro x hx; simpa using hx
    | succ n ih =>
      intro x hx
      rw [pow_succ', Module.End.mul_apply]
      exact hU _ (ih x hx)
  set t : Module.End F (LinearMap.range q) := s.restrict hU with ht
  have hres : ∀ j : ℕ, (s ^ j).restrict (hUp j) = t ^ j := by
    intro j
    induction j with
    | zero => ext x; simp
    | succ n ih =>
      ext x
      rw [pow_succ' t, Module.End.mul_apply, ← ih]
      simp [LinearMap.restrict_apply, pow_succ', Module.End.mul_apply, ht]
  have hproj : LinearMap.IsProj (LinearMap.range q) q := by
    refine ⟨fun x => ⟨x, rfl⟩, ?_⟩
    rintro _ ⟨y, rfl⟩
    have := LinearMap.congr_fun hq.eq y
    simpa [Module.End.mul_apply] using this
  set a : ℕ → F := fun j => LinearMap.trace F (LinearMap.range q) (t ^ j) with ha
  have htr : ∀ j, LinearMap.trace F W (q * s ^ j) = a j := by
    intro j
    rw [LinearMap.trace_mul_comm, pProjTrace_holds F W _ q (s ^ j) hproj (hUp j), hres j]
  have hzero : ∀ j, j₀ ≤ j → a j = 0 := fun j hj => by rw [← htr j]; exact hcon j hj
  have htinj : Function.Injective t := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨x, y, rfl⟩ hx
    have h1 : s (q y) = 0 := by
      have := congrArg Subtype.val hx
      simpa [ht, LinearMap.restrict_apply] using this
    exact Subtype.ext (by simpa using hinj y h1)
  set P := minpoly F t with hP
  have hc0 : P.coeff 0 ≠ 0 := LinearMap.minpoly_coeff_zero_of_injective htinj
  have hrec : ∀ j, ∑ k ∈ Finset.range (P.natDegree + 1), P.coeff k * a (k + j) = 0 := by
    intro j
    have h0 : Polynomial.aeval t P = 0 := minpoly.aeval F t
    rw [Polynomial.aeval_eq_sum_range] at h0
    have h1 := congrArg (fun f => LinearMap.trace F (LinearMap.range q) (f * t ^ j)) h0
    simp only [Finset.sum_mul, map_sum, zero_mul, map_zero, smul_mul_assoc, map_smul,
      ← pow_add, smul_eq_mul] at h1
    simpa [ha] using h1
  have hall : ∀ n j, j₀ ≤ j + n → a j = 0 := by
    intro n
    induction n with
    | zero => intro j hj; exact hzero j (by simpa using hj)
    | succ n ih =>
      intro j hj
      have h := hrec j
      rw [Finset.sum_range_succ'] at h
      have hs : ∑ k ∈ Finset.range P.natDegree, P.coeff (k + 1) * a (k + 1 + j) = 0 := by
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [ih (k + 1 + j) (by omega), mul_zero]
      rw [hs, zero_add, zero_add] at h
      exact (mul_eq_zero.mp h).resolve_left hc0
  have ha0 : a 0 = 0 := hall j₀ 0 (by omega)
  have hne : LinearMap.range q ≠ ⊥ := fun h => hq0 (LinearMap.range_eq_bot.mp h)
  have hpos : Module.finrank F (LinearMap.range q) ≠ 0 :=
    fun h => hne (Submodule.finrank_eq_zero.mp h)
  simp only [ha, pow_zero, LinearMap.trace_one] at ha0
  exact (Nat.cast_ne_zero.mpr hpos) ha0
