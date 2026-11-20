import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.UnitTestFunctions.LiftUnit

noncomputable section
open NumberField IsDedekindDomain Topology
open PositivityTheory.RgEis PositivityTheory.RgEis.TF

namespace GlobalTheory.CompanionTheory.RgEis.InMTopPf

variable {k : Type} [Field k] [NumberField k]

/- English proof (translation)
Establish `: (M : FiniteAdeleRing (𝓞 k) k) = algebraMap k _ (M : k)` using `by simp`. Rewrite using `[this]`. Conclude with `(IsUnit.mk0 _ (by exact_mod_cast hM)).map _`.
-/
theorem natCast_isUnit (M : ℕ) (hM : M ≠ 0) : IsUnit (M : FiniteAdeleRing (𝓞 k) k) := by
  have : (M : FiniteAdeleRing (𝓞 k) k) = algebraMap k _ (M : k) := by simp
  rw [this]
  exact (IsUnit.mk0 _ (by exact_mod_cast hM)).map _

/- English proof (translation)
Use `set u := (natCast_isUnit (k := k) M hM).unit`. Establish `hu : (u : FiniteAdeleRing (𝓞 k) k) = M` using `rfl`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Rewrite using `[← hu, ← mul_assoc, Units.inv_mul, one_mul]`.

Conclude with `hy`. Introduce `h`. Use `⟨_, h, ?_⟩` and prove the remaining obligations. Rewrite using `[← hu, ← mul_assoc, Units.mul_inv, one_mul]`.
-/
theorem inM_iff (M : ℕ) (hM : M ≠ 0) (x : FiniteAdeleRing (𝓞 k) k) :
    InM M x ↔ (((natCast_isUnit (k := k) M hM).unit⁻¹ : (FiniteAdeleRing (𝓞 k) k)ˣ) :
      FiniteAdeleRing (𝓞 k) k) * x ∈ OH k := by
  set u := (natCast_isUnit (k := k) M hM).unit
  have hu : (u : FiniteAdeleRing (𝓞 k) k) = M := rfl
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [← hu, ← mul_assoc, Units.inv_mul, one_mul]; exact hy
  · intro h
    refine ⟨_, h, ?_⟩
    rw [← hu, ← mul_assoc, Units.mul_inv, one_mul]

/- English proof (translation)
Establish `hS : {x : FiniteAdeleRing (𝓞 k) k | InM M x} = (fun x => (((natCast_isUnit (k` using `k) M hM).unit⁻¹ : (FiniteAdeleRing (𝓞 k) k)ˣ) : FiniteAdeleRing (𝓞 k) k) * x) ⁻¹' (OH k : Set (FiniteAdeleRing (𝓞 k) k)) := by`. Use extensionality with `x`. Conclude with `inM_iff M hM x`. Establish `hc : Continuous (fun x : FiniteAdeleRing (𝓞 k) k => (((natCast_isUnit (k` using `k) M hM).unit⁻¹ : (FiniteAdeleRing (𝓞 k) k)ˣ) : FiniteAdeleRing (𝓞 k) k) * x) := continuous_const.mul continuous_id`. Establish `ho : IsOpen (OH k : Set (FiniteAdeleRing (𝓞 k) k))` using `GroundTheory.Global.isOpen_integralFiniteAdeles`.

Rewrite using `[hS]`. Conclude with `⟨ho.preimage hc, (AddSubgroup.isClosed_of_isOpen (OH k).toAddSubgroup ho).preimage hc⟩`.
-/
theorem isOpen_isClosed (M : ℕ) (hM : M ≠ 0) :
    IsOpen {x : FiniteAdeleRing (𝓞 k) k | InM M x} ∧ IsClosed {x : FiniteAdeleRing (𝓞 k) k | InM M x} := by
  have hS : {x : FiniteAdeleRing (𝓞 k) k | InM M x} =
      (fun x => (((natCast_isUnit (k := k) M hM).unit⁻¹ : (FiniteAdeleRing (𝓞 k) k)ˣ) :
        FiniteAdeleRing (𝓞 k) k) * x) ⁻¹' (OH k : Set (FiniteAdeleRing (𝓞 k) k)) := by
    ext x; exact inM_iff M hM x
  have hc : Continuous (fun x : FiniteAdeleRing (𝓞 k) k =>
      (((natCast_isUnit (k := k) M hM).unit⁻¹ : (FiniteAdeleRing (𝓞 k) k)ˣ) : FiniteAdeleRing (𝓞 k) k) * x) :=
    continuous_const.mul continuous_id
  have ho : IsOpen (OH k : Set (FiniteAdeleRing (𝓞 k) k)) := GroundTheory.Global.isOpen_integralFiniteAdeles
  rw [hS]
  exact ⟨ho.preimage hc, (AddSubgroup.isClosed_of_isOpen (OH k).toAddSubgroup ho).preimage hc⟩

/- English proof (translation)
Break down `eq_or_ne c 0 with rfl | hc0` into its components or cases. Conclude with `⟨1, by simpa using (zero_lt_iff.mpr ha)⟩`. Take `⟨α, rfl⟩` from `WithZero.ne_zero_iff_exists.mp hc0`. Take `⟨β, rfl⟩` from `WithZero.ne_zero_iff_exists.mp ha`. Establish `hα : Multiplicative.toAdd α < 0`.

Establish `h1 : ((α : WithZero (Multiplicative ℤ))) < ((1 : Multiplicative ℤ) : WithZero (Multiplicative ℤ))`. Simplify using `using hc`. Rewrite `h1` using `[WithZero.coe_lt_coe]`. Conclude with `h1`. Use `⟨(Multiplicative.toAdd β).natAbs + 1, ?_⟩` and prove the remaining obligations.

Rewrite using `[← WithZero.coe_pow, WithZero.coe_lt_coe]`. Use `show Multiplicative.toAdd (α ^ ((Multiplicative.toAdd β).natAbs + 1)) < Multiplicative.toAdd β`. Rewrite using `[toAdd_pow, nsmul_eq_mul]`. Use `set a := Multiplicative.toAdd α`. Use `set b := Multiplicative.toAdd β`.

Establish `ha1 : a ≤ -1` using `by omega`. Establish `h3 : (((b.natAbs + 1 : ℕ) : ℤ)) * a ≤ -(((b.natAbs + 1 : ℕ) : ℤ))`. Establish `: (0 : ℤ) ≤ ((b.natAbs + 1 : ℕ) : ℤ)` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities. Move the coercions through the operations in `at h3 ⊢`.

Establish `h4` using `neg_abs_le b`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_pow_lt' {c a : WithZero (Multiplicative ℤ)} (ha : a ≠ 0) (hc : c < 1) : ∃ n : ℕ, c ^ n < a := by
  rcases eq_or_ne c 0 with rfl | hc0
  · exact ⟨1, by simpa using (zero_lt_iff.mpr ha)⟩
  obtain ⟨α, rfl⟩ := WithZero.ne_zero_iff_exists.mp hc0
  obtain ⟨β, rfl⟩ := WithZero.ne_zero_iff_exists.mp ha
  have hα : Multiplicative.toAdd α < 0 := by
    have h1 : ((α : WithZero (Multiplicative ℤ))) < ((1 : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
      simpa using hc
    rw [WithZero.coe_lt_coe] at h1
    exact h1
  refine ⟨(Multiplicative.toAdd β).natAbs + 1, ?_⟩
  rw [← WithZero.coe_pow, WithZero.coe_lt_coe]
  show Multiplicative.toAdd (α ^ ((Multiplicative.toAdd β).natAbs + 1)) < Multiplicative.toAdd β
  rw [toAdd_pow, nsmul_eq_mul]
  set a := Multiplicative.toAdd α
  set b := Multiplicative.toAdd β
  have ha1 : a ≤ -1 := by omega
  have h3 : (((b.natAbs + 1 : ℕ) : ℤ)) * a ≤ -(((b.natAbs + 1 : ℕ) : ℤ)) := by
    have : (0 : ℤ) ≤ ((b.natAbs + 1 : ℕ) : ℤ) := by positivity
    nlinarith
  push_cast at h3 ⊢
  have h4 := neg_abs_le b
  linarith

/- English proof (translation)
Rewrite using `[← map_natCast (algebraMap k (FiniteAdeleRing (𝓞 k) k)) M, FiniteAdeleRing.algebraMap_apply]`. Conclude with `map_natCast (algebraMap k (v.adicCompletion k)) M`.
-/
theorem natCast_apply' (v : HeightOneSpectrum (𝓞 k)) (M : ℕ) :
    (M : FiniteAdeleRing (𝓞 k) k) v = (M : v.adicCompletion k) := by
  rw [← map_natCast (algebraMap k (FiniteAdeleRing (𝓞 k) k)) M, FiniteAdeleRing.algebraMap_apply]
  exact map_natCast (algebraMap k (v.adicCompletion k)) M

/- English proof (translation)
Use `HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := k) v (n : 𝓞 k)` as an intermediate fact. Rewrite `this` using `[HeightOneSpectrum.valuation_of_algebraMap]`. Rewrite using `[← this]`. Use `congr 1`. Simplify using the standard rewrite rules.
-/
theorem valued_natCast (v : HeightOneSpectrum (𝓞 k)) (n : ℕ) :
    Valued.v (n : v.adicCompletion k) = v.intValuation (n : 𝓞 k) := by
  have := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := k) v (n : 𝓞 k)
  rw [HeightOneSpectrum.valuation_of_algebraMap] at this
  rw [← this]
  congr 1
  simp

/- English proof (translation)
Use `Subtype.ext (funext fun v => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `x v = 0`. Assume the negation of the conclusion as `hxv`. Use `set N : ℕ := Ideal.absNorm v.asIdeal with hN`. Establish `hN0 : N ≠ 0`.

Rewrite using `[hN, Ne, Ideal.absNorm_eq_zero_iff]`. Conclude with `v.ne_bot`. Establish `hNmem : (N : 𝓞 k) ∈ v.asIdeal` using `Ideal.absNorm_mem v.asIdeal`. Establish `hlt : v.intValuation (N : 𝓞 k) < 1` using `(v.intValuation_lt_one_iff_mem _).mpr hNmem`. Establish `hxv0 : Valued.v (x v) ≠ 0` using `by simpa using hxv`.

Take `⟨n, hn⟩` from `exists_pow_lt' hxv0 hlt`. Take `⟨y, hy, hxy⟩` from `hx (N ^ n) (pow_ne_zero _ hN0)`. Establish `hcomp : x v = ((N ^ n : ℕ) : v.adicCompletion k) * y v`. Rewrite using `[hxy]`. Establish `h1` using `natCast_apply' v (N ^ n)`.

Express the relevant statement in the definitionally equal form `((N ^ n : ℕ) : FiniteAdeleRing (𝓞 k) k) v * y v = _`. Rewrite using `[h1]`. Establish `hyv : Valued.v (y v) ≤ 1` using `(HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).mp (hy v)`. Establish `hle : Valued.v (x v) ≤ v.intValuation (N : 𝓞 k) ^ n`. Rewrite using `[hcomp, map_mul, valued_natCast, Nat.cast_pow, map_pow]`.

Conclude with `mul_le_of_le_one_right' hyv`. Conclude with `absurd (lt_of_le_of_lt hle hn) (lt_irrefl _)`.
-/
theorem eq_zero_of_forall_inM (x : FiniteAdeleRing (𝓞 k) k) (hx : ∀ M : ℕ, M ≠ 0 → InM M x) : x = 0 := by
  refine Subtype.ext (funext fun v => ?_)
  change x v = 0
  by_contra hxv
  set N : ℕ := Ideal.absNorm v.asIdeal with hN
  have hN0 : N ≠ 0 := by
    rw [hN, Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have hNmem : (N : 𝓞 k) ∈ v.asIdeal := Ideal.absNorm_mem v.asIdeal
  have hlt : v.intValuation (N : 𝓞 k) < 1 := (v.intValuation_lt_one_iff_mem _).mpr hNmem
  have hxv0 : Valued.v (x v) ≠ 0 := by simpa using hxv
  obtain ⟨n, hn⟩ := exists_pow_lt' hxv0 hlt
  obtain ⟨y, hy, hxy⟩ := hx (N ^ n) (pow_ne_zero _ hN0)
  have hcomp : x v = ((N ^ n : ℕ) : v.adicCompletion k) * y v := by
    rw [hxy]
    have h1 := natCast_apply' v (N ^ n)
    change ((N ^ n : ℕ) : FiniteAdeleRing (𝓞 k) k) v * y v = _
    rw [h1]
  have hyv : Valued.v (y v) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).mp (hy v)
  have hle : Valued.v (x v) ≤ v.intValuation (N : 𝓞 k) ^ n := by
    rw [hcomp, map_mul, valued_natCast, Nat.cast_pow, map_pow]
    exact mul_le_of_le_one_right' hyv
  exact absurd (lt_of_le_of_lt hle hn) (lt_irrefl _)

/- English proof (translation)
Introduce `k _ _` and use `⟨fun M hM => isOpen_isClosed M hM, fun x hx => eq_zero_of_forall_inM x hx⟩`.
-/
theorem inMTop : InMTop := fun k _ _ =>
  ⟨fun M hM => isOpen_isClosed M hM, fun x hx => eq_zero_of_forall_inM x hx⟩

end GlobalTheory.CompanionTheory.RgEis.InMTopPf
