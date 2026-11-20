import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.ChainRows
import Development.AutomorphicSpectrum.Definitions.NonGaloisLines.TopLine
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.GoodOAdicCompleteCompactBasisStatement
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.ExistsDualLatticesStatement

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.CompanionTheory.LocDual

noncomputable section

namespace GlobalTheory.CompanionTheory.LocDual.Top

section Hom

variable {O LL : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field LL] [Algebra O LL]
  [IsFractionRing O LL]

/- English proof (translation)
Take `⟨p, hp⟩ : ∃ p : LL, p = algebraMap O LL ϖ` from `⟨_, rfl⟩`. Establish `hp0 : p ≠ 0` using `fun h => hϖ.ne_zero (IsFractionRing.injective O LL (by simpa [hp] using h))`. Establish `hmem : ∀ x : LL, x ∈ T ↔ ∃ o : O, algebraMap O LL o = x`. Introduce `x`. Rewrite using `[hT]`.

Simplify using `[LinearMap.mem_range]`. Use `choose u hu using fun n : ℕ => Submodule.Quotient.mk_surjective T (ψ ((p⁻¹) ^ n))`. Establish `step : ∀ n, ∃ o : O, algebraMap O LL o = p * u (n + 1) - u n`. Introduce `n`. Rewrite using `[← hmem, ← Submodule.Quotient.eq]`.

Establish `h1 : (Submodule.Quotient.mk (p * u (n + 1)) : LL ⧸ T) = ϖ • Submodule.Quotient.mk (u (n + 1))`. Rewrite using `[← Submodule.Quotient.mk_smul, Algebra.smul_def, hp]`. Rewrite using `[h1, hu, hu, ← map_smul, Algebra.smul_def, ← hp]`. Use `congr 1`. Rewrite using `[pow_succ]`.

Clear the denominators using the available nonvanishing facts. Use `choose o ho using step`. Take `⟨y, hyd⟩ : ∃ y : ℕ → O, y = fun n => ∑ i ∈ Finset.range n, ϖ ^ i * o i` from `⟨_, rfl⟩`. Establish `hys : ∀ n, y (n + 1) = y n + ϖ ^ n * o n`. Introduce `n`.

Simplify using `[hyd, Finset.sum_range_succ]`. Establish `hy0 : y 0 = 0` using `by simp [hyd]`. Establish `hy : ∀ n, p ^ n * u n = u 0 + algebraMap O LL (y n)`. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero => simp [hy0]`. Consider the case `succ n ih`. Establish `h2 : p ^ (n + 1) * u (n + 1) = p ^ n * u n + p ^ n * (p * u (n + 1) - u n)` using `by ring`. Rewrite using `[h2, ih, ← ho n, hys, map_add, map_mul, map_pow, ← hp]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hI : ∀ m, ((Ideal.span {ϖ}) ^ m • ⊤ : Submodule O O) = Ideal.span {ϖ ^ m}`. Introduce `m`. Simplify using `[Ideal.span_singleton_pow]`. Establish `hcauchy : ∀ {m n}, m ≤ n → y m ≡ y n [SMOD ((Ideal.span {ϖ}) ^ m • ⊤ : Submodule O O)]`. Introduce `m n hmn`.

Rewrite using `[SModEq.sub_mem, hI, Ideal.mem_span_singleton]`. Proceed by induction on `n, hmn using Nat.le_induction with`. Consider the case `base => simp`. Consider the case `succ n hmn ih`. Rewrite using `[hys]`.

Establish `h3 : y m - (y n + ϖ ^ n * o n) = (y m - y n) - ϖ ^ n * o n` using `by ring`. Rewrite using `[h3]`. Conclude with `dvd_sub ih (Dvd.dvd.mul_right (pow_dvd_pow _ hmn) _)`. Take `⟨Y, hY⟩` from `IsPrecomplete.prec hc.toIsPrecomplete hcauchy`. Use `⟨u 0 + algebraMap O LL Y, ?_⟩` and prove the remaining obligations.

Establish `hpow : ∀ n, ψ ((p⁻¹) ^ n) = Submodule.Quotient.mk ((p⁻¹) ^ n * (u 0 + algebraMap O LL Y))`. Introduce `n`. Rewrite using `[← hu, Submodule.Quotient.eq, hmem]`. Establish `h4` using `hY n`. Rewrite `h4` using `[SModEq.sub_mem, hI, Ideal.mem_span_singleton]`.

Take `⟨t, ht⟩` from `h4`. Use `⟨t, ?_⟩` and prove the remaining obligations. Establish `h5 : algebraMap O LL (y n) - algebraMap O LL Y = p ^ n * algebraMap O LL t`. Rewrite using `[← map_sub, ht, map_mul, map_pow, ← hp]`. Establish `h6 : u n = (p⁻¹) ^ n * (u 0 + algebraMap O LL (y n))`.

Rewrite using `[← hy, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hp0, one_pow, one_mul]`. Rewrite using `[h6, ← mul_sub]`. Establish `h7 : u 0 + algebraMap O LL (y n) - (u 0 + algebraMap O LL Y) = p ^ n * algebraMap O LL t`. Rewrite using `[← h5]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[h7, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hp0, one_pow, one_mul]`. Introduce `a`. Take `⟨x, w, hw, rfl⟩` from `IsFractionRing.div_surjective (A := O) a`. Establish `hw0 : w ≠ 0` using `nonZeroDivisors.ne_zero hw`. Take `⟨n, e, he⟩` from `IsDiscreteValuationRing.associated_pow_irreducible hw0 hϖ`.

Establish `hw1 : algebraMap O LL w ≠ 0` using `fun h => hw0 (IsFractionRing.injective O LL (by simpa using h))`. Establish `ha : algebraMap O LL x / algebraMap O LL w = (x * e) • (p⁻¹) ^ n`. Rewrite using `[Algebra.smul_def, map_mul, div_eq_iff hw1]`. Establish `h8 : p ^ n = algebraMap O LL w * algebraMap O LL (e : O)`. Rewrite using `[hp, ← map_pow, ← he, map_mul]`.

Establish `h9 : p ^ n ≠ 0` using `pow_ne_zero _ hp0`. Rewrite using `[inv_pow]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[h8]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[ha, map_smul, hpow, ← Submodule.Quotient.mk_smul, Algebra.smul_def, Algebra.smul_def, mul_assoc]`.
-/
theorem exists_mul_of_linear (T : Submodule O LL) (hT : T = LinearMap.range (Algebra.linearMap O LL))
    {ϖ : O} (hϖ : Irreducible ϖ) (hc : IsAdicComplete (Ideal.span {ϖ}) O) (ψ : LL →ₗ[O] LL ⧸ T) :
    ∃ u : LL, ∀ a, ψ a = Submodule.Quotient.mk (a * u) := by
  obtain ⟨p, hp⟩ : ∃ p : LL, p = algebraMap O LL ϖ := ⟨_, rfl⟩
  have hp0 : p ≠ 0 := fun h => hϖ.ne_zero (IsFractionRing.injective O LL (by simpa [hp] using h))
  have hmem : ∀ x : LL, x ∈ T ↔ ∃ o : O, algebraMap O LL o = x := by
    intro x
    rw [hT]
    simp [LinearMap.mem_range]
  choose u hu using fun n : ℕ => Submodule.Quotient.mk_surjective T (ψ ((p⁻¹) ^ n))
  have step : ∀ n, ∃ o : O, algebraMap O LL o = p * u (n + 1) - u n := by
    intro n
    rw [← hmem, ← Submodule.Quotient.eq]
    have h1 : (Submodule.Quotient.mk (p * u (n + 1)) : LL ⧸ T) =
        ϖ • Submodule.Quotient.mk (u (n + 1)) := by
      rw [← Submodule.Quotient.mk_smul, Algebra.smul_def, hp]
    rw [h1, hu, hu, ← map_smul, Algebra.smul_def, ← hp]
    congr 1
    rw [pow_succ]
    field_simp
  choose o ho using step
  obtain ⟨y, hyd⟩ : ∃ y : ℕ → O, y = fun n => ∑ i ∈ Finset.range n, ϖ ^ i * o i := ⟨_, rfl⟩
  have hys : ∀ n, y (n + 1) = y n + ϖ ^ n * o n := by
    intro n
    simp [hyd, Finset.sum_range_succ]
  have hy0 : y 0 = 0 := by simp [hyd]
  have hy : ∀ n, p ^ n * u n = u 0 + algebraMap O LL (y n) := by
    intro n
    induction n with
    | zero => simp [hy0]
    | succ n ih =>
      have h2 : p ^ (n + 1) * u (n + 1) = p ^ n * u n + p ^ n * (p * u (n + 1) - u n) := by ring
      rw [h2, ih, ← ho n, hys, map_add, map_mul, map_pow, ← hp]
      ring
  have hI : ∀ m, ((Ideal.span {ϖ}) ^ m • ⊤ : Submodule O O) = Ideal.span {ϖ ^ m} := by
    intro m
    simp [Ideal.span_singleton_pow]
  have hcauchy : ∀ {m n}, m ≤ n → y m ≡ y n [SMOD ((Ideal.span {ϖ}) ^ m • ⊤ : Submodule O O)] := by
    intro m n hmn
    rw [SModEq.sub_mem, hI, Ideal.mem_span_singleton]
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      rw [hys]
      have h3 : y m - (y n + ϖ ^ n * o n) = (y m - y n) - ϖ ^ n * o n := by ring
      rw [h3]
      exact dvd_sub ih (Dvd.dvd.mul_right (pow_dvd_pow _ hmn) _)
  obtain ⟨Y, hY⟩ := IsPrecomplete.prec hc.toIsPrecomplete hcauchy
  refine ⟨u 0 + algebraMap O LL Y, ?_⟩
  have hpow : ∀ n, ψ ((p⁻¹) ^ n) = Submodule.Quotient.mk ((p⁻¹) ^ n * (u 0 + algebraMap O LL Y)) := by
    intro n
    rw [← hu, Submodule.Quotient.eq, hmem]
    have h4 := hY n
    rw [SModEq.sub_mem, hI, Ideal.mem_span_singleton] at h4
    obtain ⟨t, ht⟩ := h4
    refine ⟨t, ?_⟩
    have h5 : algebraMap O LL (y n) - algebraMap O LL Y = p ^ n * algebraMap O LL t := by
      rw [← map_sub, ht, map_mul, map_pow, ← hp]
    have h6 : u n = (p⁻¹) ^ n * (u 0 + algebraMap O LL (y n)) := by
      rw [← hy, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hp0, one_pow, one_mul]
    rw [h6, ← mul_sub]
    have h7 : u 0 + algebraMap O LL (y n) - (u 0 + algebraMap O LL Y) = p ^ n * algebraMap O LL t := by
      rw [← h5]
      ring
    rw [h7, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hp0, one_pow, one_mul]
  intro a
  obtain ⟨x, w, hw, rfl⟩ := IsFractionRing.div_surjective (A := O) a
  have hw0 : w ≠ 0 := nonZeroDivisors.ne_zero hw
  obtain ⟨n, e, he⟩ := IsDiscreteValuationRing.associated_pow_irreducible hw0 hϖ
  have hw1 : algebraMap O LL w ≠ 0 := fun h => hw0 (IsFractionRing.injective O LL (by simpa using h))
  have ha : algebraMap O LL x / algebraMap O LL w = (x * e) • (p⁻¹) ^ n := by
    rw [Algebra.smul_def, map_mul, div_eq_iff hw1]
    have h8 : p ^ n = algebraMap O LL w * algebraMap O LL (e : O) := by
      rw [hp, ← map_pow, ← he, map_mul]
    have h9 : p ^ n ≠ 0 := pow_ne_zero _ hp0
    rw [inv_pow]
    field_simp
    rw [h8]
    ring
  rw [ha, map_smul, hpow, ← Submodule.Quotient.mk_smul, Algebra.smul_def, Algebra.smul_def, mul_assoc]

end Hom

section Red

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL : Type} [Field LL] [Algebra Qp LL] {O : Type} [CommRing O] [Algebra O LL]

def red (L1 : Lattice (O := O) (charRep (cycLL PD LL))) : (G × G → LL) →ₗ[O] (G × G → LL ⧸ L1.T) :=
  LinearMap.compLeft L1.T.mkQ (G × G)

def Zc (L1 : Lattice (O := O) (charRep (cycLL PD LL))) : Submodule O (G × G → LL) :=
  (ReciprocityTheory.Def.Z2 (repD L1) ⊤).comap (red L1)

def cls (L1 : Lattice (O := O) (charRep (cycLL PD LL))) : Zc L1 →ₗ[O] ReciprocityTheory.Def.H2 (repD L1) ⊤ :=
  (Submodule.mkQ _) ∘ₗ ((red L1).restrict (q := ReciprocityTheory.Def.Z2 (repD L1) ⊤) (fun _ h => h))

/- English proof (translation)
Simplify using `only [cls, LinearMap.comp_apply, Submodule.mkQ_apply]`. Rewrite using `[Submodule.Quotient.mk_eq_zero]`. Both sides reduce to the same expression.
-/
theorem cls_eq_zero_iff (L1 : Lattice (O := O) (charRep (cycLL PD LL))) (w : Zc L1) :
    cls L1 w = 0 ↔ CobO PD L1 (w : G × G → LL) := by
  simp only [cls, LinearMap.comp_apply, Submodule.mkQ_apply]
  rw [Submodule.Quotient.mk_eq_zero]
  rfl

/- English proof (translation)
Use `⟨⟨?_, fun _ => trivial⟩, ?_⟩` and prove the remaining obligations. Introduce `s`. Establish `h1 : IsOpen ((Submodule.Quotient.mk : LL → LL ⧸ L1.T) ⁻¹' s)`. Rewrite using `[isOpen_iff_forall_mem_open]`. Introduce `y hy`.

Use `⟨(fun t => t - y) ⁻¹' (L1.T : Set LL), ?_, hop.preimage (by fun_prop), ?_⟩` and prove the remaining obligations. Introduce `t ht`. Establish `h2 : (Submodule.Quotient.mk t : LL ⧸ L1.T) = Submodule.Quotient.mk y` using `(Submodule.Quotient.eq _).2 ht`. Simplify `hy` using `[Set.mem_preimage, h2]`. Simplify using `[Set.mem_preimage]`.

Conclude with `h1.preimage hz`. Use extensionality with `x`. Establish `h3` using `congrFun hd x`. Establish `h4 : (Submodule.Quotient.mk (ReciprocityTheory.Def.d2 (charRep (cycLL PD LL)) z x) : LL ⧸ L1.T) = 0`. Rewrite using `[h3]`.

Simplify using the standard rewrite rules. Conclude with `h4`.
-/
theorem mem_Zc [TopologicalSpace LL] [IsTopologicalRing LL]
    (L1 : Lattice (O := O) (charRep (cycLL PD LL)))
    (hop : IsOpen (L1.T : Set LL)) {z : G × G → LL} (hz : Continuous z)
    (hd : ReciprocityTheory.Def.d2 (charRep (cycLL PD LL)) z = 0) : z ∈ Zc L1 := by
  refine ⟨⟨?_, fun _ => trivial⟩, ?_⟩
  · intro s
    have h1 : IsOpen ((Submodule.Quotient.mk : LL → LL ⧸ L1.T) ⁻¹' s) := by
      rw [isOpen_iff_forall_mem_open]
      intro y hy
      refine ⟨(fun t => t - y) ⁻¹' (L1.T : Set LL), ?_, hop.preimage (by fun_prop), ?_⟩
      · intro t ht
        have h2 : (Submodule.Quotient.mk t : LL ⧸ L1.T) = Submodule.Quotient.mk y :=
          (Submodule.Quotient.eq _).2 ht
        simpa [Set.mem_preimage, h2] using hy
      · simp [Set.mem_preimage]
    exact h1.preimage hz
  · ext x
    have h3 := congrFun hd x
    have h4 : (Submodule.Quotient.mk (ReciprocityTheory.Def.d2 (charRep (cycLL PD LL)) z x) : LL ⧸ L1.T) = 0 := by
      rw [h3]
      simp
    exact h4

/- English proof (translation)
Establish `hsm : ∀ {w : G × G → LL}, Continuous w → ReciprocityTheory.Def.d2 (charRep (cycLL PD LL)) w = 0 → ∀ a : LL, a • w ∈ Zc L1`. Introduce `w hw hdw a`. Use `mem_Zc L1 hop (hw.const_smul a) ?_` and prove the remaining obligations. Rewrite using `[map_smul, hdw, smul_zero]`. Establish `key : ∀ {w : G × G → LL} (hw : Continuous w) (hdw : ReciprocityTheory.Def.d2 (charRep (cycLL PD LL)) w = 0), ∃ u : LL, ∀ a : LL, φ (cls L1 ⟨a • w, hsm hw hdw a⟩) = Submodule.Quotient.mk (a * u)`.

Introduce `w hw hdw`. Set `ι : LL →ₗ[O] Zc L1` to `{ toFun := fun a => ⟨a • w, hsm hw hdw a⟩ map_add' := fun a b => Subtype.ext (add_smul a b w) map_smul' := fun r a => Subtype.ext (by`. Use extensionality with `x`. Simplify using `[Algebra.smul_def, mul_assoc]) }`. Conclude with `exists_mul_of_linear L1.T hT hϖ hc ((φ.toLinearMap ∘ₗ cls L1) ∘ₗ ι)`.

Take `⟨u, hu⟩` from `key hz hd`. Take `⟨u', hu'⟩` from `key hz' hd'`. Establish `hu0 : u ≠ 0`. Introduce and unpack `rfl`. Apply `hn` to reduce the goal to its premises.

Rewrite using `[hC z hz]`. Introduce `a`. Establish `h1` using `hu a`. Rewrite `h1` using `[mul_zero, Submodule.Quotient.mk_zero, map_eq_zero_iff φ φ.injective, cls_eq_zero_iff]`. Conclude with `h1`.

Use `⟨u' / u, ?_⟩` and prove the remaining obligations. Establish `hwc : Continuous (z' - (u' / u) • z)` using `hz'.sub (hz.const_smul _)`. Establish `hdw : ReciprocityTheory.Def.d2 (charRep (cycLL PD LL)) (z' - (u' / u) • z) = 0`. Rewrite using `[map_sub, map_smul, hd, hd', smul_zero, sub_zero]`. Rewrite using `[hC _ hwc]`.

Introduce `b`. Establish `h2 : (⟨b • (z' - (u' / u) • z), hsm hwc hdw b⟩ : Zc L1) = ⟨b • z', hsm hz' hd' b⟩ - ⟨(b * (u' / u)) • z, hsm hz hd _⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[smul_sub, mul_smul]`. Establish `h3 : φ (cls L1 ⟨b • (z' - (u' / u) • z), hsm hwc hdw b⟩) = 0`.

Rewrite using `[h2, map_sub, map_sub, hu, hu', ← Submodule.Quotient.mk_sub]`. Establish `h4 : b * u' - b * (u' / u) * u = 0`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h4, Submodule.Quotient.mk_zero]`.

Rewrite `h3` using `[map_eq_zero_iff φ φ.injective, cls_eq_zero_iff]`. Conclude with `h3`.
-/
theorem topLine_at [TopologicalSpace LL] [IsTopologicalRing LL] [IsDomain O] [IsDiscreteValuationRing O]
    [IsFractionRing O LL] (L1 : Lattice (O := O) (charRep (cycLL PD LL)))
    (hT : L1.T = LinearMap.range (Algebra.linearMap O LL)) (hop : IsOpen (L1.T : Set LL))
    {ϖ : O} (hϖ : Irreducible ϖ) (hc : IsAdicComplete (Ideal.span {ϖ}) O)
    (φ : ReciprocityTheory.Def.H2 (repD L1) ⊤ ≃ₗ[O] (LL ⧸ L1.T))
    (hC : ∀ z : G × G → LL, Continuous z → (CobL PD z ↔ ∀ a : LL, CobO PD L1 (a • z)))
    {z z' : G × G → LL} (hz : Continuous z) (hz' : Continuous z')
    (hd : ReciprocityTheory.Def.d2 (charRep (cycLL PD LL)) z = 0)
    (hd' : ReciprocityTheory.Def.d2 (charRep (cycLL PD LL)) z' = 0) (hn : ¬ CobL PD z) :
    ∃ a : LL, CobL PD (z' - a • z) := by
  have hsm : ∀ {w : G × G → LL}, Continuous w → ReciprocityTheory.Def.d2 (charRep (cycLL PD LL)) w = 0 →
      ∀ a : LL, a • w ∈ Zc L1 := by
    intro w hw hdw a
    refine mem_Zc L1 hop (hw.const_smul a) ?_
    rw [map_smul, hdw, smul_zero]
  have key : ∀ {w : G × G → LL} (hw : Continuous w) (hdw : ReciprocityTheory.Def.d2 (charRep (cycLL PD LL)) w = 0),
      ∃ u : LL, ∀ a : LL, φ (cls L1 ⟨a • w, hsm hw hdw a⟩) = Submodule.Quotient.mk (a * u) := by
    intro w hw hdw
    let ι : LL →ₗ[O] Zc L1 :=
      { toFun := fun a => ⟨a • w, hsm hw hdw a⟩
        map_add' := fun a b => Subtype.ext (add_smul a b w)
        map_smul' := fun r a => Subtype.ext (by
          ext x
          simp [Algebra.smul_def, mul_assoc]) }
    exact exists_mul_of_linear L1.T hT hϖ hc ((φ.toLinearMap ∘ₗ cls L1) ∘ₗ ι)
  obtain ⟨u, hu⟩ := key hz hd
  obtain ⟨u', hu'⟩ := key hz' hd'
  have hu0 : u ≠ 0 := by
    rintro rfl
    apply hn
    rw [hC z hz]
    intro a
    have h1 := hu a
    rw [mul_zero, Submodule.Quotient.mk_zero, map_eq_zero_iff φ φ.injective, cls_eq_zero_iff] at h1
    exact h1
  refine ⟨u' / u, ?_⟩
  have hwc : Continuous (z' - (u' / u) • z) := hz'.sub (hz.const_smul _)
  have hdw : ReciprocityTheory.Def.d2 (charRep (cycLL PD LL)) (z' - (u' / u) • z) = 0 := by
    rw [map_sub, map_smul, hd, hd', smul_zero, sub_zero]
  rw [hC _ hwc]
  intro b
  have h2 : (⟨b • (z' - (u' / u) • z), hsm hwc hdw b⟩ : Zc L1) =
      ⟨b • z', hsm hz' hd' b⟩ - ⟨(b * (u' / u)) • z, hsm hz hd _⟩ := by
    apply Subtype.ext
    simp [smul_sub, mul_smul]
  have h3 : φ (cls L1 ⟨b • (z' - (u' / u) • z), hsm hwc hdw b⟩) = 0 := by
    rw [h2, map_sub, map_sub, hu, hu', ← Submodule.Quotient.mk_sub]
    have h4 : b * u' - b * (u' / u) * u = 0 := by
      field_simp
      ring
    rw [h4, Submodule.Quotient.mk_zero]
  rw [map_eq_zero_iff φ φ.injective, cls_eq_zero_iff] at h3
  exact h3

end Red

/- English proof (translation)
Introduce `D l _ K hT hC LL _ _ _ O _ _ hO z z' hz hz' hd hd' hn`. Take `⟨L1, hL1⟩` from `(GlobalTheory.T.exists_dual_lattices D l K).1 LL O hO`. Take `⟨⟨hD, hDVR, hFrac⟩, -, -, htr, hopen⟩` from `id hO`. Use `haveI := hD`. Use `haveI := hDVR`.

Use `haveI := hFrac`. Use `haveI := htr`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Establish `hc` using `(GlobalTheory.T.goodO_adic_complete_compact_basis l LL O hO ϖ hϖ).1`. Establish `hop : IsOpen (L1.T : Set LL)`.

Establish `: (L1.T : Set LL) = Set.range (algebraMap O LL)`. Rewrite using `[hL1]`. Use extensionality with `x`. Simplify using `[LinearMap.mem_range]`. Rewrite using `[this]`.

Conclude with `hopen`. Take `⟨φ⟩` from `hT LL O hO L1 hL1`. Conclude with `topLine_at L1 hL1 hop hϖ hc φ (hC LL O hO L1 hL1) hz hz' hd hd' hn`.
-/
theorem h2_line_of_tate_h2_and_coboundaries : ∀ (D : D7) (l : ℕ) [Fact l.Prime] (K : FinExt l),
    LocalTateTopDegree ((D.loc l).PD K) → CobLO ((D.loc l).PD K) → TopLine ((D.loc l).PD K) := by
  intro D l _ K hT hC LL _ _ _ O _ _ hO z z' hz hz' hd hd' hn
  obtain ⟨L1, hL1⟩ := (GlobalTheory.T.exists_dual_lattices D l K).1 LL O hO
  obtain ⟨⟨hD, hDVR, hFrac⟩, -, -, htr, hopen⟩ := id hO
  haveI := hD
  haveI := hDVR
  haveI := hFrac
  haveI := htr
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hc := (GlobalTheory.T.goodO_adic_complete_compact_basis l LL O hO ϖ hϖ).1
  have hop : IsOpen (L1.T : Set LL) := by
    have : (L1.T : Set LL) = Set.range (algebraMap O LL) := by
      rw [hL1]
      ext x
      simp [LinearMap.mem_range]
    rw [this]
    exact hopen
  obtain ⟨φ⟩ := hT LL O hO L1 hL1
  exact topLine_at L1 hL1 hop hϖ hc φ (hC LL O hO L1 hL1) hz hz' hd hd' hn

end GlobalTheory.CompanionTheory.LocDual.Top
