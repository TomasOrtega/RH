import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.HermitianTraceFormVanishing

namespace ReciprocityTheory.ChartRestriction.G.FD

namespace DiscriminantTraceBounds

open NumberField Complex Module Matrix
open scoped ComplexConjugate nonZeroDivisors

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Establish `h10 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0`. Rewrite using `[← FractionalIdeal.coeIdeal_top, Ne, FractionalIdeal.coeIdeal_eq_zero]`. Conclude with `top_ne_bot`. Establish `hD0 : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0` using `FractionalIdeal.dual_ne_zero ℤ ℚ h10`. Establish `hmem : x ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E)`.

Rewrite using `[FractionalIdeal.mem_dual h10]`. Introduce `a ha`. Take `⟨β, rfl⟩` from `(FractionalIdeal.mem_one_iff _).mp ha`. Take `⟨m, hm⟩` from `htr β`. Use `⟨m, ?_⟩` and prove the remaining obligations.

Rewrite using `[Algebra.traceForm_apply]`. Simplify using `using hm.symm`. Establish `hsp : FractionalIdeal.spanSingleton (𝓞 E)⁰ x ≤ FractionalIdeal.dual ℤ ℚ 1` using `FractionalIdeal.spanSingleton_le_iff_mem.mpr hmem`. Establish `hdiff` using `coeIdeal_differentIdeal ℤ ℚ E (𝓞 E)`. Establish `hJ : FractionalIdeal.spanSingleton (𝓞 E)⁰ x * (differentIdeal ℤ (𝓞 E) : FractionalIdeal (𝓞 E)⁰ E) ≤ 1`.

Rewrite using `[hdiff]`. Combine the equalities or inequalities in the displayed calculation. Consider the case `exact mul_le_mul' hsp le_rfl`. Consider the case `exact mul_right_mono hsp`. Consider the case `exact FractionalIdeal.mul_right_mono _ hsp`.

Use `_ = 1 := mul_inv_cancel₀ hD0`. Take `⟨I, hI⟩` from `FractionalIdeal.le_one_iff_exists_coeIdeal.mp hJ`. Establish `hJ0 : FractionalIdeal.spanSingleton (𝓞 E)⁰ x * (differentIdeal ℤ (𝓞 E) : FractionalIdeal (𝓞 E)⁰ E) ≠ 0`. Use `mul_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx) ?_` and prove the remaining obligations. Rewrite using `[hdiff]`.

Conclude with `inv_ne_zero hD0`. Establish `hI0 : I ≠ ⊥`. Introduce and unpack `rfl`. Apply `hJ0` to reduce the goal to its premises. Rewrite using `[← hI]`.

Simplify using the standard rewrite rules. Establish `hnorm` using `congrArg FractionalIdeal.absNorm hI`. Rewrite `hnorm` using `[FractionalIdeal.coeIdeal_absNorm, map_mul, FractionalIdeal.absNorm_span_singleton, FractionalIdeal.coeIdeal_absNorm, NumberField.absNorm_differentIdeal E (𝓞 E)]`. Establish `h1 : (1 : ℚ) ≤ (Ideal.absNorm I : ℚ)`. Conclude with `Nat.one_le_iff_ne_zero.mpr (fun h => hI0 (Ideal.absNorm_eq_zero_iff.mp h))` after adjusting the coercions.

Rewrite `h1` using `[hnorm]`. Establish `h2 : (((NumberField.discr E).natAbs : ℕ) : ℚ) = |(NumberField.discr E : ℚ)|`. Rewrite using `[Nat.cast_natAbs]`. Use `push_cast`. Both sides reduce to the same expression.

Rewrite `h1` using `[h2]`. Conclude with `h1`.
-/
theorem norm_mul_discr_ge {x : E} (hx : x ≠ 0)
    (htr : ∀ β : 𝓞 E, ∃ m : ℤ, Algebra.trace ℚ E (x * β) = m) :
    1 ≤ |Algebra.norm ℚ x| * |(NumberField.discr E : ℚ)| := by
  classical
  have h10 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := by
    rw [← FractionalIdeal.coeIdeal_top, Ne, FractionalIdeal.coeIdeal_eq_zero]
    exact top_ne_bot
  have hD0 : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 :=
    FractionalIdeal.dual_ne_zero ℤ ℚ h10
  have hmem : x ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
    rw [FractionalIdeal.mem_dual h10]
    intro a ha
    obtain ⟨β, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp ha
    obtain ⟨m, hm⟩ := htr β
    refine ⟨m, ?_⟩
    rw [Algebra.traceForm_apply]
    simpa using hm.symm
  have hsp : FractionalIdeal.spanSingleton (𝓞 E)⁰ x ≤ FractionalIdeal.dual ℤ ℚ 1 :=
    FractionalIdeal.spanSingleton_le_iff_mem.mpr hmem
  have hdiff := coeIdeal_differentIdeal ℤ ℚ E (𝓞 E)
  have hJ : FractionalIdeal.spanSingleton (𝓞 E)⁰ x *
      (differentIdeal ℤ (𝓞 E) : FractionalIdeal (𝓞 E)⁰ E) ≤ 1 := by
    rw [hdiff]
    calc _ ≤ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) *
          (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E))⁻¹ := by
            first
            | exact mul_le_mul' hsp le_rfl
            | exact mul_right_mono hsp
            | exact FractionalIdeal.mul_right_mono _ hsp
      _ = 1 := mul_inv_cancel₀ hD0
  obtain ⟨I, hI⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hJ
  have hJ0 : FractionalIdeal.spanSingleton (𝓞 E)⁰ x *
      (differentIdeal ℤ (𝓞 E) : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := by
    refine mul_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx) ?_
    rw [hdiff]
    exact inv_ne_zero hD0
  have hI0 : I ≠ ⊥ := by
    rintro rfl
    apply hJ0
    rw [← hI]
    simp
  have hnorm := congrArg FractionalIdeal.absNorm hI
  rw [FractionalIdeal.coeIdeal_absNorm, map_mul, FractionalIdeal.absNorm_span_singleton,
    FractionalIdeal.coeIdeal_absNorm, NumberField.absNorm_differentIdeal E (𝓞 E)] at hnorm
  have h1 : (1 : ℚ) ≤ (Ideal.absNorm I : ℚ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun h => hI0 (Ideal.absNorm_eq_zero_iff.mp h))
  rw [hnorm] at h1
  have h2 : (((NumberField.discr E).natAbs : ℕ) : ℚ) = |(NumberField.discr E : ℚ)| := by
    rw [Nat.cast_natAbs]
    push_cast
    rfl
  rw [h2] at h1
  exact h1

/- English proof (translation)
The claim follows from `|((Algebra.norm ℚ x : ℚ) : ℝ)| = a ^ finrank ℚ E := by have h1 := Algebra.norm_eq_prod_embeddings ℚ ℂ x have h2 : ‖algebraMap ℚ ℂ (Algebra.norm ℚ x)‖ = a ^ finrank ℚ E := by rw [h1, norm_prod, Finset.prod_congr rfl (fun σ _ => h σ.toRingHom), Finset.prod_const, Finset.card_univ, …`.
-/
theorem abs_norm_eq_pow {x : E} {a : ℝ} (h : ∀ σ : E →+* ℂ, ‖σ x‖ = a) :
    |((Algebra.norm ℚ x : ℚ) : ℝ)| = a ^ finrank ℚ E := by
  have h1 := Algebra.norm_eq_prod_embeddings ℚ ℂ x
  have h2 : ‖algebraMap ℚ ℂ (Algebra.norm ℚ x)‖ = a ^ finrank ℚ E := by
    rw [h1, norm_prod, Finset.prod_congr rfl (fun σ _ => h σ.toRingHom), Finset.prod_const,
      Finset.card_univ, AlgHom.card]
  rw [← h2, eq_ratCast, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]

section data

variable [IsCMField E] {r : ℕ} (X : DataX E r)

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Establish `hcc_add : ∀ a b : E, cc (a + b) = cc a + cc b` using `fun a b => by`. Unfold `cc`. Conclude with `map_add _ a b`.

Establish `hcc_mul : ∀ a b : E, cc (a * b) = cc a * cc b` using `fun a b => by`. Unfold `cc`. Conclude with `map_mul _ a b`. Establish `hcc0 : cc (0 : E) = 0`. Unfold `cc`.

Conclude with `map_zero _`. Establish `hcc1 : cc (1 : E) = 1`. Unfold `cc`. Conclude with `map_one _`. Establish `hadd2 : ∀ x y y' : Fin r → E, herm X.Gm x (y + y') = herm X.Gm x y + herm X.Gm x y'`.

Introduce `x y y'`. Simplify using `only [herm, Pi.add_apply, hcc_add, mul_add, Finset.sum_add_distrib]`. Establish `hsmul2 : ∀ (x y : Fin r → E) (c : E), herm X.Gm x (c • y) = cc c * herm X.Gm x y`. Introduce `x y c`. Simplify using `only [herm, Pi.smul_apply, smul_eq_mul, hcc_mul, Finset.mul_sum]`.

Conclude with `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring`. Establish `hzero2 : ∀ x : Fin r → E, herm X.Gm x 0 = 0` using `fun x => by simp [herm, hcc0]`. Establish `hadd1 : ∀ x x' y : Fin r → E, herm X.Gm (x + x') y = herm X.Gm x y + herm X.Gm x' y`. Introduce `x x' y`. Simplify using `only [herm, Pi.add_apply, add_mul, Finset.sum_add_distrib]`.

Establish `hsmul1 : ∀ (x y : Fin r → E) (c : E), herm X.Gm (c • x) y = c * herm X.Gm x y`. Introduce `x y c`. Simplify using `only [herm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring`. Establish `hzero1 : ∀ y : Fin r → E, herm X.Gm 0 y = 0` using `fun y => by simp [herm]`.

Establish `hspan : Submodule.span E (X.L' : Set (Fin r → E)) = ⊤`. Rewrite using `[eq_top_iff, ← X.Λ_span]`. Apply `Submodule.span_le.mpr` to reduce the goal to its premises. Introduce `z hz`. Establish `h1` using `X.NA_sub z hz`.

Establish `hNA : (X.NA : E) ≠ 0` using `Nat.cast_ne_zero.mpr X.NA_pos.ne'`. Establish `hz' : z = (X.NA : E)⁻¹ • ((X.NA : E) • z)`. Rewrite using `[smul_smul, inv_mul_cancel₀ hNA, one_smul]`. Rewrite using `[hz']`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span h1)`.

Establish `hall2 : ∀ x ∈ X.L', ∀ y, herm X.Gm x y = 0`. Introduce `x hx y`. Establish `hy : y ∈ Submodule.span E (X.L' : Set (Fin r → E))`. Rewrite using `[hspan]`. Conclude with `Submodule.mem_top`.

Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy => exact hcon x hx y hy`. Consider the case `zero => exact hzero2 x`. Consider the case `add y y' _ _ h1 h2 => rw [hadd2, h1, h2, add_zero]`. Consider the case `smul c y _ h => rw [hsmul2, h, mul_zero]`.

Establish `hall : ∀ x y : Fin r → E, herm X.Gm x y = 0`. Introduce `x y`. Establish `hx : x ∈ Submodule.span E (X.L' : Set (Fin r → E))`. Rewrite using `[hspan]`. Conclude with `Submodule.mem_top`.

Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx => exact hall2 x hx y`. Consider the case `zero => exact hzero1 y`. Consider the case `add x x' _ _ h1 h2 => rw [hadd1, h1, h2, add_zero]`. Consider the case `smul c x _ h => rw [hsmul1, h, mul_zero]`.

Establish `hG : X.Gm = 0`. Use extensionality with `a b`. Establish `hval : herm X.Gm (Pi.single a 1) (Pi.single b 1) = X.Gm a b`. Simplify using `[herm, Pi.single_apply, apply_ite cc, hcc1, hcc0]`. Rewrite using `[Matrix.zero_apply, ← hval]`.

Conclude with `hall _ _`. Use `haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩`. Conclude with `X.Gm_det (by rw [hG]; exact Matrix.det_zero)`.
-/
theorem exists_herm_ne (hr : 0 < r) : ∃ x ∈ X.L', ∃ y ∈ X.L', herm X.Gm x y ≠ 0 := by
  classical
  by_contra hcon
  push_neg at hcon
  have hcc_add : ∀ a b : E, cc (a + b) = cc a + cc b := fun a b => by
    unfold cc
    exact map_add _ a b
  have hcc_mul : ∀ a b : E, cc (a * b) = cc a * cc b := fun a b => by
    unfold cc
    exact map_mul _ a b
  have hcc0 : cc (0 : E) = 0 := by
    unfold cc
    exact map_zero _
  have hcc1 : cc (1 : E) = 1 := by
    unfold cc
    exact map_one _
  have hadd2 : ∀ x y y' : Fin r → E, herm X.Gm x (y + y') = herm X.Gm x y + herm X.Gm x y' := by
    intro x y y'
    simp only [herm, Pi.add_apply, hcc_add, mul_add, Finset.sum_add_distrib]
  have hsmul2 : ∀ (x y : Fin r → E) (c : E), herm X.Gm x (c • y) = cc c * herm X.Gm x y := by
    intro x y c
    simp only [herm, Pi.smul_apply, smul_eq_mul, hcc_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have hzero2 : ∀ x : Fin r → E, herm X.Gm x 0 = 0 := fun x => by simp [herm, hcc0]
  have hadd1 : ∀ x x' y : Fin r → E, herm X.Gm (x + x') y = herm X.Gm x y + herm X.Gm x' y := by
    intro x x' y
    simp only [herm, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  have hsmul1 : ∀ (x y : Fin r → E) (c : E), herm X.Gm (c • x) y = c * herm X.Gm x y := by
    intro x y c
    simp only [herm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have hzero1 : ∀ y : Fin r → E, herm X.Gm 0 y = 0 := fun y => by simp [herm]
  have hspan : Submodule.span E (X.L' : Set (Fin r → E)) = ⊤ := by
    rw [eq_top_iff, ← X.Λ_span]
    apply Submodule.span_le.mpr
    intro z hz
    have h1 := X.NA_sub z hz
    have hNA : (X.NA : E) ≠ 0 := Nat.cast_ne_zero.mpr X.NA_pos.ne'
    have hz' : z = (X.NA : E)⁻¹ • ((X.NA : E) • z) := by
      rw [smul_smul, inv_mul_cancel₀ hNA, one_smul]
    rw [hz']
    exact Submodule.smul_mem _ _ (Submodule.subset_span h1)
  have hall2 : ∀ x ∈ X.L', ∀ y, herm X.Gm x y = 0 := by
    intro x hx y
    have hy : y ∈ Submodule.span E (X.L' : Set (Fin r → E)) := by
      rw [hspan]
      exact Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem y hy => exact hcon x hx y hy
    | zero => exact hzero2 x
    | add y y' _ _ h1 h2 => rw [hadd2, h1, h2, add_zero]
    | smul c y _ h => rw [hsmul2, h, mul_zero]
  have hall : ∀ x y : Fin r → E, herm X.Gm x y = 0 := by
    intro x y
    have hx : x ∈ Submodule.span E (X.L' : Set (Fin r → E)) := by
      rw [hspan]
      exact Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem x hx => exact hall2 x hx y
    | zero => exact hzero1 y
    | add x x' _ _ h1 h2 => rw [hadd1, h1, h2, add_zero]
    | smul c x _ h => rw [hsmul1, h, mul_zero]
  have hG : X.Gm = 0 := by
    ext a b
    have hval : herm X.Gm (Pi.single a 1) (Pi.single b 1) = X.Gm a b := by
      simp [herm, Pi.single_apply, apply_ite cc, hcc1, hcc0]
    rw [Matrix.zero_apply, ← hval]
    exact hall _ _
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  exact X.Gm_det (by rw [hG]; exact Matrix.det_zero)

/- English proof (translation)
Simplify using `only [herm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring`.
-/
private theorem herm_smul_left_eq_mul (G : Matrix (Fin r) (Fin r) E) (c : E) (x y : Fin r → E) :
    herm G (c • x) y = c * herm G x y := by
  simp only [herm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

/- English proof (translation)
Establish `hcc_mul : ∀ a b : E, cc (a * b) = cc a * cc b` using `fun a b => by`. Unfold `cc`. Conclude with `map_mul _ a b`. Simplify using `only [herm, Pi.smul_apply, smul_eq_mul, hcc_mul, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring`.
-/
private theorem herm_smul_right_fundamental_domains (G : Matrix (Fin r) (Fin r) E) (c : E) (x y : Fin r → E) :
    herm G x (c • y) = cc c * herm G x y := by
  have hcc_mul : ∀ a b : E, cc (a * b) = cc a * cc b := fun a b => by
    unfold cc
    exact map_mul _ a b
  simp only [herm, Pi.smul_apply, smul_eq_mul, hcc_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

/- English proof (translation)
Use `set gens : Set (𝓞 E) := {c | ∃ x ∈ X.L', ∃ y ∈ X.L', (c : E) = herm X.Gm x y} with hgens`. Use `set J : Ideal (𝓞 E) := Ideal.span gens with hJdef`. Establish `hgen_mem : ∀ x ∈ X.L', ∀ y ∈ X.L', ∃ c ∈ J, (c : E) = herm X.Gm x y`. Introduce `x hx y hy`. Conclude with `⟨⟨herm X.Gm x y, X.L'_int x hx y hy⟩, Ideal.subset_span ⟨x, hx, y, hy, rfl⟩, rfl⟩`.

Establish `hJ0 : J ≠ ⊥`. Take `⟨x, hx, y, hy, hne⟩` from `exists_herm_ne X hr`. Take `⟨c, hc, hce⟩` from `hgen_mem x hx y hy`. Introduce `hbot`. Rewrite `hc` using `[hbot, Ideal.mem_bot]`.

Apply `hne` to reduce the goal to its premises. Rewrite using `[← hce, hc]`. Simplify using the standard rewrite rules. Establish `hJf0 : (J : FractionalIdeal (𝓞 E)⁰ E) ≠ 0`. Rewrite using `[Ne, FractionalIdeal.coeIdeal_eq_zero]`.

Conclude with `hJ0`. Establish `hmemJf : ∀ c ∈ J, ((c : 𝓞 E) : E) ∈ (J : FractionalIdeal (𝓞 E)⁰ E)` using `fun c hc => (FractionalIdeal.mem_coeIdeal _).mpr ⟨c, hc, rfl⟩`. Establish `hinv : ∀ t ∈ (J : FractionalIdeal (𝓞 E)⁰ E)⁻¹, ∀ x ∈ X.L', t • x ∈ X.L'`. Introduce `t ht x hx`. Apply `X.L'_dual` to reduce the goal to its premises.

Introduce `y hy`. Rewrite using `[herm_smul_left_eq_mul]`. Take `⟨c, hc, hce⟩` from `hgen_mem x hx y hy`. Establish `h1` using `(FractionalIdeal.mem_inv_iff hJf0).mp ht _ (hmemJf c hc)`. Take `⟨d, hd⟩` from `(FractionalIdeal.mem_one_iff _).mp h1`.

Rewrite using `[← hce, ← hd]`. Conclude with `RingOfIntegers.isIntegral_coe d`. Establish `hmul : ∀ t ∈ (J : FractionalIdeal (𝓞 E)⁰ E)⁻¹, ∀ c ∈ J, t * (c : E) ∈ (J : FractionalIdeal (𝓞 E)⁰ E)`. Introduce `t ht c hc`. Proceed by induction on `hc using Submodule.span_induction with`.

Consider the case `mem c hc`. Take `⟨x, hx, y, hy, hce⟩` from `hc`. Rewrite using `[hce, ← herm_smul_left_eq_mul]`. Take `⟨c', hc', hce'⟩` from `hgen_mem _ (hinv t ht x hx) y hy`. Rewrite using `[← hce']`.

Conclude with `hmemJf c' hc'`. Consider the case `zero`. Simplify using the standard rewrite rules. Consider the case `add a b _ _ ha hb`. Use `push_cast`.

Rewrite using `[mul_add]`. Conclude with `Submodule.add_mem _ ha hb`. Consider the case `smul a c _ h`. Rewrite using `[smul_eq_mul]`. Use `push_cast`.

Rewrite using `[mul_left_comm, ← Algebra.smul_def]`. Conclude with `Submodule.smul_mem _ a h`. Establish `hle : (J : FractionalIdeal (𝓞 E)⁰ E)⁻¹ * (J : FractionalIdeal (𝓞 E)⁰ E) ≤ (J : FractionalIdeal (𝓞 E)⁰ E)` using `FractionalIdeal.mul_le.mpr fun t ht j hj => by`. Take `⟨c, hc, rfl⟩` from `(FractionalIdeal.mem_coeIdeal _).mp hj`. Conclude with `hmul t ht c hc`.

Rewrite `hle` using `[inv_mul_cancel₀ hJf0]`. Establish `hJtop : J = ⊤`. Rewrite using `[eq_top_iff]`. Rewrite `hle` using `[← FractionalIdeal.coeIdeal_top]`. Conclude with `(FractionalIdeal.coeIdeal_le_coeIdeal E).mp hle`.

Establish `hccNC : cc (X.NC : E) = X.NC`. Unfold `cc`. Conclude with `map_natCast _ _`. Establish `hP : ∀ c ∈ J, ∀ a : 𝓞 E, ∃ m : ℤ, Algebra.trace ℚ E ((X.NC : E) ^ 2 * X.ξ0 * ((a : E) * (c : E))) = m`. Introduce `c hc`.

Proceed by induction on `hc using Submodule.span_induction with`. Consider the case `mem c hc`. Introduce `a`. Take `⟨x, hx, y, hy, hce⟩` from `hc`. Establish `hax : (a : E) • x ∈ X.L'`.

Rewrite using `[show (a : E) • x = a • x from algebraMap_smul E a x]`. Conclude with `X.L'.smul_mem a hx`. Take `⟨k, hk⟩` from `X.EF_int _ (X.NC_sub _ hax) _ (X.NC_sub _ hy)`. Use `⟨-k, ?_⟩` and prove the remaining obligations. Unfold `EFf at hk`.

Rewrite `hk` using `[herm_smul_left_eq_mul, herm_smul_right_fundamental_domains, herm_smul_left_eq_mul, hccNC]`. Establish `h2 : (X.NC : E) ^ 2 * X.ξ0 * ((a : E) * (c : E)) = -(-X.ξ0 * ((X.NC : E) * ((X.NC : E) * ((a : E) * herm X.Gm x y))))`. Rewrite using `[hce]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h2, map_neg, hk]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Consider the case `zero`. Introduce `a`. Conclude with `⟨0, by simp⟩`.

Consider the case `add c c' _ _ h1 h2`. Introduce `a`. Take `⟨m1, hm1⟩` from `h1 a`. Take `⟨m2, hm2⟩` from `h2 a`. Use `⟨m1 + m2, ?_⟩` and prove the remaining obligations.

Use `push_cast`. Rewrite using `[mul_add, mul_add, map_add, hm1, hm2]`. Consider the case `smul b c _ h`. Introduce `a`. Take `⟨m, hm⟩` from `h (a * b)`.

Use `⟨m, ?_⟩` and prove the remaining obligations. Rewrite using `[← hm, smul_eq_mul]`. Use `push_cast`. Put the polynomial expressions in normal form. Take `⟨m, hm⟩` from `hP c (by rw [hJtop]; exact Submodule.mem_top) 1`.

Use `⟨m, ?_⟩` and prove the remaining obligations. Rewrite using `[← hm]`. Simplify using the standard rewrite rules.
-/
theorem trace_int (hr : 0 < r) (c : 𝓞 E) :
    ∃ m : ℤ, Algebra.trace ℚ E ((X.NC : E) ^ 2 * X.ξ0 * c) = m := by
  classical
  set gens : Set (𝓞 E) := {c | ∃ x ∈ X.L', ∃ y ∈ X.L', (c : E) = herm X.Gm x y} with hgens
  set J : Ideal (𝓞 E) := Ideal.span gens with hJdef
  have hgen_mem : ∀ x ∈ X.L', ∀ y ∈ X.L', ∃ c ∈ J, (c : E) = herm X.Gm x y := by
    intro x hx y hy
    exact ⟨⟨herm X.Gm x y, X.L'_int x hx y hy⟩, Ideal.subset_span ⟨x, hx, y, hy, rfl⟩, rfl⟩
  have hJ0 : J ≠ ⊥ := by
    obtain ⟨x, hx, y, hy, hne⟩ := exists_herm_ne X hr
    obtain ⟨c, hc, hce⟩ := hgen_mem x hx y hy
    intro hbot
    rw [hbot, Ideal.mem_bot] at hc
    apply hne
    rw [← hce, hc]
    simp
  have hJf0 : (J : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
    exact hJ0
  have hmemJf : ∀ c ∈ J, ((c : 𝓞 E) : E) ∈ (J : FractionalIdeal (𝓞 E)⁰ E) :=
    fun c hc => (FractionalIdeal.mem_coeIdeal _).mpr ⟨c, hc, rfl⟩
  have hinv : ∀ t ∈ (J : FractionalIdeal (𝓞 E)⁰ E)⁻¹, ∀ x ∈ X.L', t • x ∈ X.L' := by
    intro t ht x hx
    apply X.L'_dual
    intro y hy
    rw [herm_smul_left_eq_mul]
    obtain ⟨c, hc, hce⟩ := hgen_mem x hx y hy
    have h1 := (FractionalIdeal.mem_inv_iff hJf0).mp ht _ (hmemJf c hc)
    obtain ⟨d, hd⟩ := (FractionalIdeal.mem_one_iff _).mp h1
    rw [← hce, ← hd]
    exact RingOfIntegers.isIntegral_coe d
  have hmul : ∀ t ∈ (J : FractionalIdeal (𝓞 E)⁰ E)⁻¹, ∀ c ∈ J,
      t * (c : E) ∈ (J : FractionalIdeal (𝓞 E)⁰ E) := by
    intro t ht c hc
    induction hc using Submodule.span_induction with
    | mem c hc =>
      obtain ⟨x, hx, y, hy, hce⟩ := hc
      rw [hce, ← herm_smul_left_eq_mul]
      obtain ⟨c', hc', hce'⟩ := hgen_mem _ (hinv t ht x hx) y hy
      rw [← hce']
      exact hmemJf c' hc'
    | zero =>
      simp
    | add a b _ _ ha hb =>
      push_cast
      rw [mul_add]
      exact Submodule.add_mem _ ha hb
    | smul a c _ h =>
      rw [smul_eq_mul]
      push_cast
      rw [mul_left_comm, ← Algebra.smul_def]
      exact Submodule.smul_mem _ a h
  have hle : (J : FractionalIdeal (𝓞 E)⁰ E)⁻¹ * (J : FractionalIdeal (𝓞 E)⁰ E) ≤
      (J : FractionalIdeal (𝓞 E)⁰ E) := FractionalIdeal.mul_le.mpr fun t ht j hj => by
    obtain ⟨c, hc, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hj
    exact hmul t ht c hc
  rw [inv_mul_cancel₀ hJf0] at hle
  have hJtop : J = ⊤ := by
    rw [eq_top_iff]
    rw [← FractionalIdeal.coeIdeal_top] at hle
    exact (FractionalIdeal.coeIdeal_le_coeIdeal E).mp hle
  have hccNC : cc (X.NC : E) = X.NC := by
    unfold cc
    exact map_natCast _ _
  have hP : ∀ c ∈ J, ∀ a : 𝓞 E, ∃ m : ℤ,
      Algebra.trace ℚ E ((X.NC : E) ^ 2 * X.ξ0 * ((a : E) * (c : E))) = m := by
    intro c hc
    induction hc using Submodule.span_induction with
    | mem c hc =>
      intro a
      obtain ⟨x, hx, y, hy, hce⟩ := hc
      have hax : (a : E) • x ∈ X.L' := by
        rw [show (a : E) • x = a • x from algebraMap_smul E a x]
        exact X.L'.smul_mem a hx
      obtain ⟨k, hk⟩ := X.EF_int _ (X.NC_sub _ hax) _ (X.NC_sub _ hy)
      refine ⟨-k, ?_⟩
      unfold EFf at hk
      rw [herm_smul_left_eq_mul, herm_smul_right_fundamental_domains, herm_smul_left_eq_mul, hccNC] at hk
      have h2 : (X.NC : E) ^ 2 * X.ξ0 * ((a : E) * (c : E)) =
          -(-X.ξ0 * ((X.NC : E) * ((X.NC : E) * ((a : E) * herm X.Gm x y)))) := by
        rw [hce]
        ring
      rw [h2, map_neg, hk]
      push_cast
      ring
    | zero =>
      intro a
      exact ⟨0, by simp⟩
    | add c c' _ _ h1 h2 =>
      intro a
      obtain ⟨m1, hm1⟩ := h1 a
      obtain ⟨m2, hm2⟩ := h2 a
      refine ⟨m1 + m2, ?_⟩
      push_cast
      rw [mul_add, mul_add, map_add, hm1, hm2]
    | smul b c _ h =>
      intro a
      obtain ⟨m, hm⟩ := h (a * b)
      refine ⟨m, ?_⟩
      rw [← hm, smul_eq_mul]
      push_cast
      ring_nf
  obtain ⟨m, hm⟩ := hP c (by rw [hJtop]; exact Submodule.mem_top) 1
  refine ⟨m, ?_⟩
  rw [← hm]
  simp

/- English proof (translation)
Use `set n := finrank ℚ E with hn_def`. Establish `hn : 0 < n` using `Module.finrank_pos`. Establish `hNC : (0 : ℝ) < X.NC` using `Nat.cast_pos.mpr X.NC_pos`. Establish `hx0 : ((X.NC : E) ^ 2 * X.ξ0) ≠ 0` using `mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.mpr X.NC_pos.ne')) X.ξ0_ne`. Establish `h1` using `norm_mul_discr_ge hx0 (fun β => by`.

Take `⟨m, hm⟩` from `trace_int X hr β`. Conclude with `⟨m, hm⟩)`. Establish `habs : ∀ σ : E →+* ℂ, ‖σ ((X.NC : E) ^ 2 * X.ξ0)‖ = (X.NC : ℝ) ^ 2 * (X.k0 / 2)`. Introduce `σ`. Rewrite using `[map_mul, map_pow, map_natCast, norm_mul, norm_pow, Complex.norm_natCast]`.

Use `congr 1`. Distinguish the cases in `hσ : σ ∈ X.Ψ`. Conclude with `X.ξ0_abs ⟨σ, hσ⟩`. Establish `hc : ComplexEmbedding.conjugate σ ∈ X.Ψ`. Assume the negation of the conclusion as `h'`.

Conclude with `hσ ((X.cmType σ).mpr h')`. Establish `h5` using `X.ξ0_abs ⟨_, hc⟩`. Simplify using `only [ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj] at h5`. Conclude with `h5`. Establish `h2` using `abs_norm_eq_pow habs`.

Establish `h3 : (1 : ℝ) ≤ |((Algebra.norm ℚ ((X.NC : E) ^ 2 * X.ξ0) : ℚ) : ℝ)| * dE E`. Unfold `dE`. Establish `h1' : ((1 : ℚ) : ℝ) ≤ ((|Algebra.norm ℚ ((X.NC : E) ^ 2 * X.ξ0)| * |(NumberField.discr E : ℚ)| : ℚ) : ℝ)`. Conclude with `h1` after adjusting the coercions. Move the coercions through the operations in `at h1'`.

Conclude with `h1'`. Rewrite `h3` using `[h2]`. Establish `ha : 0 < (X.NC : ℝ) ^ 2 * (X.k0 / 2)`. Use `X.minWeight_pos` as an intermediate fact. Check the signs of the components of the expression.

Establish `hd : 0 ≤ dE E` using `abs_nonneg _`. Establish `h4 : 1 ≤ (((X.NC : ℝ) ^ 2 * (X.k0 / 2)) ^ n * dE E) ^ (1 / (n : ℝ))` using `Real.one_le_rpow h3 (by positivity)`. Rewrite `h4` using `[Real.mul_rpow (by positivity) hd, ← Real.rpow_natCast, ← Real.rpow_mul ha.le, mul_one_div_cancel (by positivity), Real.rpow_one]`. Unfold `rdE`. Rewrite using `[← hn_def]`.

Use polynomial arithmetic with `[h4]`.
-/
theorem two_le_normSq_mul_rootDisc (hr : 0 < r) : 2 ≤ (X.NC : ℝ) ^ 2 * X.k0 * rdE E := by
  set n := finrank ℚ E with hn_def
  have hn : 0 < n := Module.finrank_pos
  have hNC : (0 : ℝ) < X.NC := Nat.cast_pos.mpr X.NC_pos
  have hx0 : ((X.NC : E) ^ 2 * X.ξ0) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.mpr X.NC_pos.ne')) X.ξ0_ne
  have h1 := norm_mul_discr_ge hx0 (fun β => by
    obtain ⟨m, hm⟩ := trace_int X hr β
    exact ⟨m, hm⟩)
  have habs : ∀ σ : E →+* ℂ, ‖σ ((X.NC : E) ^ 2 * X.ξ0)‖ = (X.NC : ℝ) ^ 2 * (X.k0 / 2) := by
    intro σ
    rw [map_mul, map_pow, map_natCast, norm_mul, norm_pow, Complex.norm_natCast]
    congr 1
    by_cases hσ : σ ∈ X.Ψ
    · exact X.ξ0_abs ⟨σ, hσ⟩
    · have hc : ComplexEmbedding.conjugate σ ∈ X.Ψ := by
        by_contra h'
        exact hσ ((X.cmType σ).mpr h')
      have h5 := X.ξ0_abs ⟨_, hc⟩
      simp only [ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj] at h5
      exact h5
  have h2 := abs_norm_eq_pow habs
  have h3 : (1 : ℝ) ≤ |((Algebra.norm ℚ ((X.NC : E) ^ 2 * X.ξ0) : ℚ) : ℝ)| * dE E := by
    unfold dE
    have h1' : ((1 : ℚ) : ℝ) ≤
        ((|Algebra.norm ℚ ((X.NC : E) ^ 2 * X.ξ0)| * |(NumberField.discr E : ℚ)| : ℚ) : ℝ) := by
      exact_mod_cast h1
    push_cast at h1'
    exact h1'
  rw [h2] at h3
  have ha : 0 < (X.NC : ℝ) ^ 2 * (X.k0 / 2) := by
    have := X.minWeight_pos
    positivity
  have hd : 0 ≤ dE E := abs_nonneg _
  have h4 : 1 ≤ (((X.NC : ℝ) ^ 2 * (X.k0 / 2)) ^ n * dE E) ^ (1 / (n : ℝ)) :=
    Real.one_le_rpow h3 (by positivity)
  rw [Real.mul_rpow (by positivity) hd, ← Real.rpow_natCast, ← Real.rpow_mul ha.le,
    mul_one_div_cancel (by positivity), Real.rpow_one] at h4
  unfold rdE
  rw [← hn_def]
  nlinarith [h4]

end data

end DiscriminantTraceBounds

end ReciprocityTheory.ChartRestriction.G.FD
