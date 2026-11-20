import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RationalPointsIntegralPointsMembership
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPointStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardFiniteSubgroupGLIntDvd

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators nonZeroDivisors

namespace GlobalTheory.StabOrder

section General

variable {E : Type} [Field E] [NumberField E] {N : ℕ}

/- English proof (translation)
The claim follows from `IsIntegralClosure.isLocalization ℤ ℚ E (𝓞 E)`.
-/
theorem loc_int : IsLocalization (Algebra.algebraMapSubmonoid (𝓞 E) ℤ⁰) E :=
  IsIntegralClosure.isLocalization ℤ ℚ E (𝓞 E)

/- English proof (translation)
Use `haveI := loc_int (E := E)`. Take `⟨t, ht⟩` from `multiple_mem_span_of_mem_localization_span (Algebra.algebraMapSubmonoid (𝓞 E) ℤ⁰) E (L : Set (Fin N → E)) x (hs ▸ Submodule.mem_top)`. Take `⟨t, n, hn, rfl⟩` from `t`. Use `⟨n, nonZeroDivisors.ne_zero hn, ?_⟩` and prove the remaining obligations. Rewrite `ht` using `[Submodule.span_eq]`.

Simplify `ht` using `[Submonoid.smul_def, Int.cast_smul_eq_zsmul]`.
-/
theorem exists_int_smul_mem (L : Submodule (𝓞 E) (Fin N → E))
    (hs : Submodule.span E (L : Set (Fin N → E)) = ⊤) (x : Fin N → E) :
    ∃ n : ℤ, n ≠ 0 ∧ n • x ∈ L := by
  haveI := loc_int (E := E)
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span
    (Algebra.algebraMapSubmonoid (𝓞 E) ℤ⁰) E (L : Set (Fin N → E)) x (hs ▸ Submodule.mem_top)
  obtain ⟨t, n, hn, rfl⟩ := t
  refine ⟨n, nonZeroDivisors.ne_zero hn, ?_⟩
  rw [Submodule.span_eq] at ht
  simpa [Submonoid.smul_def, Int.cast_smul_eq_zsmul] using ht

/- English proof (translation)
Use `haveI := loc_int (E := E)`. Take `⟨s, rfl⟩` from `hf`. Take `⟨⟨t, n, hn, rfl⟩, ht⟩` from `IsLocalization.exist_integer_multiples_of_finite (Algebra.algebraMapSubmonoid (𝓞 E) ℤ⁰) (fun p : s × Fin N => (p.1 : Fin N → E) p.2)`. Use `⟨n, nonZeroDivisors.ne_zero hn, ?_⟩` and prove the remaining obligations. Introduce `x hx i`.

Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨y, hy⟩` from `ht (⟨x, hx⟩, i)`. Establish `: (n : E) * x i = algebraMap (𝓞 E) E y`. Rewrite using `[hy]`.

Simplify using `[Algebra.smul_def]`. Rewrite using `[this]`. Conclude with `y.isIntegral_coe`. Consider the case `zero => simpa using isIntegral_zero`. Consider the case `add x y _ _ hx hy => simpa [mul_add] using hx.add hy`.

Consider the case `smul a x _ hx`. Establish `: (n : E) * (a • x) i = (a : E) * ((n : E) * x i)`. Simplify using `[Algebra.smul_def]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`.

Conclude with `a.isIntegral_coe.mul hx`.
-/
theorem exists_int_denominator (L : Submodule (𝓞 E) (Fin N → E)) (hf : L.FG) :
    ∃ n : ℤ, n ≠ 0 ∧ ∀ x ∈ L, ∀ i, IsIntegral ℤ ((n : E) * x i) := by
  haveI := loc_int (E := E)
  obtain ⟨s, rfl⟩ := hf
  obtain ⟨⟨t, n, hn, rfl⟩, ht⟩ := IsLocalization.exist_integer_multiples_of_finite
    (Algebra.algebraMapSubmonoid (𝓞 E) ℤ⁰) (fun p : s × Fin N => (p.1 : Fin N → E) p.2)
  refine ⟨n, nonZeroDivisors.ne_zero hn, ?_⟩
  intro x hx i
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy⟩ := ht (⟨x, hx⟩, i)
    have : (n : E) * x i = algebraMap (𝓞 E) E y := by
      rw [hy]; simp [Algebra.smul_def]
    rw [this]; exact y.isIntegral_coe
  | zero => simpa using isIntegral_zero
  | add x y _ _ hx hy => simpa [mul_add] using hx.add hy
  | smul a x _ hx =>
    have : (n : E) * (a • x) i = (a : E) * ((n : E) * x i) := by
      simp [Algebra.smul_def]; ring
    rw [this]; exact a.isIntegral_coe.mul hx

/- English proof (translation)
Establish `h1` using `congrArg φ (congrFun (congrFun h i) i)`. Simplify using `only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, hc, Matrix.one_apply_eq, map_one, Complex.mul_conj'] at h1`. Establish `h2 : ∑ k, ‖φ (γ i k)‖ ^ 2 = 1` using `by exact_mod_cast h1`. Establish `h3 : ‖φ (γ i j)‖ ^ 2 ≤ 1`. Rewrite using `[← h2]`.

Conclude with `Finset.single_le_sum (f := fun k => ‖φ (γ i k)‖ ^ 2) (fun k _ => by positivity) (Finset.mem_univ j)`. Use polynomial arithmetic with `[norm_nonneg (φ (γ i j))]`.
-/
theorem norm_entry_le (c : E → E) (hc : ∀ (φ : E →+* ℂ) x, φ (c x) = starRingEnd ℂ (φ x))
    (γ : Matrix (Fin N) (Fin N) E) (h : γ * (γ.map c).transpose = 1) (φ : E →+* ℂ) (i j : Fin N) :
    ‖φ (γ i j)‖ ≤ 1 := by
  have h1 := congrArg φ (congrFun (congrFun h i) i)
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, hc,
    Matrix.one_apply_eq, map_one, Complex.mul_conj'] at h1
  have h2 : ∑ k, ‖φ (γ i k)‖ ^ 2 = 1 := by exact_mod_cast h1
  have h3 : ‖φ (γ i j)‖ ^ 2 ≤ 1 := by
    rw [← h2]
    exact Finset.single_le_sum (f := fun k => ‖φ (γ i k)‖ ^ 2) (fun k _ => by positivity) (Finset.mem_univ j)
  nlinarith [norm_nonneg (φ (γ i j))]

/- English proof (translation)
Take `⟨b, hb, hbL⟩` from `exists_int_denominator L hf`. Use `choose a ha haL using fun j : Fin N => exists_int_smul_mem L hs (Pi.single j 1)`. Establish `hS : ∀ j, {x : E | IsIntegral ℤ (((b * a j : ℤ) : E) * x) ∧ ∀ φ : E →+* ℂ, ‖φ x‖ ≤ 1}.Finite`. Introduce `j`. Establish `hne : ((b * a j : ℤ) : E) ≠ 0` using `by exact_mod_cast mul_ne_zero hb (ha j)`.

Use `Set.Finite.of_finite_image (f := fun x => ((b * a j : ℤ) : E) * x) ?_ (mul_right_injective₀ hne).injOn` and prove the remaining obligations. Use `(Embeddings.finite_of_norm_le E ℂ ‖((b * a j : ℤ) : ℂ)‖).subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, ⟨h1, h2⟩, rfl⟩`. Use `⟨h1, fun φ => ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_intCast, norm_mul]`.

Conclude with `mul_le_of_le_one_right (norm_nonneg _) (h2 φ)`. Use `(Set.Finite.pi' (fun _ : Fin N => Set.Finite.pi' hS)).subset ?_` and prove the remaining obligations. Introduce and unpack `(γ : Matrix (Fin N) (Fin N) E) ⟨h1, h2⟩ i j`. Use `⟨?_, fun φ => norm_entry_le c hc γ h1 φ i j⟩` and prove the remaining obligations. Use `hbL _ (h2 _ (haL j)) i` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Establish `h3` using `Matrix.mulVec_smul γ (a j) (Pi.single j (1 : E))`. Rewrite using `[h3]`. Simplify using `[mul_assoc]`.
-/
theorem finite_stab (c : E → E) (hc : ∀ (φ : E →+* ℂ) x, φ (c x) = starRingEnd ℂ (φ x))
    (L : Submodule (𝓞 E) (Fin N → E)) (hf : L.FG)
    (hs : Submodule.span E (L : Set (Fin N → E)) = ⊤) :
    {γ : Matrix (Fin N) (Fin N) E | γ * (γ.map c).transpose = 1 ∧ ∀ x ∈ L, γ.mulVec x ∈ L}.Finite := by
  obtain ⟨b, hb, hbL⟩ := exists_int_denominator L hf
  choose a ha haL using fun j : Fin N => exists_int_smul_mem L hs (Pi.single j 1)
  have hS : ∀ j, {x : E | IsIntegral ℤ (((b * a j : ℤ) : E) * x) ∧ ∀ φ : E →+* ℂ, ‖φ x‖ ≤ 1}.Finite := by
    intro j
    have hne : ((b * a j : ℤ) : E) ≠ 0 := by exact_mod_cast mul_ne_zero hb (ha j)
    refine Set.Finite.of_finite_image (f := fun x => ((b * a j : ℤ) : E) * x) ?_
      (mul_right_injective₀ hne).injOn
    refine (Embeddings.finite_of_norm_le E ℂ ‖((b * a j : ℤ) : ℂ)‖).subset ?_
    rintro _ ⟨x, ⟨h1, h2⟩, rfl⟩
    refine ⟨h1, fun φ => ?_⟩
    rw [map_mul, map_intCast, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (h2 φ)
  refine (Set.Finite.pi' (fun _ : Fin N => Set.Finite.pi' hS)).subset ?_
  rintro (γ : Matrix (Fin N) (Fin N) E) ⟨h1, h2⟩ i j
  refine ⟨?_, fun φ => norm_entry_le c hc γ h1 φ i j⟩
  have := hbL _ (h2 _ (haL j)) i
  convert this using 1
  have h3 := Matrix.mulVec_smul γ (a j) (Pi.single j (1 : E))
  rw [h3]
  simp [mul_assoc]

/- English proof (translation)
Set `L' : Submodule ℤ (Fin N → E)` to `L.restrictScalars ℤ`. Establish `hf' : L'.FG` using `by haveI : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.mpr hf haveI : Module.Finite ℤ L := Module.Finite.trans (𝓞 E) L`. Conclude with `Module.Finite.iff_fg.mp (inferInstanceAs (Module.Finite ℤ L))`. Use `haveI hlat : Submodule.IsLattice ℚ L' := by`. Use `⟨hf', ?_⟩` and prove the remaining obligations.

Rewrite using `[eq_top_iff]`. Introduce `x _`. Take `⟨n, hn, hx⟩` from `exists_int_smul_mem L hs x`. Establish `: x = (n : ℚ)⁻¹ • (n • x)`. Rewrite using `[← Int.cast_smul_eq_zsmul ℚ, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hn), one_smul]`.

Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span hx)`. Use `haveI : Module.Finite ℤ L' := Module.Finite.iff_fg.mpr hf'`. Establish `hr : Module.finrank ℤ L' = Module.finrank ℚ E * N`. Establish `h1 : Module.finrank ℤ L' = Module.finrank ℚ (Fin N → E)`.

Unfold `Module.finrank`. Rewrite using `[Submodule.IsLattice.rank' ℚ L']`. Rewrite using `[h1, Module.finrank_pi_fintype]`. Simplify using `[mul_comm]`. Set `b` to `Module.finBasisOfFinrankEq ℤ L' hr`.

Set `θ : H →* Module.End ℤ L'` to `{ toFun := fun h => ((Matrix.toLin' (ρ h)).restrictScalars ℤ).restrict (p := L') (q := L') (fun x hx => hL h x hx) map_one' := by ext x i; simp map_mul' := by`. Introduce `g h`. Use extensionality with `x i`. Use `show Matrix.toLin' (ρ (g * h)) x i = Matrix.toLin' (ρ g) (Matrix.toLin' (ρ h) x) i`. Simplify using `}`.

Establish `hθ : Function.Injective θ`. Introduce `g h hgh`. Apply `hρ` to reduce the goal to its premises. Apply `Matrix.toLin'.injective` to reduce the goal to its premises. Apply `LinearMap.ext` to reduce the goal to its premises.

Introduce `x`. Take `⟨n, hn, hx⟩` from `exists_int_smul_mem L hs x`. Establish `h1 : Matrix.toLin' (ρ g) (n • x) = Matrix.toLin' (ρ h) (n • x)` using `congrArg Subtype.val (LinearMap.congr_fun hgh ⟨n • x, hx⟩)`. Rewrite `h1` using `[map_zsmul, map_zsmul]`. Conclude with `smul_right_injective _ hn h1`.

Use `⟨(((LinearMap.toMatrixAlgEquiv b).toMonoidHom).comp θ).toHomUnits, ?_⟩` and prove the remaining obligations. Introduce `g h hgh`. Apply `hθ` to reduce the goal to its premises. Apply `(LinearMap.toMatrixAlgEquiv b).injective` to reduce the goal to its premises. Conclude with `congrArg Units.val hgh`.
-/
theorem exists_faithful (L : Submodule (𝓞 E) (Fin N → E)) (hf : L.FG)
    (hs : Submodule.span E (L : Set (Fin N → E)) = ⊤) {H : Type} [Group H]
    (ρ : H →* Matrix (Fin N) (Fin N) E) (hρ : Function.Injective ρ)
    (hL : ∀ h, ∀ x ∈ L, (ρ h).mulVec x ∈ L) :
    ∃ ψ : H →* GL (Fin (Module.finrank ℚ E * N)) ℤ, Function.Injective ψ := by
  let L' : Submodule ℤ (Fin N → E) := L.restrictScalars ℤ
  have hf' : L'.FG := by
    haveI : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.mpr hf
    haveI : Module.Finite ℤ L := Module.Finite.trans (𝓞 E) L
    exact Module.Finite.iff_fg.mp (inferInstanceAs (Module.Finite ℤ L))
  haveI hlat : Submodule.IsLattice ℚ L' := by
    refine ⟨hf', ?_⟩
    rw [eq_top_iff]
    intro x _
    obtain ⟨n, hn, hx⟩ := exists_int_smul_mem L hs x
    have : x = (n : ℚ)⁻¹ • (n • x) := by
      rw [← Int.cast_smul_eq_zsmul ℚ, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hn), one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hx)
  haveI : Module.Finite ℤ L' := Module.Finite.iff_fg.mpr hf'
  have hr : Module.finrank ℤ L' = Module.finrank ℚ E * N := by
    have h1 : Module.finrank ℤ L' = Module.finrank ℚ (Fin N → E) := by
      unfold Module.finrank
      rw [Submodule.IsLattice.rank' ℚ L']
    rw [h1, Module.finrank_pi_fintype]
    simp [mul_comm]
  let b := Module.finBasisOfFinrankEq ℤ L' hr
  let θ : H →* Module.End ℤ L' :=
    { toFun := fun h => ((Matrix.toLin' (ρ h)).restrictScalars ℤ).restrict (p := L') (q := L')
        (fun x hx => hL h x hx)
      map_one' := by ext x i; simp
      map_mul' := by
        intro g h
        ext x i
        show Matrix.toLin' (ρ (g * h)) x i = Matrix.toLin' (ρ g) (Matrix.toLin' (ρ h) x) i
        simp }
  have hθ : Function.Injective θ := by
    intro g h hgh
    apply hρ
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro x
    obtain ⟨n, hn, hx⟩ := exists_int_smul_mem L hs x
    have h1 : Matrix.toLin' (ρ g) (n • x) = Matrix.toLin' (ρ h) (n • x) :=
      congrArg Subtype.val (LinearMap.congr_fun hgh ⟨n • x, hx⟩)
    rw [map_zsmul, map_zsmul] at h1
    exact smul_right_injective _ hn h1
  refine ⟨(((LinearMap.toMatrixAlgEquiv b).toMonoidHom).comp θ).toHomUnits, ?_⟩
  intro g h hgh
  apply hθ
  apply (LinearMap.toMatrixAlgEquiv b).injective
  exact congrArg Units.val hgh

end General

/- English proof (translation)
Establish `h` using `D.host.finrank_cmField`. Rewrite using `[show Module.finrank ℚ D.host.E = _ from h]`. Simplify using `only [fF, Ranks.f, Ranks.n]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem finrank_host (D : D7) : Module.finrank ℚ D.host.E = 2 * fF D := by
  have h := D.host.finrank_cmField
  rw [show Module.finrank ℚ D.host.E = _ from h]
  simp only [fF, Ranks.f, Ranks.n]
  ring

/- English proof (translation)
Introduce `D N J hJ g`. Take `⟨hrat, -, -, huni, hinc⟩` from `GlobalTheory.NormSum.mem_ratG_intG D N`. Take `⟨Lt, hSD, -, hEq, hmv, -⟩` from `GlobalTheory.T.Lt_eq_iff_inv_mul_mem_intG_and_transport D N`. Set `H : Subgroup (GA D N)` to `ratG D N ⊓ J.comap (MulAut.conj g⁻¹).toMonoidHom`. Establish `hH : ∀ x, x ∈ H ↔ x ∈ ratG D N ∧ g⁻¹ * x * g ∈ J`.

Introduce `x`. Simplify using `[H]`. Establish `hcard : gam D J g = Nat.card H` using `Nat.card_congr (Equiv.subtypeEquivRight fun x => (hH x).symm)`. Use `choose r hr using fun h : H => (hrat h).1 ((hH h).1 h.2).1`. Establish `hmap : Function.Injective (fun M : Matrix (Fin N) (Fin N) D.host.E => M.map (inc D))` using `Matrix.map_injective hinc`.

Set `ρ : H →* Matrix (Fin N) (Fin N) D.host.E` to `{ toFun := r map_one' := by`. Apply `hmap` to reduce the goal to its premises. Use `hr 1` as an intermediate fact. Unfold `IsRat at this`. Simplify using `only [← this]`.

Simplify using the standard rewrite rules. Use the proof step `map_mul' := by`. Introduce `x y`. Apply `hmap` to reduce the goal to its premises. Establish `h1` using `hr x`.

Establish `h2` using `hr y`. Establish `h3` using `hr (x * y)`. Unfold `IsRat at h1 h2 h3`. Simplify using `only [Matrix.map_mul, ← h1, ← h2, ← h3]`. Simplify using `}`.

Establish `hρ : Function.Injective ρ`. Introduce `x y hxy`. Establish `h1` using `hr x`. Establish `h2` using `hr y`. Unfold `IsRat at h1 h2`.

Establish `h3 : r x = r y` using `hxy`. Rewrite `h1` using `[h3, ← h2]`. Conclude with `Subtype.ext (Subtype.ext (Units.ext h1))`. Establish `hL : ∀ h : H, ∀ x ∈ Lt g, (ρ h).mulVec x ∈ Lt g`. Introduce `h x hx`.

Establish `h1 : Lt g = Lt (h * g)` using `(hEq _ _).2 (by`. Rewrite using `[← mul_assoc]`. Conclude with `hJ ((hH h).1 h.2).2)`. Use `(hmv h g (r h) (hr h) x).1 hx` as an intermediate fact. Rewrite `this` using `[← h1]`. Then use the resulting hypothesis.

Take `⟨hfg, hspan, -⟩` from `(hSD g).2`. Establish `hfin : Finite H`. Use `(finite_stab D.host.conj (fun φ x => D.host.conjE_apply φ x) (Lt g) hfg hspan).to_subtype` as an intermediate fact. Conclude with `Finite.of_injective (β := {γ : Matrix (Fin N) (Fin N) D.host.E | γ * (γ.map D.host.conj).transpose = 1 ∧ ∀ x ∈ Lt g, γ.mulVec x ∈ Lt g}) (fun h => ⟨ρ h, huni h _ (hr h), hL h⟩) (fun x y hxy => hρ (congrArg Subtype.val hxy))`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hcard]`. Conclude with `Nat.card_pos.ne'`. Take `⟨ψ, hψ⟩` from `exists_faithful (Lt g) hfg hspan ρ hρ hL`. Establish `e` using `(MonoidHom.ofInjective hψ).toEquiv`. Use `GlobalTheory.card_finite_subgroup_GL_int_dvd _ ψ.range (Finite.of_equiv _ e)` as an intermediate fact.

Rewrite `this` using `[← Nat.card_congr e, finrank_host]`. Rewrite using `[hcard]`. Conclude with `this`. Introduce `γ hγ j hj`. Unfold `gam`.

Use `Nat.card_congr ((MulAut.conj γ⁻¹).toEquiv.subtypeEquiv fun x => ?_)` and prove the remaining obligations. Establish `e1 : (MulAut.conj γ⁻¹).toEquiv x = γ⁻¹ * x * γ` using `by simp`. Rewrite using `[e1]`. Establish `e2 : (γ * g * j)⁻¹ * x * (γ * g * j) = j⁻¹ * (g⁻¹ * (γ⁻¹ * x * γ) * g) * j` using `by group`. Rewrite using `[e2, Subgroup.mul_mem_cancel_right _ hj, Subgroup.mul_mem_cancel_left _ (J.inv_mem hj), Subgroup.mul_mem_cancel_right _ hγ, Subgroup.mul_mem_cancel_left _ ((ratG D N).inv_mem hγ)]`.
-/
theorem gam_ne_zero_dvd_invariant : ∀ (D : D7) (N : ℕ) (J : Subgroup (GA D N)), J ≤ intG D N → ∀ g, gam D J g ≠ 0 ∧ gam D J g ∣ 8 ^ (2 * fF D * N) * (2 * (2 * fF D * N)).factorial ∧ ∀ γ ∈ ratG D N, ∀ j ∈ J, gam D J (γ * g * j) = gam D J g := by
  intro D N J hJ g
  obtain ⟨hrat, -, -, huni, hinc⟩ := GlobalTheory.NormSum.mem_ratG_intG D N
  obtain ⟨Lt, hSD, -, hEq, hmv, -⟩ := GlobalTheory.T.Lt_eq_iff_inv_mul_mem_intG_and_transport D N
  let H : Subgroup (GA D N) := ratG D N ⊓ J.comap (MulAut.conj g⁻¹).toMonoidHom
  have hH : ∀ x, x ∈ H ↔ x ∈ ratG D N ∧ g⁻¹ * x * g ∈ J := by
    intro x; simp [H]
  have hcard : gam D J g = Nat.card H :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => (hH x).symm)
  choose r hr using fun h : H => (hrat h).1 ((hH h).1 h.2).1
  have hmap : Function.Injective (fun M : Matrix (Fin N) (Fin N) D.host.E => M.map (inc D)) :=
    Matrix.map_injective hinc
  let ρ : H →* Matrix (Fin N) (Fin N) D.host.E :=
    { toFun := r
      map_one' := by
        apply hmap
        have := hr 1
        unfold IsRat at this
        simp only [← this]
        simp
      map_mul' := by
        intro x y
        apply hmap
        have h1 := hr x
        have h2 := hr y
        have h3 := hr (x * y)
        unfold IsRat at h1 h2 h3
        simp only [Matrix.map_mul, ← h1, ← h2, ← h3]
        simp }
  have hρ : Function.Injective ρ := by
    intro x y hxy
    have h1 := hr x
    have h2 := hr y
    unfold IsRat at h1 h2
    have h3 : r x = r y := hxy
    rw [h3, ← h2] at h1
    exact Subtype.ext (Subtype.ext (Units.ext h1))
  have hL : ∀ h : H, ∀ x ∈ Lt g, (ρ h).mulVec x ∈ Lt g := by
    intro h x hx
    have h1 : Lt g = Lt (h * g) := (hEq _ _).2 (by
      rw [← mul_assoc]; exact hJ ((hH h).1 h.2).2)
    have := (hmv h g (r h) (hr h) x).1 hx
    rwa [← h1] at this
  obtain ⟨hfg, hspan, -⟩ := (hSD g).2
  have hfin : Finite H := by
    have := (finite_stab D.host.conj
      (fun φ x => D.host.conjE_apply φ x) (Lt g) hfg hspan).to_subtype
    exact Finite.of_injective (β := {γ : Matrix (Fin N) (Fin N) D.host.E |
        γ * (γ.map D.host.conj).transpose = 1 ∧ ∀ x ∈ Lt g, γ.mulVec x ∈ Lt g})
      (fun h => ⟨ρ h, huni h _ (hr h), hL h⟩) (fun x y hxy => hρ (congrArg Subtype.val hxy))
  refine ⟨?_, ?_, ?_⟩
  · rw [hcard]; exact Nat.card_pos.ne'
  · obtain ⟨ψ, hψ⟩ := exists_faithful (Lt g) hfg hspan ρ hρ hL
    have e := (MonoidHom.ofInjective hψ).toEquiv
    have := GlobalTheory.card_finite_subgroup_GL_int_dvd _ ψ.range (Finite.of_equiv _ e)
    rw [← Nat.card_congr e, finrank_host] at this
    rw [hcard]; exact this
  · intro γ hγ j hj
    unfold gam
    refine Nat.card_congr ((MulAut.conj γ⁻¹).toEquiv.subtypeEquiv fun x => ?_)
    have e1 : (MulAut.conj γ⁻¹).toEquiv x = γ⁻¹ * x * γ := by simp
    rw [e1]
    have e2 : (γ * g * j)⁻¹ * x * (γ * g * j) = j⁻¹ * (g⁻¹ * (γ⁻¹ * x * γ) * g) * j := by group
    rw [e2, Subgroup.mul_mem_cancel_right _ hj, Subgroup.mul_mem_cancel_left _ (J.inv_mem hj),
      Subgroup.mul_mem_cancel_right _ hγ, Subgroup.mul_mem_cancel_left _ ((ratG D N).inv_mem hγ)]

end GlobalTheory.StabOrder
