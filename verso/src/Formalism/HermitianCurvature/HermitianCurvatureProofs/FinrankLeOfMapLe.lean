import Formalism.HermitianCurvature.PrimeToDifferent

namespace Formalism.FourierDecayAlt.P.S6x3

open Formalism.FourierDecayAlt.S6
open NumberField NumberField.IsCMField Module
open scoped nonZeroDivisors

/- English proof (translation)
Rewrite using `[trace_eq_sum_automorphisms]`. Establish `hu : (Finset.univ : Finset (E ≃ₐ[maximalRealSubfield E] E)) = {1, complexConj E}`. Use `symm`. Apply `Finset.eq_univ_of_card` to reduce the goal to its premises. Rewrite using `[Finset.card_pair (complexConj_ne_one E).symm, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, Algebra.IsQuadraticExtension.finrank_eq_two]`.

Rewrite using `[hu, Finset.sum_pair (complexConj_ne_one E).symm]`. Both sides reduce to the same expression.
-/
theorem trace_eq (E : Type) [Field E] [NumberField E] [IsCMField E] (x : E) :
    algebraMap (maximalRealSubfield E) E (Algebra.trace (maximalRealSubfield E) E x)
      = x + complexConj E x := by
  classical
  rw [trace_eq_sum_automorphisms]
  have hu : (Finset.univ : Finset (E ≃ₐ[maximalRealSubfield E] E)) = {1, complexConj E} := by
    symm
    apply Finset.eq_univ_of_card
    rw [Finset.card_pair (complexConj_ne_one E).symm, ← Nat.card_eq_fintype_card,
      IsGalois.card_aut_eq_finrank, Algebra.IsQuadraticExtension.finrank_eq_two]
  rw [hu, Finset.sum_pair (complexConj_ne_one E).symm]
  rfl

/- English proof (translation)
Use `set F := maximalRealSubfield E with hF`. Set `I : Ideal (𝓞 F)` to `LinearMap.range (Algebra.intTrace (𝓞 F) (𝓞 E))`. Establish `key : I ⊔ Ideal.span {(g : 𝓞 F)} = ⊤`. Assume the negation of the conclusion as `hne`. Take `⟨P, hP, hle⟩` from `Ideal.exists_le_maximal _ hne`.

Establish `hgP : (g : 𝓞 F) ∈ P` using `hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))`. Establish `hP0 : P ≠ ⊥`. Introduce `h`. Rewrite `hgP` using `[h, Ideal.mem_bot]`. Conclude with `hg.ne' (by exact_mod_cast hgP)`.

Take `⟨x, hx, hx1⟩` from `FractionalIdeal.exists_notMem_one_of_ne_bot (K := F) hP0 hP.ne_top`. Establish `hPF : ((P : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) ≠ 0`. Simplify using `using hP0`. Rewrite `hx` using `[FractionalIdeal.mem_inv_iff hPF]`. Establish `hxP : ∀ p ∈ P, ∃ z : 𝓞 F, x * (p : F) = z`.

Introduce `p hp`. Use `hx (algebraMap (𝓞 F) F p) ((FractionalIdeal.mem_coeIdeal _).mpr ⟨p, hp, rfl⟩)` as an intermediate fact. Take `⟨z, hz⟩` from `(FractionalIdeal.mem_one_iff _).mp this`. Conclude with `⟨z, hz.symm⟩`. Establish `h10 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0` using `one_ne_zero`.

Establish `hdual : algebraMap F E x ∈ FractionalIdeal.dual (𝓞 F) F (1 : FractionalIdeal (𝓞 E)⁰ E)`. Rewrite using `[FractionalIdeal.mem_dual h10]`. Introduce `a ha`. Take `⟨a0, rfl⟩` from `(FractionalIdeal.mem_one_iff _).mp ha`. Establish `h1 : Algebra.traceForm F E (algebraMap F E x) (algebraMap (𝓞 E) E a0) = x * algebraMap (𝓞 F) F (Algebra.intTrace (𝓞 F) (𝓞 E) a0)`.

Rewrite using `[Algebra.traceForm_apply, ← Algebra.smul_def, map_smul, smul_eq_mul, Algebra.algebraMap_intTrace (L := E)]`. Rewrite using `[h1]`. Take `⟨z, hz⟩` from `hxP (Algebra.intTrace (𝓞 F) (𝓞 E) a0) (hle (Ideal.mem_sup_left ⟨a0, rfl⟩))`. Conclude with `⟨z, hz.symm⟩`. Take `⟨d, hd, j, hj, hdj⟩` from `Ideal.isCoprime_iff_exists.mp hU`.

Take `⟨y, rfl⟩` from `Ideal.mem_span_singleton'.mp hj`. Establish `hd' : algebraMap (𝓞 E) E d ∈ (FractionalIdeal.dual (𝓞 F) F (1 : FractionalIdeal (𝓞 E)⁰ E))⁻¹`. Rewrite using `[← coeIdeal_differentIdeal (𝓞 F) F E (𝓞 E)]`. Conclude with `(FractionalIdeal.mem_coeIdeal _).mpr ⟨d, hd, rfl⟩`. Rewrite `hd'` using `[FractionalIdeal.mem_inv_iff (FractionalIdeal.dual_ne_zero _ _ h10)]`.

Take `⟨z1, hz1⟩` from `(FractionalIdeal.mem_one_iff _).mp (hd' _ hdual)`. Take `⟨z2, hz2⟩` from `hxP _ hgP`. Establish `hxE : algebraMap F E x = algebraMap (𝓞 E) E (z1 + y * algebraMap (𝓞 F) (𝓞 E) z2)`. Establish `e1 : algebraMap (𝓞 E) E d + algebraMap (𝓞 E) E y * (g : E) = 1`. Use `congrArg (algebraMap (𝓞 E) E) hdj` as an intermediate fact.

Simplify using `using this`. Establish `e2 : algebraMap F E x * (g : E) = algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) z2)`. Use `congrArg (algebraMap F E) hz2` as an intermediate fact. Rewrite `this` using `[map_mul]`. Establish `e4 : algebraMap F E (((g : 𝓞 F) : 𝓞 F) : F) = (g : E)` using `by simp`.

Rewrite `this` using `[e4]`. Conclude with `this`. Rewrite using `[map_add, map_mul, hz1, ← e2]`. Take the linear combination `(-(algebraMap F E x)) * e1`. Establish `hint : IsIntegral ℤ x`.

Establish `: IsIntegral ℤ (algebraMap F E x)`. Rewrite using `[hxE]`. Conclude with `RingOfIntegers.isIntegral_coe _`. Conclude with `(isIntegral_algebraMap_iff (algebraMap F E).injective).mp this`. Conclude with `hx1 ((FractionalIdeal.mem_one_iff _).mpr ⟨⟨x, hint⟩, rfl⟩)`.

Establish `h1 : (1 : 𝓞 F) ∈ I ⊔ Ideal.span {(g : 𝓞 F)}` using `by rw [key]; trivial`. Take `⟨i, ⟨θ, rfl⟩, j, hj, hij⟩` from `Submodule.mem_sup.mp h1`. Take `⟨w, rfl⟩` from `Ideal.mem_span_singleton'.mp hj`. Use `⟨θ, -algebraMap (𝓞 F) (𝓞 E) w, ?_⟩` and prove the remaining obligations. Rewrite using `[← trace_eq, ← Algebra.algebraMap_intTrace (A := 𝓞 F) (B := 𝓞 E)]`.

Use `congrArg (fun t : 𝓞 F => algebraMap F E (algebraMap (𝓞 F) F t)) hij` as an intermediate fact. Simplify using `only [map_add, map_mul, map_one, map_natCast] at this`. Establish `e3 : algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) w) = algebraMap F E (algebraMap (𝓞 F) F w)` using `rfl`. Establish `e5 : ((-algebraMap (𝓞 F) (𝓞 E) w : 𝓞 E) : E) = -algebraMap F E (algebraMap (𝓞 F) F w)`. Rewrite using `[← e3]`.

Conclude with `map_neg (algebraMap (𝓞 E) E) _`. Rewrite using `[e5]`. Take the linear combination `this`.
-/
theorem exists_theta (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (hg : 0 < g)
    (hU : UnramAbove E g) :
    ∃ θ w : 𝓞 E, (θ : E) + complexConj E θ = 1 + (g : E) * w := by
  set F := maximalRealSubfield E with hF
  let I : Ideal (𝓞 F) := LinearMap.range (Algebra.intTrace (𝓞 F) (𝓞 E))
  have key : I ⊔ Ideal.span {(g : 𝓞 F)} = ⊤ := by
    by_contra hne
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
    have hgP : (g : 𝓞 F) ∈ P := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    have hP0 : P ≠ ⊥ := by
      intro h
      rw [h, Ideal.mem_bot] at hgP
      exact hg.ne' (by exact_mod_cast hgP)
    obtain ⟨x, hx, hx1⟩ := FractionalIdeal.exists_notMem_one_of_ne_bot (K := F) hP0 hP.ne_top
    have hPF : ((P : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := by
      simpa using hP0
    rw [FractionalIdeal.mem_inv_iff hPF] at hx
    have hxP : ∀ p ∈ P, ∃ z : 𝓞 F, x * (p : F) = z := by
      intro p hp
      have := hx (algebraMap (𝓞 F) F p) ((FractionalIdeal.mem_coeIdeal _).mpr ⟨p, hp, rfl⟩)
      obtain ⟨z, hz⟩ := (FractionalIdeal.mem_one_iff _).mp this
      exact ⟨z, hz.symm⟩

    have h10 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := one_ne_zero
    have hdual : algebraMap F E x ∈ FractionalIdeal.dual (𝓞 F) F (1 : FractionalIdeal (𝓞 E)⁰ E) := by
      rw [FractionalIdeal.mem_dual h10]
      intro a ha
      obtain ⟨a0, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp ha
      have h1 : Algebra.traceForm F E (algebraMap F E x) (algebraMap (𝓞 E) E a0)
          = x * algebraMap (𝓞 F) F (Algebra.intTrace (𝓞 F) (𝓞 E) a0) := by
        rw [Algebra.traceForm_apply, ← Algebra.smul_def, map_smul, smul_eq_mul,
          Algebra.algebraMap_intTrace (L := E)]
      rw [h1]
      obtain ⟨z, hz⟩ := hxP (Algebra.intTrace (𝓞 F) (𝓞 E) a0)
        (hle (Ideal.mem_sup_left ⟨a0, rfl⟩))
      exact ⟨z, hz.symm⟩
    obtain ⟨d, hd, j, hj, hdj⟩ := Ideal.isCoprime_iff_exists.mp hU
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp hj
    have hd' : algebraMap (𝓞 E) E d ∈
        (FractionalIdeal.dual (𝓞 F) F (1 : FractionalIdeal (𝓞 E)⁰ E))⁻¹ := by
      rw [← coeIdeal_differentIdeal (𝓞 F) F E (𝓞 E)]
      exact (FractionalIdeal.mem_coeIdeal _).mpr ⟨d, hd, rfl⟩
    rw [FractionalIdeal.mem_inv_iff (FractionalIdeal.dual_ne_zero _ _ h10)] at hd'
    obtain ⟨z1, hz1⟩ := (FractionalIdeal.mem_one_iff _).mp (hd' _ hdual)
    obtain ⟨z2, hz2⟩ := hxP _ hgP
    have hxE : algebraMap F E x = algebraMap (𝓞 E) E (z1 + y * algebraMap (𝓞 F) (𝓞 E) z2) := by
      have e1 : algebraMap (𝓞 E) E d + algebraMap (𝓞 E) E y * (g : E) = 1 := by
        have := congrArg (algebraMap (𝓞 E) E) hdj
        simpa using this
      have e2 : algebraMap F E x * (g : E) = algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) z2) := by
        have := congrArg (algebraMap F E) hz2
        rw [map_mul] at this
        have e4 : algebraMap F E (((g : 𝓞 F) : 𝓞 F) : F) = (g : E) := by simp
        rw [e4] at this
        exact this
      rw [map_add, map_mul, hz1, ← e2]
      linear_combination (-(algebraMap F E x)) * e1
    have hint : IsIntegral ℤ x := by
      have : IsIntegral ℤ (algebraMap F E x) := by
        rw [hxE]; exact RingOfIntegers.isIntegral_coe _
      exact (isIntegral_algebraMap_iff (algebraMap F E).injective).mp this
    exact hx1 ((FractionalIdeal.mem_one_iff _).mpr ⟨⟨x, hint⟩, rfl⟩)
  have h1 : (1 : 𝓞 F) ∈ I ⊔ Ideal.span {(g : 𝓞 F)} := by rw [key]; trivial
  obtain ⟨i, ⟨θ, rfl⟩, j, hj, hij⟩ := Submodule.mem_sup.mp h1
  obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.mp hj
  refine ⟨θ, -algebraMap (𝓞 F) (𝓞 E) w, ?_⟩
  rw [← trace_eq, ← Algebra.algebraMap_intTrace (A := 𝓞 F) (B := 𝓞 E)]
  have := congrArg (fun t : 𝓞 F => algebraMap F E (algebraMap (𝓞 F) F t)) hij
  simp only [map_add, map_mul, map_one, map_natCast] at this
  have e3 : algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) w) = algebraMap F E (algebraMap (𝓞 F) F w) := rfl
  have e5 : ((-algebraMap (𝓞 F) (𝓞 E) w : 𝓞 E) : E)
      = -algebraMap F E (algebraMap (𝓞 F) F w) := by
    rw [← e3]; exact map_neg (algebraMap (𝓞 E) E) _
  rw [e5]
  linear_combination this

section Lattices

variable (E : Type) [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Unfold `twLat`. Rewrite using `[Submodule.mem_inf, Submodule.mem_comap]`. Establish `: ((LinearMap.id : E →ₗ[ℤ] E) - ((-1 : ℤ) ^ s) • conjZ E) t = t - (-1) ^ s * complexConj E t`. Rewrite using `[LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, zsmul_eq_mul]`. Use `push_cast`.

Both sides reduce to the same expression. Rewrite using `[this]`. Both sides reduce to the same expression.
-/
theorem mem_twLat (A B : FI E) (s : ℕ) (t : E) :
    t ∈ twLat E A B s ↔ t ∈ A ∧ t - (-1) ^ s * complexConj E t ∈ B := by
  unfold twLat
  rw [Submodule.mem_inf, Submodule.mem_comap]
  have : ((LinearMap.id : E →ₗ[ℤ] E) - ((-1 : ℤ) ^ s) • conjZ E) t
      = t - (-1) ^ s * complexConj E t := by
    rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, zsmul_eq_mul]
    push_cast
    rfl
  rw [this]; rfl

noncomputable def eig (A : FI E) (s : ℕ) : Submodule ℤ E :=
  zsub E A ⊓ LinearMap.ker (LinearMap.id - ((-1 : ℤ) ^ s) • conjZ E)

/- English proof (translation)
Unfold `eig`. Rewrite using `[Submodule.mem_inf, LinearMap.mem_ker]`. Establish `: ((LinearMap.id : E →ₗ[ℤ] E) - ((-1 : ℤ) ^ s) • conjZ E) t = t - (-1) ^ s * complexConj E t`. Rewrite using `[LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, zsmul_eq_mul]`. Use `push_cast`.

Both sides reduce to the same expression. Rewrite using `[this]`. Both sides reduce to the same expression.
-/
theorem mem_eig (A : FI E) (s : ℕ) (t : E) :
    t ∈ eig E A s ↔ t ∈ A ∧ t - (-1) ^ s * complexConj E t = 0 := by
  unfold eig
  rw [Submodule.mem_inf, LinearMap.mem_ker]
  have : ((LinearMap.id : E →ₗ[ℤ] E) - ((-1 : ℤ) ^ s) • conjZ E) t
      = t - (-1) ^ s * complexConj E t := by
    rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, zsmul_eq_mul]
    push_cast
    rfl
  rw [this]; rfl

/- English proof (translation)
Use `(A : Submodule (𝓞 E) E).smul_mem z ht` as an intermediate fact. Rewrite `this` using `[Algebra.smul_def]`. Conclude with `this`.
-/
theorem mul_mem_FI (A : FI E) (z : 𝓞 E) (t : E) (ht : t ∈ A) : (z : E) * t ∈ A := by
  have := (A : Submodule (𝓞 E) E).smul_mem z ht
  rw [Algebra.smul_def] at this
  exact this

/- English proof (translation)
Use `mul_mem_FI E A ((-1) ^ s) t ht` as an intermediate fact. Simplify using `using this`.
-/
theorem sign_mem (A : FI E) (s : ℕ) (t : E) (ht : t ∈ A) : (-1) ^ s * t ∈ A := by
  have := mul_mem_FI E A ((-1) ^ s) t ht
  simpa using this

/- English proof (translation)
Rewrite using `[← mul_pow]`. Simplify using the standard rewrite rules.
-/
theorem sign_sq (s : ℕ) : ((-1 : E) ^ s) * (-1) ^ s = 1 := by
  rw [← mul_pow]; simp

/- English proof (translation)
Rewrite using `[mul_comm, FractionalIdeal.mem_singleton_mul]`.
-/
theorem mem_gA (A : FI E) (g : ℕ) (x : E) :
    x ∈ A * FractionalIdeal.spanSingleton (𝓞 E)⁰ (g : E) ↔ ∃ a ∈ A, x = (g : E) * a := by
  rw [mul_comm, FractionalIdeal.mem_singleton_mul]

/- English proof (translation)
Take `⟨a, ha, rfl⟩` from `(mem_gA E A g x).mp hx`. Use `mul_mem_FI E A (g : 𝓞 E) a ha` as an intermediate fact. Simplify using `using this`.
-/
theorem gA_le (A : FI E) (g : ℕ) (x : E)
    (hx : x ∈ A * FractionalIdeal.spanSingleton (𝓞 E)⁰ (g : E)) : x ∈ A := by
  obtain ⟨a, ha, rfl⟩ := (mem_gA E A g x).mp hx
  have := mul_mem_FI E A (g : 𝓞 E) a ha
  simpa using this

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce `t ht`. Take `⟨ht1, ht2⟩` from `(mem_twLat E _ _ s t).mp ht`. Take `⟨θ, w, hθ⟩` from `exists_theta E g hg hU`. Establish `h1 : (θ : E) * t ∈ A` using `mul_mem_FI E A θ t ht1`.

Establish `h2 : (θ : E) * t + (-1) ^ s * complexConj E ((θ : E) * t) ∈ eig E A s`. Rewrite using `[mem_eig]`. Use `⟨A.val.add_mem h1 (sign_mem E A s _ (hA _ h1)), ?_⟩` and prove the remaining obligations. Simplify using `only [map_add, map_mul, map_pow, map_neg, map_one, complexConj_apply_apply]`. Take the linear combination `(-(θ : E) * t) * sign_sq E s`.

Establish `h3 : complexConj E θ * (t - (-1) ^ s * complexConj E t) - (g : E) * ((w : E) * t) ∈ zsub E (A * FractionalIdeal.spanSingleton _ (g : E))`. Use `Submodule.sub_mem _ ?_ ?_` and prove the remaining obligations. Conclude with `mul_mem_FI E _ (ringOfIntegersComplexConj E θ) _ ht2`. Conclude with `(mem_gA E A g _).mpr ⟨_, mul_mem_FI E A w t ht1, rfl⟩`. Establish `h4 : t = ((θ : E) * t + (-1) ^ s * complexConj E ((θ : E) * t)) + (complexConj E θ * (t - (-1) ^ s * complexConj E t) - (g : E) * ((w : E) * t))`.

Rewrite using `[map_mul]`. Take the linear combination `(-t) * hθ`. Rewrite using `[h4]`. Conclude with `Submodule.add_mem_sup h2 h3`. Use `sup_le ?_ ?_` and prove the remaining obligations.

Introduce `t ht`. Take `⟨ht1, ht2⟩` from `(mem_eig E A s t).mp ht`. Rewrite using `[mem_twLat, ht2]`. Conclude with `⟨ht1, Submodule.zero_mem _⟩`. Introduce `t ht`.

Rewrite using `[mem_twLat]`. Use `⟨gA_le E A g t ht, ?_⟩` and prove the remaining obligations. Take `⟨a, ha, rfl⟩` from `(mem_gA E A g t).mp ht`. Use `(mem_gA E A g _).mpr ⟨a - (-1) ^ s * complexConj E a, A.val.sub_mem ha (sign_mem E A s _ (hA _ ha)), ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_natCast]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem tw_eq (A : FI E) (g s : ℕ) (hA : ConjStable E A) (hg : 0 < g) (hU : UnramAbove E g) :
    twLat E A (A * FractionalIdeal.spanSingleton _ (g : E)) s
      = eig E A s ⊔ zsub E (A * FractionalIdeal.spanSingleton _ (g : E)) := by
  apply le_antisymm
  · intro t ht
    obtain ⟨ht1, ht2⟩ := (mem_twLat E _ _ s t).mp ht
    obtain ⟨θ, w, hθ⟩ := exists_theta E g hg hU
    have h1 : (θ : E) * t ∈ A := mul_mem_FI E A θ t ht1
    have h2 : (θ : E) * t + (-1) ^ s * complexConj E ((θ : E) * t) ∈ eig E A s := by
      rw [mem_eig]
      refine ⟨A.val.add_mem h1 (sign_mem E A s _ (hA _ h1)), ?_⟩
      simp only [map_add, map_mul, map_pow, map_neg, map_one, complexConj_apply_apply]
      linear_combination (-(θ : E) * t) * sign_sq E s
    have h3 : complexConj E θ * (t - (-1) ^ s * complexConj E t) - (g : E) * ((w : E) * t)
        ∈ zsub E (A * FractionalIdeal.spanSingleton _ (g : E)) := by
      refine Submodule.sub_mem _ ?_ ?_
      · exact mul_mem_FI E _ (ringOfIntegersComplexConj E θ) _ ht2
      · exact (mem_gA E A g _).mpr ⟨_, mul_mem_FI E A w t ht1, rfl⟩
    have h4 : t = ((θ : E) * t + (-1) ^ s * complexConj E ((θ : E) * t)) +
        (complexConj E θ * (t - (-1) ^ s * complexConj E t) - (g : E) * ((w : E) * t)) := by
      rw [map_mul]
      linear_combination (-t) * hθ
    rw [h4]
    exact Submodule.add_mem_sup h2 h3
  · refine sup_le ?_ ?_
    · intro t ht
      obtain ⟨ht1, ht2⟩ := (mem_eig E A s t).mp ht
      rw [mem_twLat, ht2]
      exact ⟨ht1, Submodule.zero_mem _⟩
    · intro t ht
      rw [mem_twLat]
      refine ⟨gA_le E A g t ht, ?_⟩
      obtain ⟨a, ha, rfl⟩ := (mem_gA E A g t).mp ht
      refine (mem_gA E A g _).mpr ⟨a - (-1) ^ s * complexConj E a,
        A.val.sub_mem ha (sign_mem E A s _ (hA _ ha)), ?_⟩
      rw [map_mul, map_natCast]
      ring

end Lattices

section Ranks

variable (E : Type) [Field E] [NumberField E] [IsCMField E]

instance finite_zsub (A : FI E) : Module.Finite ℤ (zsub E A) :=
  inferInstanceAs (Module.Finite ℤ A)

/- English proof (translation)
Use `fractionalIdeal_rank E (Units.mk0 A hA)` as an intermediate fact. Rewrite `this` using `[RingOfIntegers.rank]`. Conclude with `this`.
-/
theorem finrank_zsub (A : FI E) (hA : A ≠ 0) : finrank ℤ (zsub E A) = finrank ℚ E := by
  have := fractionalIdeal_rank E (Units.mk0 A hA)
  rw [RingOfIntegers.rank] at this
  exact this

/- English proof (translation)
Establish `: IsNoetherian ℤ (zsub E A)` using `inferInstance`. Use `isNoetherian_of_le h` as an intermediate fact. Use `infer_instance`.
-/
theorem finite_of_le (N : Submodule ℤ E) (A : FI E) (h : N ≤ zsub E A) : Module.Finite ℤ N := by
  have : IsNoetherian ℤ (zsub E A) := inferInstance
  have := isNoetherian_of_le h
  infer_instance

/- English proof (translation)
Rewrite using `[(Submodule.equivMapOfInjective f hf N).finrank_eq]`. Conclude with `Submodule.finrank_mono h`.
-/
theorem finrank_le_of_map_le (f : E →ₗ[ℤ] E) (hf : Function.Injective f) (N N' : Submodule ℤ E)
    [Module.Finite ℤ N'] (h : N.map f ≤ N') : finrank ℤ N ≤ finrank ℤ N' := by
  rw [(Submodule.equivMapOfInjective f hf N).finrank_eq]
  exact Submodule.finrank_mono h

/- English proof (translation)
Establish `h1 : Module.Finite ℤ ↥(AddSubgroup.toIntSubmodule N.toAddSubgroup)` using `inferInstanceAs (Module.Finite ℤ N)`. Establish `h2 : Module.Free ℤ ↥(AddSubgroup.toIntSubmodule N.toAddSubgroup)` using `inferInstance`. Conclude with `AddSubgroup.relIndex_map_nsmul g N.toAddSubgroup`.
-/
theorem relIndex_nsmul (N : Submodule ℤ E) [Module.Finite ℤ N] (g : ℕ) :
    (N.toAddSubgroup.map (nsmulAddMonoidHom (α := E) g)).relIndex N.toAddSubgroup
      = g ^ finrank ℤ N := by
  have h1 : Module.Finite ℤ ↥(AddSubgroup.toIntSubmodule N.toAddSubgroup) :=
    inferInstanceAs (Module.Finite ℤ N)
  have h2 : Module.Free ℤ ↥(AddSubgroup.toIntSubmodule N.toAddSubgroup) := inferInstance
  exact AddSubgroup.relIndex_map_nsmul g N.toAddSubgroup

/- English proof (translation)
Establish `hinj : Function.Injective (N₁.subtype.coprod N₂.subtype)`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_coprod_of_disjoint_range]`. Simplify using the standard rewrite rules. Simplify using `using h`. Use `LinearMap.finrank_range_of_inj hinj` as an intermediate fact.

Rewrite `this` using `[LinearMap.range_coprod, Submodule.range_subtype, Submodule.range_subtype, Module.finrank_prod]`. Conclude with `this`.
-/
theorem finrank_sup (N₁ N₂ : Submodule ℤ E) [Module.Finite ℤ N₁] [Module.Finite ℤ N₂]
    (h : Disjoint N₁ N₂) : finrank ℤ ↥(N₁ ⊔ N₂) = finrank ℤ N₁ + finrank ℤ N₂ := by
  have hinj : Function.Injective (N₁.subtype.coprod N₂.subtype) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_coprod_of_disjoint_range]
    · simp
    · simpa using h
  have := LinearMap.finrank_range_of_inj hinj
  rw [LinearMap.range_coprod, Submodule.range_subtype, Submodule.range_subtype,
    Module.finrank_prod] at this
  exact this

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push Not at h`. Establish `hfix : ∀ a : 𝓞 E, complexConj E a = a`. Introduce `a`. Assume the negation of the conclusion as `hne`.

Use `h (a - ringOfIntegersComplexConj E a) ?_ ?_` and prove the remaining obligations. Introduce `h0`. Apply `hne` to reduce the goal to its premises. Establish `: (a : E) - complexConj E a = 0` using `h0`. Take the linear combination `-this`.

Establish `: ((a - ringOfIntegersComplexConj E a : 𝓞 E) : E) = (a : E) - complexConj E a` using `rfl`. Rewrite using `[this, map_sub, complexConj_apply_apply]`. Expand and normalize the polynomial expressions, which then agree. Apply `complexConj_ne_one E` to reduce the goal to its premises. Use extensionality with `x`.

Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (A := 𝓞 E) x`. Rewrite using `[map_div₀, hfix, hfix]`. Both sides reduce to the same expression.
-/
theorem exists_delta : ∃ δ : 𝓞 E, (δ : E) ≠ 0 ∧ complexConj E δ = -(δ : E) := by
  by_contra h
  push Not at h
  have hfix : ∀ a : 𝓞 E, complexConj E a = a := by
    intro a
    by_contra hne
    refine h (a - ringOfIntegersComplexConj E a) ?_ ?_
    · intro h0
      apply hne
      have : (a : E) - complexConj E a = 0 := h0
      linear_combination -this
    · have : ((a - ringOfIntegersComplexConj E a : 𝓞 E) : E) = (a : E) - complexConj E a := rfl
      rw [this, map_sub, complexConj_apply_apply]
      ring
  apply complexConj_ne_one E
  ext x
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
  rw [map_div₀, hfix, hfix]
  rfl

instance finite_eig (A : FI E) (s : ℕ) : Module.Finite ℤ (eig E A s) :=
  finite_of_le E _ A inf_le_left

/- English proof (translation)
Take `⟨δ, h0, hδ⟩` from `exists_delta E`. Use `finrank_le_of_map_le E (LinearMap.mulLeft ℤ (δ : E)) (mul_right_injective₀ h0) _ _ ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨t, ht, rfl⟩`. Take `⟨ht1, ht2⟩` from `(mem_eig E A s t).mp ht`. Rewrite using `[mem_eig, LinearMap.mulLeft_apply]`.

Use `⟨mul_mem_FI E A δ t ht1, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, hδ, pow_succ]`. Take the linear combination `(δ : E) * ht2`.
-/
theorem rk_le (A : FI E) (s : ℕ) : finrank ℤ (eig E A s) ≤ finrank ℤ (eig E A (s + 1)) := by
  obtain ⟨δ, h0, hδ⟩ := exists_delta E
  refine finrank_le_of_map_le E (LinearMap.mulLeft ℤ (δ : E)) (mul_right_injective₀ h0) _ _ ?_
  rintro _ ⟨t, ht, rfl⟩
  obtain ⟨ht1, ht2⟩ := (mem_eig E A s t).mp ht
  rw [mem_eig, LinearMap.mulLeft_apply]
  refine ⟨mul_mem_FI E A δ t ht1, ?_⟩
  rw [map_mul, hδ, pow_succ]
  linear_combination (δ : E) * ht2

/- English proof (translation)
Use extensionality with `t`. Rewrite using `[mem_eig, mem_eig, pow_add]`. Simplify using the standard rewrite rules.
-/
theorem eig_add_two (A : FI E) (s : ℕ) : eig E A (s + 2) = eig E A s := by
  ext t
  rw [mem_eig, mem_eig, pow_add]
  simp

/- English proof (translation)
Apply `le_antisymm _ (rk_le E A s)` to reduce the goal to its premises. Use `rk_le E A (s + 1)` as an intermediate fact. Rewrite `this` using `[eig_add_two]`. Then use the resulting hypothesis.
-/
theorem rk_succ (A : FI E) (s : ℕ) : finrank ℤ (eig E A (s + 1)) = finrank ℤ (eig E A s) := by
  apply le_antisymm _ (rk_le E A s)
  have := rk_le E A (s + 1)
  rwa [eig_add_two] at this

/- English proof (translation)
Establish `hd : Disjoint (eig E A s) (eig E A (s + 1))`. Rewrite using `[Submodule.disjoint_def]`. Introduce `t h1 h2`. Establish `e1` using `((mem_eig E A s t).mp h1).2`. Establish `e2` using `((mem_eig E A (s + 1) t).mp h2).2`.

Rewrite `e2` using `[pow_succ]`. Establish `: (2 : E) * t = 0` using `by linear_combination e1 + e2`. Simplify using `using this`. Rewrite using `[← finrank_sup E _ _ hd]`. Apply `le_antisymm` to reduce the goal to its premises.

Conclude with `Submodule.finrank_mono (sup_le inf_le_left inf_le_left)`. Establish `: Module.Finite ℤ ↥(eig E A s ⊔ eig E A (s + 1))` using `finite_of_le E _ A (sup_le inf_le_left inf_le_left)`. Use `finrank_le_of_map_le E (LinearMap.mulLeft ℤ (2 : E)) (mul_right_injective₀ two_ne_zero) _ _ ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨a, ha, rfl⟩`. Establish `ha' : a ∈ A` using `ha`.

Establish `hc` using `sign_mem E A s _ (hA _ ha')`. Establish `h1 : a + (-1) ^ s * complexConj E a ∈ eig E A s`. Rewrite using `[mem_eig]`. Use `⟨A.val.add_mem ha' hc, ?_⟩` and prove the remaining obligations. Simplify using `only [map_add, map_mul, map_pow, map_neg, map_one, complexConj_apply_apply]`.

Take the linear combination `(-a) * sign_sq E s`. Establish `h2 : a - (-1) ^ s * complexConj E a ∈ eig E A (s + 1)`. Rewrite using `[mem_eig]`. Use `⟨A.val.sub_mem ha' hc, ?_⟩` and prove the remaining obligations. Simplify using `only [map_sub, map_mul, map_pow, map_neg, map_one, complexConj_apply_apply, pow_succ]`.

Take the linear combination `(-a) * sign_sq E s`. Establish `h3 : LinearMap.mulLeft ℤ (2 : E) a = (a + (-1) ^ s * complexConj E a) + (a - (-1) ^ s * complexConj E a)`. Rewrite using `[LinearMap.mulLeft_apply]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h3]`.

Conclude with `Submodule.add_mem_sup h1 h2`.
-/
theorem rk_add (A : FI E) (s : ℕ) (hA : ConjStable E A) :
    finrank ℤ (eig E A s) + finrank ℤ (eig E A (s + 1)) = finrank ℤ (zsub E A) := by
  have hd : Disjoint (eig E A s) (eig E A (s + 1)) := by
    rw [Submodule.disjoint_def]
    intro t h1 h2
    have e1 := ((mem_eig E A s t).mp h1).2
    have e2 := ((mem_eig E A (s + 1) t).mp h2).2
    rw [pow_succ] at e2
    have : (2 : E) * t = 0 := by linear_combination e1 + e2
    simpa using this
  rw [← finrank_sup E _ _ hd]
  apply le_antisymm
  · exact Submodule.finrank_mono (sup_le inf_le_left inf_le_left)
  · have : Module.Finite ℤ ↥(eig E A s ⊔ eig E A (s + 1)) :=
      finite_of_le E _ A (sup_le inf_le_left inf_le_left)
    refine finrank_le_of_map_le E (LinearMap.mulLeft ℤ (2 : E))
      (mul_right_injective₀ two_ne_zero) _ _ ?_
    rintro _ ⟨a, ha, rfl⟩
    have ha' : a ∈ A := ha
    have hc := sign_mem E A s _ (hA _ ha')
    have h1 : a + (-1) ^ s * complexConj E a ∈ eig E A s := by
      rw [mem_eig]
      refine ⟨A.val.add_mem ha' hc, ?_⟩
      simp only [map_add, map_mul, map_pow, map_neg, map_one, complexConj_apply_apply]
      linear_combination (-a) * sign_sq E s
    have h2 : a - (-1) ^ s * complexConj E a ∈ eig E A (s + 1) := by
      rw [mem_eig]
      refine ⟨A.val.sub_mem ha' hc, ?_⟩
      simp only [map_sub, map_mul, map_pow, map_neg, map_one, complexConj_apply_apply, pow_succ]
      linear_combination (-a) * sign_sq E s
    have h3 : LinearMap.mulLeft ℤ (2 : E) a
        = (a + (-1) ^ s * complexConj E a) + (a - (-1) ^ s * complexConj E a) := by
      rw [LinearMap.mulLeft_apply]; ring
    rw [h3]
    exact Submodule.add_mem_sup h1 h2

/- English proof (translation)
Establish `h1` using `rk_add E A s hA`. Rewrite `h1` using `[rk_succ, finrank_zsub E A hA0]`. Establish `h2 : finrank (maximalRealSubfield E) E = 2` using `Algebra.IsQuadraticExtension.finrank_eq_two _ _`. Establish `h3` using `finrank_mul_finrank ℚ (maximalRealSubfield E) E`. Rewrite `h3` using `[h2]`.

Unfold `deg`. Use linear arithmetic over natural numbers and integers.
-/
theorem rk_eq (A : FI E) (s : ℕ) (hA0 : A ≠ 0) (hA : ConjStable E A) :
    finrank ℤ (eig E A s) = deg E := by
  have h1 := rk_add E A s hA
  rw [rk_succ, finrank_zsub E A hA0] at h1
  have h2 : finrank (maximalRealSubfield E) E = 2 :=
    Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have h3 := finrank_mul_finrank ℚ (maximalRealSubfield E) E
  rw [h2] at h3
  unfold deg
  omega

end Ranks

section Index

variable (E : Type) [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[AddSubgroup.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Take `⟨a, ha, rfl⟩` from `(mem_gA E A g x).mp hx`.

Conclude with `⟨a, ha, by simp⟩`. Introduce and unpack `⟨a, ha, rfl⟩`. Conclude with `(mem_gA E A g _).mpr ⟨a, ha, by simp⟩`.
-/
theorem gA_eq_map (A : FI E) (g : ℕ) :
    (zsub E (A * FractionalIdeal.spanSingleton _ (g : E))).toAddSubgroup
      = (zsub E A).toAddSubgroup.map (nsmulAddMonoidHom (α := E) g) := by
  ext x
  rw [AddSubgroup.mem_map]
  constructor
  · intro hx
    obtain ⟨a, ha, rfl⟩ := (mem_gA E A g x).mp hx
    exact ⟨a, ha, by simp⟩
  · rintro ⟨a, ha, rfl⟩
    exact (mem_gA E A g _).mpr ⟨a, ha, by simp⟩

/- English proof (translation)
Establish `hg' : (g : E) ≠ 0` using `by exact_mod_cast hg.ne'`. Use extensionality with `x`. Rewrite using `[AddSubgroup.mem_map, AddSubgroup.mem_inf]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hx1, hx2⟩`.

Take `⟨a, ha, rfl⟩` from `(mem_gA E A g x).mp hx1`. Take `⟨-, h2⟩` from `(mem_eig E A s _).mp hx2`. Use `⟨a, (mem_eig E A s a).mpr ⟨ha, ?_⟩, by simp⟩` and prove the remaining obligations. Rewrite `h2` using `[map_mul, map_natCast]`. Apply `mul_left_cancel₀ hg'` to reduce the goal to its premises.

Take the linear combination `h2`. Introduce and unpack `⟨a, ha, rfl⟩`. Take `⟨h1, h2⟩` from `(mem_eig E A s a).mp ha`. Establish `e : nsmulAddMonoidHom (α` using `E) g a = (g : E) * a := by simp`. Rewrite using `[e]`.

Use `⟨(mem_gA E A g _).mpr ⟨a, h1, rfl⟩, (mem_eig E A s _).mpr ⟨?_, ?_⟩⟩` and prove the remaining obligations. Conclude with `gA_le E A g _ ((mem_gA E A g _).mpr ⟨a, h1, rfl⟩)`. Rewrite using `[map_mul, map_natCast]`. Take the linear combination `(g : E) * h2`.
-/
theorem inf_eq_map (A : FI E) (g s : ℕ) (hg : 0 < g) :
    (zsub E (A * FractionalIdeal.spanSingleton _ (g : E))).toAddSubgroup ⊓
        (eig E A s).toAddSubgroup
      = (eig E A s).toAddSubgroup.map (nsmulAddMonoidHom (α := E) g) := by
  have hg' : (g : E) ≠ 0 := by exact_mod_cast hg.ne'
  ext x
  rw [AddSubgroup.mem_map, AddSubgroup.mem_inf]
  constructor
  · rintro ⟨hx1, hx2⟩
    obtain ⟨a, ha, rfl⟩ := (mem_gA E A g x).mp hx1
    obtain ⟨-, h2⟩ := (mem_eig E A s _).mp hx2
    refine ⟨a, (mem_eig E A s a).mpr ⟨ha, ?_⟩, by simp⟩
    rw [map_mul, map_natCast] at h2
    apply mul_left_cancel₀ hg'
    linear_combination h2
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨h1, h2⟩ := (mem_eig E A s a).mp ha
    have e : nsmulAddMonoidHom (α := E) g a = (g : E) * a := by simp
    rw [e]
    refine ⟨(mem_gA E A g _).mpr ⟨a, h1, rfl⟩, (mem_eig E A s _).mpr ⟨?_, ?_⟩⟩
    · exact gA_le E A g _ ((mem_gA E A g _).mpr ⟨a, h1, rfl⟩)
    · rw [map_mul, map_natCast]
      linear_combination (g : E) * h2

end Index

end Formalism.FourierDecayAlt.P.S6x3

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.S6 Formalism.FourierDecayAlt.P.S6x3
open NumberField NumberField.IsCMField Module
open scoped nonZeroDivisors

/- English proof (translation)
Introduce `E _ _ _ A g s hA0 hA hg hU`. Establish `h2 : idx E (zsub E (A * FractionalIdeal.spanSingleton _ (g : E))) (twLat E A (A * FractionalIdeal.spanSingleton _ (g : E)) s) = g ^ deg E`. Unfold `idx`. Rewrite using `[tw_eq E A g s hA hg hU, Submodule.sup_toAddSubgroup, AddSubgroup.relIndex_sup_right, ← AddSubgroup.inf_relIndex_right, inf_eq_map E A g s hg, relIndex_nsmul, rk_eq E A s hA0 hA]`. Use `⟨?_, h2⟩` and prove the remaining obligations.

Establish `h3 : idx E (zsub E (A * FractionalIdeal.spanSingleton _ (g : E))) (zsub E A) = g ^ deg E * g ^ deg E`. Unfold `idx`. Rewrite using `[gA_eq_map, relIndex_nsmul, ← rk_add E A s hA, rk_succ, rk_eq E A s hA0 hA, pow_add]`. Establish `hle1 : (zsub E (A * FractionalIdeal.spanSingleton _ (g : E))).toAddSubgroup ≤ (twLat E A (A * FractionalIdeal.spanSingleton _ (g : E)) s).toAddSubgroup`. Rewrite using `[tw_eq E A g s hA hg hU]`.

Conclude with `Submodule.toAddSubgroup_mono le_sup_right`. Establish `hle2 : (twLat E A (A * FractionalIdeal.spanSingleton _ (g : E)) s).toAddSubgroup ≤ (zsub E A).toAddSubgroup` using `Submodule.toAddSubgroup_mono inf_le_left`. Establish `h4` using `AddSubgroup.relIndex_mul_relIndex _ _ _ hle1 hle2`. Unfold `idx at h2 h3 ⊢`. Rewrite `h4` using `[h2, h3]`.

Conclude with `Nat.eq_of_mul_eq_mul_left (pow_pos hg _) h4`.
-/
theorem twistedLatticeIndex : Formalism.FourierDecayAlt.S6.IndexCore := by
  intro E _ _ _ A g s hA0 hA hg hU
  have h2 : idx E (zsub E (A * FractionalIdeal.spanSingleton _ (g : E)))
      (twLat E A (A * FractionalIdeal.spanSingleton _ (g : E)) s) = g ^ deg E := by
    unfold idx
    rw [tw_eq E A g s hA hg hU, Submodule.sup_toAddSubgroup, AddSubgroup.relIndex_sup_right,
      ← AddSubgroup.inf_relIndex_right, inf_eq_map E A g s hg, relIndex_nsmul, rk_eq E A s hA0 hA]
  refine ⟨?_, h2⟩
  have h3 : idx E (zsub E (A * FractionalIdeal.spanSingleton _ (g : E))) (zsub E A)
      = g ^ deg E * g ^ deg E := by
    unfold idx
    rw [gA_eq_map, relIndex_nsmul, ← rk_add E A s hA, rk_succ, rk_eq E A s hA0 hA, pow_add]
  have hle1 : (zsub E (A * FractionalIdeal.spanSingleton _ (g : E))).toAddSubgroup ≤
      (twLat E A (A * FractionalIdeal.spanSingleton _ (g : E)) s).toAddSubgroup := by
    rw [tw_eq E A g s hA hg hU]
    exact Submodule.toAddSubgroup_mono le_sup_right
  have hle2 : (twLat E A (A * FractionalIdeal.spanSingleton _ (g : E)) s).toAddSubgroup ≤
      (zsub E A).toAddSubgroup := Submodule.toAddSubgroup_mono inf_le_left
  have h4 := AddSubgroup.relIndex_mul_relIndex _ _ _ hle1 hle2
  unfold idx at h2 h3 ⊢
  rw [h2, h3] at h4
  exact Nat.eq_of_mul_eq_mul_left (pow_pos hg _) h4

end Formalism.FourierDecayAlt.P
