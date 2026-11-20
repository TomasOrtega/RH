import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.WeightedHomogeneousComponentMemElimIdeal

open MvPolynomial

noncomputable section

namespace GlobalTheory.Chow

/- English proof (translation)
Set `φ : MvPolynomial σ K →+* F` to `(aeval ξ : MvPolynomial σ K →ₐ[K] F).toRingHom`. Establish `hφ : (fun j => φ (X j)) = ξ` using `by ext j; simp [φ]`. Distinguish the cases in `hj : ξ j = 0`. Conclude with `⟨1, Ideal.mul_mem_left _ _ (C_mem_incidenceIdeal (by`. Rewrite using `[pow_one, ← hξ, aeval_X, hj]))⟩`.

Take `⟨m, g, hg⟩` from `exists_pow_mul_sub_rename_mem (X : σ → MvPolynomial σ K) j h`. Use `⟨m, ?_⟩` and prove the remaining obligations. Establish `h1` using `map_mem_span_linForm φ hg`. Rewrite `h1` using `[hφ, map_sub, map_mul, map_rename]`. Establish `h2 : rename Subtype.val (map φ g) ∈ Ideal.span (Set.range (linForm ξ : β → _))`.

Use `Ideal.sub_mem _ (Ideal.mul_mem_right (map φ (C (X j ^ m))) _ hf) h1` as an intermediate fact. Rewrite `this` using `[sub_sub_cancel]`. Then use the resulting hypothesis. Rewrite `h2` using `[← Set.image_univ, ← ker_linFormElim ξ (Ne.isUnit hj), RingHom.mem_ker, linFormElim_rename, ← RingHom.mem_ker, MvPolynomial.ker_map]`. Establish `hker : RingHom.ker φ = p` using `Ideal.ext fun g => hξ g`. Rewrite `h2` using `[hker]`.

Establish `h3 : rename Subtype.val g ∈ p.map (C : _ →+* MvPolynomial (β × σ) (MvPolynomial σ K))`. Rewrite using `[← Ideal.mem_comap (f := (rename Subtype.val : _ →ₐ[MvPolynomial σ K] _))]`. Use `Ideal.map_le_iff_le_comap.2 (fun a ha => ?_) h2` and prove the remaining obligations. Simplify `Ideal.mem_map_of_mem _ ha` using `[Ideal.mem_comap]`. Use `Ideal.add_mem _ (Ideal.mem_sup_right (S := p.map C) hg) (Ideal.mem_sup_left h3)` as an intermediate fact.

Rewrite `this` using `[sub_add_cancel]`. Then use the resulting hypothesis.
-/
theorem exists_mul_pow_mem_incidenceIdeal_of_generic {σ β K F : Type*} [Fintype σ] [CommRing K]
    [Field F] [Algebra K F]
    {p : Ideal (MvPolynomial σ K)} {ξ : σ → F} (hξ : ∀ g, aeval ξ g = 0 ↔ g ∈ p)
    {h : MvPolynomial (β × σ) (MvPolynomial σ K)}
    (hf : map (aeval ξ : MvPolynomial σ K →ₐ[K] F).toRingHom h ∈
      Ideal.span (Set.range (linForm ξ : β → _))) (j : σ) :
    ∃ m : ℕ, h * C (X j ^ m) ∈ incidenceIdeal β p := by
  let φ : MvPolynomial σ K →+* F := (aeval ξ : MvPolynomial σ K →ₐ[K] F).toRingHom
  have hφ : (fun j => φ (X j)) = ξ := by ext j; simp [φ]
  by_cases hj : ξ j = 0
  · exact ⟨1, Ideal.mul_mem_left _ _ (C_mem_incidenceIdeal (by
      rw [pow_one, ← hξ, aeval_X, hj]))⟩
  obtain ⟨m, g, hg⟩ := exists_pow_mul_sub_rename_mem (X : σ → MvPolynomial σ K) j h
  refine ⟨m, ?_⟩
  have h1 := map_mem_span_linForm φ hg
  rw [hφ, map_sub, map_mul, map_rename] at h1
  have h2 : rename Subtype.val (map φ g) ∈ Ideal.span (Set.range (linForm ξ : β → _)) := by
    have := Ideal.sub_mem _ (Ideal.mul_mem_right (map φ (C (X j ^ m))) _ hf) h1
    rwa [sub_sub_cancel] at this
  rw [← Set.image_univ, ← ker_linFormElim ξ (Ne.isUnit hj), RingHom.mem_ker,
    linFormElim_rename, ← RingHom.mem_ker, MvPolynomial.ker_map] at h2
  have hker : RingHom.ker φ = p := Ideal.ext fun g => hξ g
  rw [hker] at h2
  have h3 : rename Subtype.val g ∈ p.map (C : _ →+* MvPolynomial (β × σ) (MvPolynomial σ K)) := by
    rw [← Ideal.mem_comap (f := (rename Subtype.val : _ →ₐ[MvPolynomial σ K] _))]
    refine Ideal.map_le_iff_le_comap.2 (fun a ha => ?_) h2
    simpa [Ideal.mem_comap] using Ideal.mem_map_of_mem _ ha
  have := Ideal.add_mem _ (Ideal.mem_sup_right (S := p.map C) hg) (Ideal.mem_sup_left h3)
  rwa [sub_add_cancel] at this

/- English proof (translation)
Assemble the required witnesses or components as `⟨FractionRing (MvPolynomial σ K ⧸ p), inferInstance, inferInstance, genericPoint p, aeval_genericPoint_eq_zero_iff p, genericPoint_ne_zero hp⟩`.
-/
theorem exists_field_generic_point {σ K : Type} [CommRing K] {p : Ideal (MvPolynomial σ K)}
    [p.IsPrime] (hp : ∃ j, X j ∉ p) :
    ∃ (F : Type) (_ : Field F) (_ : Algebra K F) (ξ : σ → F),
      (∀ g, aeval ξ g = 0 ↔ g ∈ p) ∧ ξ ≠ 0 :=
  ⟨FractionRing (MvPolynomial σ K ⧸ p), inferInstance, inferInstance, genericPoint p,
    aeval_genericPoint_eq_zero_iff p, genericPoint_ne_zero hp⟩

/- English proof (translation)
Apply `map_injective (algebraMap K (AlgebraicClosure K)) (algebraMap K _).injective` to reduce the goal to its premises. Rewrite using `[map_zero]`. Apply `MvPolynomial.funext` to reduce the goal to its premises. Introduce `t`. Take `⟨y, hy, hyP, hs⟩` from `hP (fun j => t ((), j))`.

Use `aeval_eq_zero_of_mem_elimIdeal (β := Unit) hyP hy (t := t) (fun _ => hs) hf` as an intermediate fact. Rewrite using `[map_zero, eval_map, ← aeval_def, this]`.
-/
theorem eq_zero_of_mem_elimIdeal_of_forall_meets {K : Type} [Field K] {N : ℕ}
    {P : Ideal (MvPolynomial (Fin N) K)}
    (hP : ∀ u : Fin N → AlgebraicClosure K, ∃ y : Fin N → AlgebraicClosure K,
      y ≠ 0 ∧ (∀ g ∈ P, aeval y g = 0) ∧ ∑ j, u j * y j = 0)
    {f : MvPolynomial (Unit × Fin N) K} (hf : f ∈ elimIdeal Unit P) : f = 0 := by
  apply map_injective (algebraMap K (AlgebraicClosure K)) (algebraMap K _).injective
  rw [map_zero]
  apply MvPolynomial.funext
  intro t
  obtain ⟨y, hy, hyP, hs⟩ := hP (fun j => t ((), j))
  have := aeval_eq_zero_of_mem_elimIdeal (β := Unit) hyP hy (t := t) (fun _ => hs) hf
  rw [map_zero, eval_map, ← aeval_def, this]

/- English proof (translation)
Establish `hex : ∃ j, X j ∉ P`. Take `⟨y, hy, hyP, -⟩` from `hP 0`. Take `⟨j, hj⟩` from `Function.ne_iff.1 hy`. Conclude with `⟨j, fun h => hj (by simpa using hyP _ h)⟩`. Take `⟨F, _, _, ξ, hξ, hne⟩ : ∃ (F : Type) (_ : Field F) (_ : Algebra K F) (ξ : Fin N → F), (∀ g, aeval ξ g = 0 ↔ g ∈ P) ∧ ξ ≠ 0` from `exists_field_generic_point hex`.

Take `⟨j₀, hj₀⟩` from `Function.ne_iff.1 hne`. Establish `hq` using `isPrime_span_linForm (ι := Unit) ξ (Ne.isUnit hj₀) Set.univ`. Rewrite `hq` using `[Set.image_univ]`. Use `set q : Ideal (MvPolynomial (Unit × Fin N) F) := Ideal.span (Set.range (linForm ξ : Unit → _)) with hqdef`. Choose the witnesses or unpack the hypotheses as in `⟨Ω, _, π, hπ⟩ : ∃ (Ω : Type) (_ : Field Ω) (π : MvPolynomial (Unit × Fin N) F →+* Ω), ∀ a, π a = 0 ↔ a ∈ q := by`.

Use `⟨FractionRing (MvPolynomial (Unit × Fin N) F ⧸ q), inferInstance, (algebraMap (MvPolynomial (Unit × Fin N) F ⧸ q) _).comp (Ideal.Quotient.mk q), fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[RingHom.comp_apply, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]`. Set `ρ : MvPolynomial (Fin N) K →+* MvPolynomial (Unit × Fin N) K` to `(rename (fun j => ((), j)) : _ →ₐ[K] _).toRingHom`. Set `θ : MvPolynomial (Fin N) K →+* Ω` to `π.comp ((map (algebraMap K F)).comp ρ)`. Establish `hθ : Function.Injective θ`.

Rewrite using `[injective_iff_map_eq_zero]`. Introduce `a ha`. Establish `h1 : ρ a ∈ elimIdeal Unit P` using `(mem_elimIdeal_iff_of_generic hξ hne).2 ((hπ _).1 ha)`. Establish `h2` using `eq_zero_of_mem_elimIdeal_of_forall_meets hP h1`. Apply `rename_injective (fun j : Fin N => ((), j)) (fun _ _ h => (Prod.ext_iff.1 h).2)` to reduce the goal to its premises.

Rewrite using `[map_zero]`. Conclude with `h2`. Set `θL : L →+* Ω` to `IsFractionRing.lift hθ`. Establish `hθL (a) : θL (algebraMap _ L a) = θ a` using `IsFractionRing.lift_algebraMap hθ a`. Establish `hθK (a : K) : θL (algebraMap K L a) = π (C (algebraMap K F a))`.

Rewrite using `[IsScalarTower.algebraMap_apply K (MvPolynomial (Fin N) K) L, hθL]`. Simplify using `[θ, ρ]`. Set `ev : MvPolynomial (Fin N) L →+* Ω` to `eval₂Hom θL (fun j => π (C (ξ j)))`. Set `Ψ : MvPolynomial (Unit × Fin N) (MvPolynomial (Fin N) K) →+* MvPolynomial (Fin N) L` to `eval₂Hom (map (algebraMap K L)) (fun v => C (algebraMap (MvPolynomial (Fin N) K) L (X v.2)))`. Set `φ : MvPolynomial (Fin N) K →+* F` to `(aeval ξ : MvPolynomial (Fin N) K →ₐ[K] F).toRingHom`.

Establish `hcomp : ev.comp Ψ = π.comp (map φ)`. Use extensionality with `a`. Simplify using `[ev, Ψ, φ, hθK]`. Simplify using `[ev, Ψ, φ]`. Simplify using `[ev, Ψ, φ, hθL, θ, ρ]`.

Establish `hcomp' (h) : ev (Ψ h) = π (map φ h)` using `DFunLike.congr_fun hcomp h`. Establish `hΨC (a) : Ψ (C a) = map (algebraMap K L) a` using `by simp [Ψ]`. Establish `hΨL : Ψ (genericForm K (Fin N) ()) = ∑ j : Fin N, C (algebraMap (MvPolynomial (Fin N) K) L (X j)) * X j`. Rewrite using `[genericForm_eq, map_sum]`. Conclude with `Finset.sum_congr rfl fun j _ => by simp [Ψ, mul_comm]`.

Establish `hΨc (c : MvPolynomial (Fin N) K) : Ψ (map C (ρ c)) = C (algebraMap _ L c)`. Establish `: Ψ.comp ((map C).comp ρ) = C.comp (algebraMap _ L)`. Use extensionality with `a`. Simplify using `[Ψ, ρ, IsScalarTower.algebraMap_apply K (MvPolynomial (Fin N) K) L]`. Simplify using `[Ψ, ρ]`.

Conclude with `DFunLike.congr_fun this c`. Establish `hden (g : MvPolynomial (Fin N) L) : ∃ c : MvPolynomial (Fin N) K, c ≠ 0 ∧ ∃ h, Ψ h = C (algebraMap _ L c) * g`. Proceed by induction on `g using MvPolynomial.induction_on with`. Consider the case `C a`. Take `⟨x, y, hy, rfl⟩` from `IsFractionRing.div_surjective (A := MvPolynomial (Fin N) K) a`.

Establish `hy0 : y ≠ 0` using `nonZeroDivisors.ne_zero hy`. Use `⟨y, hy0, map C (ρ x), ?_⟩` and prove the remaining obligations. Establish `: algebraMap _ L y ≠ 0`. Simplify using `using hy0`. Rewrite using `[hΨc, ← C_mul, mul_div_cancel₀ _ this]`.

Consider the case `add f g hf hg`. Take `⟨c, hc, h, hh⟩` from `hf`. Take `⟨d, hd, k, hk⟩` from `hg`. Use `⟨c * d, mul_ne_zero hc hd, map C (ρ d) * h + map C (ρ c) * k, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, map_mul, map_mul, hΨc, hΨc, hh, hk, map_mul, map_mul]`.

Expand and normalize the polynomial expressions, which then agree. Consider the case `mul_X f v hf`. Take `⟨c, hc, h, hh⟩` from `hf`. Use `⟨c, hc, h * C (X v), ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, hh, hΨC, map_X, mul_assoc]`.

Use `⟨RingHom.ker ev, RingHom.ker_isPrime ev, ?_, ?_⟩` and prove the remaining obligations. Use `sup_le (Ideal.map_le_iff_le_comap.2 fun g hg => ?_) ?_` and prove the remaining obligations. Rewrite using `[Ideal.mem_comap, RingHom.mem_ker, ← hΨC, hcomp', map_C]`. Establish `: φ g = 0` using `(hξ g).2 hg`. Rewrite using `[this, map_zero, map_zero]`.

Rewrite using `[Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, ← hΨL, hcomp', hπ, genericForm, map_linForm]`. Establish `hφ : (fun j => φ (X j)) = ξ` using `by ext j; simp [φ]`. Rewrite using `[hφ]`. Conclude with `Ideal.subset_span ⟨(), rfl⟩`. Introduce `g hg j`.

Take `⟨c, hc, h, hh⟩` from `hden g`. Establish `h1 : map φ h ∈ q`. Rewrite using `[← hπ, ← hcomp', hh, map_mul, (RingHom.mem_ker.1 hg), mul_zero]`. Take `⟨m, hm⟩` from `exists_mul_pow_mem_incidenceIdeal_of_generic hξ h1 j`. Use `⟨m, ?_⟩` and prove the remaining obligations.

Establish `hle : incidenceIdeal Unit P ≤ Ideal.comap Ψ (P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L) ⊔ Ideal.span {(∑ j : Fin N, C (algebraMap (MvPolynomial (Fin N) K) L (X j)) * X j : MvPolynomial (Fin N) L)})`. Use `incidenceIdeal_le.2 ⟨fun a ha => ?_, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[Ideal.mem_comap, hΨC]`. Conclude with `Ideal.mem_sup_left (Ideal.mem_map_of_mem _ ha)`. Rewrite using `[Ideal.mem_comap, hΨL]`.

Conclude with `Ideal.mem_sup_right (Ideal.subset_span rfl)`. Establish `h2` using `hle hm`. Rewrite `h2` using `[Ideal.mem_comap, map_mul, hh, hΨC, map_pow, map_X]`. Establish `hcL : algebraMap _ L c ≠ 0` using `by simpa using hc`. Establish `h3` using `Ideal.mul_mem_left _ (C (algebraMap _ L c)⁻¹) h2`.

Use `h3 using 1` and compare the differences between its conclusion and the goal. Rewrite using `[mul_assoc, ← mul_assoc (C _) (C _), ← C_mul, inv_mul_cancel₀ hcL, C_1, one_mul, mul_comm]`.
-/
theorem exists_prime_saturation_generic_section (K L : Type) [Field K] [Field L] (N : ℕ)
    [Algebra K L] [Algebra (MvPolynomial (Fin N) K) L]
    [IsScalarTower K (MvPolynomial (Fin N) K) L] [IsFractionRing (MvPolynomial (Fin N) K) L]
    (P : Ideal (MvPolynomial (Fin N) K)) (hprime : P.IsPrime)
    (hP : ∀ u : Fin N → AlgebraicClosure K, ∃ y : Fin N → AlgebraicClosure K,
      y ≠ 0 ∧ (∀ g ∈ P, aeval y g = 0) ∧ ∑ j, u j * y j = 0) :
    ∃ Q : Ideal (MvPolynomial (Fin N) L), Q.IsPrime ∧
      P.map (MvPolynomial.map (algebraMap K L) :
          MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L) ⊔
        Ideal.span {(∑ j : Fin N, C (algebraMap (MvPolynomial (Fin N) K) L (X j)) * X j :
          MvPolynomial (Fin N) L)} ≤ Q ∧
      ∀ g ∈ Q, ∀ j, ∃ m : ℕ, X j ^ m * g ∈
        P.map (MvPolynomial.map (algebraMap K L) :
          MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L) ⊔
        Ideal.span {(∑ j : Fin N, C (algebraMap (MvPolynomial (Fin N) K) L (X j)) * X j :
          MvPolynomial (Fin N) L)} := by
  classical
  have hex : ∃ j, X j ∉ P := by
    obtain ⟨y, hy, hyP, -⟩ := hP 0
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hy
    exact ⟨j, fun h => hj (by simpa using hyP _ h)⟩
  obtain ⟨F, _, _, ξ, hξ, hne⟩ : ∃ (F : Type) (_ : Field F) (_ : Algebra K F) (ξ : Fin N → F),
      (∀ g, aeval ξ g = 0 ↔ g ∈ P) ∧ ξ ≠ 0 :=
    exists_field_generic_point hex
  obtain ⟨j₀, hj₀⟩ := Function.ne_iff.1 hne
  have hq := isPrime_span_linForm (ι := Unit) ξ (Ne.isUnit hj₀) Set.univ
  rw [Set.image_univ] at hq
  set q : Ideal (MvPolynomial (Unit × Fin N) F) :=
    Ideal.span (Set.range (linForm ξ : Unit → _)) with hqdef
  obtain ⟨Ω, _, π, hπ⟩ : ∃ (Ω : Type) (_ : Field Ω) (π : MvPolynomial (Unit × Fin N) F →+* Ω),
      ∀ a, π a = 0 ↔ a ∈ q := by
    refine ⟨FractionRing (MvPolynomial (Unit × Fin N) F ⧸ q), inferInstance,
      (algebraMap (MvPolynomial (Unit × Fin N) F ⧸ q) _).comp (Ideal.Quotient.mk q), fun a => ?_⟩
    rw [RingHom.comp_apply, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
  let ρ : MvPolynomial (Fin N) K →+* MvPolynomial (Unit × Fin N) K :=
    (rename (fun j => ((), j)) : _ →ₐ[K] _).toRingHom
  let θ : MvPolynomial (Fin N) K →+* Ω := π.comp ((map (algebraMap K F)).comp ρ)
  have hθ : Function.Injective θ := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have h1 : ρ a ∈ elimIdeal Unit P :=
      (mem_elimIdeal_iff_of_generic hξ hne).2 ((hπ _).1 ha)
    have h2 := eq_zero_of_mem_elimIdeal_of_forall_meets hP h1
    apply rename_injective (fun j : Fin N => ((), j)) (fun _ _ h => (Prod.ext_iff.1 h).2)
    rw [map_zero]
    exact h2
  let θL : L →+* Ω := IsFractionRing.lift hθ
  have hθL (a) : θL (algebraMap _ L a) = θ a := IsFractionRing.lift_algebraMap hθ a
  have hθK (a : K) : θL (algebraMap K L a) = π (C (algebraMap K F a)) := by
    rw [IsScalarTower.algebraMap_apply K (MvPolynomial (Fin N) K) L, hθL]
    simp [θ, ρ]
  let ev : MvPolynomial (Fin N) L →+* Ω := eval₂Hom θL (fun j => π (C (ξ j)))
  let Ψ : MvPolynomial (Unit × Fin N) (MvPolynomial (Fin N) K) →+* MvPolynomial (Fin N) L :=
    eval₂Hom (map (algebraMap K L))
      (fun v => C (algebraMap (MvPolynomial (Fin N) K) L (X v.2)))
  let φ : MvPolynomial (Fin N) K →+* F := (aeval ξ : MvPolynomial (Fin N) K →ₐ[K] F).toRingHom
  have hcomp : ev.comp Ψ = π.comp (map φ) := by
    ext a
    · simp [ev, Ψ, φ, hθK]
    · simp [ev, Ψ, φ]
    · simp [ev, Ψ, φ, hθL, θ, ρ]
  have hcomp' (h) : ev (Ψ h) = π (map φ h) := DFunLike.congr_fun hcomp h
  have hΨC (a) : Ψ (C a) = map (algebraMap K L) a := by simp [Ψ]
  have hΨL : Ψ (genericForm K (Fin N) ()) =
      ∑ j : Fin N, C (algebraMap (MvPolynomial (Fin N) K) L (X j)) * X j := by
    rw [genericForm_eq, map_sum]
    exact Finset.sum_congr rfl fun j _ => by simp [Ψ, mul_comm]
  have hΨc (c : MvPolynomial (Fin N) K) : Ψ (map C (ρ c)) = C (algebraMap _ L c) := by
    have : Ψ.comp ((map C).comp ρ) = C.comp (algebraMap _ L) := by
      ext a
      · simp [Ψ, ρ, IsScalarTower.algebraMap_apply K (MvPolynomial (Fin N) K) L]
      · simp [Ψ, ρ]
    exact DFunLike.congr_fun this c
  have hden (g : MvPolynomial (Fin N) L) : ∃ c : MvPolynomial (Fin N) K, c ≠ 0 ∧
      ∃ h, Ψ h = C (algebraMap _ L c) * g := by
    induction g using MvPolynomial.induction_on with
    | C a =>
      obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial (Fin N) K) a
      have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
      refine ⟨y, hy0, map C (ρ x), ?_⟩
      have : algebraMap _ L y ≠ 0 := by
        simpa using hy0
      rw [hΨc, ← C_mul, mul_div_cancel₀ _ this]
    | add f g hf hg =>
      obtain ⟨c, hc, h, hh⟩ := hf
      obtain ⟨d, hd, k, hk⟩ := hg
      refine ⟨c * d, mul_ne_zero hc hd, map C (ρ d) * h + map C (ρ c) * k, ?_⟩
      rw [map_add, map_mul, map_mul, hΨc, hΨc, hh, hk, map_mul, map_mul]
      ring
    | mul_X f v hf =>
      obtain ⟨c, hc, h, hh⟩ := hf
      refine ⟨c, hc, h * C (X v), ?_⟩
      rw [map_mul, hh, hΨC, map_X, mul_assoc]
  refine ⟨RingHom.ker ev, RingHom.ker_isPrime ev, ?_, ?_⟩
  · refine sup_le (Ideal.map_le_iff_le_comap.2 fun g hg => ?_) ?_
    · rw [Ideal.mem_comap, RingHom.mem_ker, ← hΨC, hcomp', map_C]
      have : φ g = 0 := (hξ g).2 hg
      rw [this, map_zero, map_zero]
    · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, ← hΨL,
        hcomp', hπ, genericForm, map_linForm]
      have hφ : (fun j => φ (X j)) = ξ := by ext j; simp [φ]
      rw [hφ]
      exact Ideal.subset_span ⟨(), rfl⟩
  · intro g hg j
    obtain ⟨c, hc, h, hh⟩ := hden g
    have h1 : map φ h ∈ q := by
      rw [← hπ, ← hcomp', hh, map_mul, (RingHom.mem_ker.1 hg), mul_zero]
    obtain ⟨m, hm⟩ := exists_mul_pow_mem_incidenceIdeal_of_generic hξ h1 j
    refine ⟨m, ?_⟩
    have hle : incidenceIdeal Unit P ≤ Ideal.comap Ψ
        (P.map (MvPolynomial.map (algebraMap K L) :
          MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L) ⊔
        Ideal.span {(∑ j : Fin N, C (algebraMap (MvPolynomial (Fin N) K) L (X j)) * X j :
          MvPolynomial (Fin N) L)}) := by
      refine incidenceIdeal_le.2 ⟨fun a ha => ?_, fun i => ?_⟩
      · rw [Ideal.mem_comap, hΨC]
        exact Ideal.mem_sup_left (Ideal.mem_map_of_mem _ ha)
      · rw [Ideal.mem_comap, hΨL]
        exact Ideal.mem_sup_right (Ideal.subset_span rfl)
    have h2 := hle hm
    rw [Ideal.mem_comap, map_mul, hh, hΨC, map_pow, map_X] at h2
    have hcL : algebraMap _ L c ≠ 0 := by simpa using hc
    have h3 := Ideal.mul_mem_left _ (C (algebraMap _ L c)⁻¹) h2
    convert h3 using 1
    rw [mul_assoc, ← mul_assoc (C _) (C _), ← C_mul, inv_mul_cancel₀ hcL, C_1, one_mul, mul_comm]

end GlobalTheory.Chow
