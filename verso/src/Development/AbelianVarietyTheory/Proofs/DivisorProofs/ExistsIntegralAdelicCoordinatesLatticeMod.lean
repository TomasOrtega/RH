import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorResIEqResS
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicElementLatticeFullAndCompletion
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionRationalPointsAndApproximation

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GeoActCompare

open scoped TensorProduct Matrix nonZeroDivisors

section Core

/- English proof (translation)
Set `ρ : La →+ (Fin n → S)` to `{ toFun := fun a i => ⟨t * φ a i, hN1 _ (hmem a) i⟩ map_zero' := by funext i; apply Subtype.ext; simp map_add' := fun a b => by funext i; apply Subtype.ext; simp [mul_add] }`. Establish `hρ : ∀ a i, (ρ a i : R) = t * φ a i` using `fun _ _ => rfl`. Establish `key : ∀ z ∈ N, ∀ u : Fin n → S, (∀ i, t * z i = M * (u i : R)) → ∃ w ∈ N, z = M • w`. Introduce `z hz u hu`. Use `⟨_, add_mem (hN3 m z hz) (hN2 u), ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `i`. Simplify using `only [Pi.smul_apply, Pi.add_apply, nsmul_eq_mul]`. Take the linear combination `(z i) * h1 + a₀ * hu i`. Establish `hlin : ∀ (b : O) (a : La), ρ (b • a) = o b • ρ a`. Introduce `b a`.

Use function extensionality and compare the values at `i`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hρ, hφ, Pi.smul_apply, smul_eq_mul, Subring.coe_mul, hρ]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨ρ, hlin, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `s`. Take `⟨a, w, hw, h⟩` from `happ _ (hN2 s)`. Use `⟨a, fun i => ⟨t * w i, hN1 w hw i⟩ + o m * s i, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Apply `Subtype.ext` to reduce the goal to its premises.

Use `congrFun h i` as an intermediate fact. Rewrite `this` using `[Pi.add_apply, Pi.smul_apply, nsmul_eq_mul]`. Rewrite using `[Pi.add_apply, Pi.smul_apply, nsmul_eq_mul]`. Simplify using `only [Subring.coe_add, Subring.coe_mul, hρ, Subring.coe_natCast]`. Take the linear combination `(s i : R) * h1 + t * this`.

Introduce `I J hIJ a ha`. Establish `hc : ∀ c ∈ J, ∃ a', c • a = M • a'`. Introduce `c hc`. Establish `h2 : ∀ i, ∃ u : S, ρ (c • a) i = M * u`. Introduce `i`.

Establish `: ρ (c • a) i ∈ (I * J).map o`. Rewrite using `[hlin, Ideal.map_mul, Pi.smul_apply, smul_eq_mul, mul_comm (o c)]`. Conclude with `Ideal.mul_mem_mul (ha i) (Ideal.mem_map_of_mem _ hc)`. Rewrite `this` using `[hIJ, Ideal.map_span, Set.image_singleton, map_natCast, Ideal.mem_span_singleton]`. Conclude with `this`.

Use `choose u hu using h2`. Take `⟨w, hw, h⟩` from `key _ (hmem (c • a)) u (fun i => by`. Rewrite using `[← hρ, hu i, Subring.coe_mul, Subring.coe_natCast])`. Conclude with `hrat _ w hw h`. Establish `h3 : ∀ x ∈ I * J, ∃ a' ∈ I • (⊤ : Submodule O La), x • a = M • a'`.

Introduce `x hx`. Use `Submodule.mul_induction_on hx ?_ ?_` and prove the remaining obligations. Introduce `b hb c hc'`. Take `⟨a', h⟩` from `hc c hc'`. Conclude with `⟨b • a', Submodule.smul_mem_smul hb trivial, by rw [mul_smul, h, smul_comm]⟩`.

Introduce and unpack `x y ⟨a1, h1, e1⟩ ⟨a2, h2, e2⟩`. Conclude with `⟨a1 + a2, add_mem h1 h2, by rw [add_smul, e1, e2, smul_add]⟩`. Take `⟨a', ha', e⟩` from `h3 M (by rw [hIJ]; exact Ideal.mem_span_singleton_self _)`. Rewrite `e` using `[Nat.cast_smul_eq_nsmul]`. Establish `: a = a'`.

Apply `hinj` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Rewrite using `[← sub_eq_zero]`. Apply `hM` to reduce the goal to its premises. Use `congrFun (congrArg φ e) i` as an intermediate fact.

Rewrite `this` using `[map_nsmul, map_nsmul]`. Rewrite using `[smul_sub]`. Conclude with `sub_eq_zero.2 this`. Rewrite using `[this]`. Conclude with `ha'`.

Introduce `y a a'`. Establish `hz : (y.map S.subtype) *ᵥ φ a - φ a' ∈ N` using `sub_mem (hN4 y _ (hmem a)) (hmem a')`. Establish `he : ∀ i, ((y *ᵥ ρ a - ρ a') i : R) = t * ((y.map S.subtype) *ᵥ φ a - φ a') i`. Introduce `i`. Simplify using `only [Pi.sub_apply, Matrix.mulVec, dotProduct, Matrix.map_apply, mul_sub, Finset.mul_sum]`.

Use `push_cast`. Simplify using `only [hρ, Subring.coe_subtype]`. Use `congr 1`. Conclude with `Finset.sum_congr rfl fun j _ => by ring`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨w, hw, h⟩`. Use `⟨fun i => ⟨t * w i, hN1 w hw i⟩, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[he, h]`.

Simplify using `only [Pi.smul_apply, nsmul_eq_mul, Subring.coe_mul, Subring.coe_natCast]`. Expand and normalize the polynomial expressions, which then agree. Introduce and unpack `⟨s, h⟩`. Use `key _ hz s fun i => ?_` and prove the remaining obligations. Rewrite using `[← he, h]`.

Simplify using `only [Pi.smul_apply, nsmul_eq_mul, Subring.coe_mul, Subring.coe_natCast]`.
-/
theorem coord_core {O R : Type} [CommRing O] [CommRing R] (S : Subring R) (o : O →+* S) {n : ℕ} (M : ℕ)
    (hM : ∀ x : R, M • x = 0 → x = 0) (t a₀ : R) (m : O) (h1 : (1 : R) = M * (o m : R) + t * a₀)
    (N : AddSubgroup (Fin n → R)) (hN1 : ∀ w ∈ N, ∀ i, t * w i ∈ S)
    (hN2 : ∀ s : Fin n → S, (fun i => a₀ * (s i : R)) ∈ N)
    (hN3 : ∀ (b : O), ∀ w ∈ N, (fun i => (o b : R) * w i) ∈ N)
    (hN4 : ∀ (y : Matrix (Fin n) (Fin n) S), ∀ w ∈ N, (y.map S.subtype) *ᵥ w ∈ N)
    {La : Type} [AddCommGroup La] [Module O La] (φ : La →+ (Fin n → R))
    (hφ : ∀ (b : O) (a : La), φ (b • a) = fun i => (o b : R) * φ a i) (hinj : Function.Injective φ)
    (hmem : ∀ a, φ a ∈ N) (happ : ∀ z ∈ N, ∃ a, ∃ w ∈ N, z = φ a + M • w)
    (hrat : ∀ a, ∀ w ∈ N, φ a = M • w → ∃ a', a = M • a') :
    ∃ ρ : La →+ (Fin n → S), (∀ (b : O) (a : La), ρ (b • a) = o b • ρ a) ∧
      (∀ s : Fin n → S, ∃ (a : La) (s' : Fin n → S), s = ρ a + M • s') ∧
      (∀ I J : Ideal O, I * J = Ideal.span {(M : O)} → ∀ a : La, (∀ i, ρ a i ∈ I.map o) →
        a ∈ I • (⊤ : Submodule O La)) ∧
      ∀ (y : Matrix (Fin n) (Fin n) S) (a a' : La),
        (∃ w ∈ N, (y.map S.subtype) *ᵥ φ a - φ a' = M • w) ↔ ∃ s : Fin n → S, y *ᵥ ρ a - ρ a' = M • s := by
  let ρ : La →+ (Fin n → S) :=
    { toFun := fun a i => ⟨t * φ a i, hN1 _ (hmem a) i⟩
      map_zero' := by funext i; apply Subtype.ext; simp
      map_add' := fun a b => by funext i; apply Subtype.ext; simp [mul_add] }
  have hρ : ∀ a i, (ρ a i : R) = t * φ a i := fun _ _ => rfl
  have key : ∀ z ∈ N, ∀ u : Fin n → S, (∀ i, t * z i = M * (u i : R)) → ∃ w ∈ N, z = M • w := by
    intro z hz u hu
    refine ⟨_, add_mem (hN3 m z hz) (hN2 u), ?_⟩
    funext i
    simp only [Pi.smul_apply, Pi.add_apply, nsmul_eq_mul]
    linear_combination (z i) * h1 + a₀ * hu i
  have hlin : ∀ (b : O) (a : La), ρ (b • a) = o b • ρ a := by
    intro b a
    funext i
    apply Subtype.ext
    rw [hρ, hφ, Pi.smul_apply, smul_eq_mul, Subring.coe_mul, hρ]
    ring
  refine ⟨ρ, hlin, ?_, ?_, ?_⟩
  · intro s
    obtain ⟨a, w, hw, h⟩ := happ _ (hN2 s)
    refine ⟨a, fun i => ⟨t * w i, hN1 w hw i⟩ + o m * s i, ?_⟩
    funext i
    apply Subtype.ext
    have := congrFun h i
    rw [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul] at this
    rw [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul]
    simp only [Subring.coe_add, Subring.coe_mul, hρ,
      Subring.coe_natCast]
    linear_combination (s i : R) * h1 + t * this
  · intro I J hIJ a ha
    have hc : ∀ c ∈ J, ∃ a', c • a = M • a' := by
      intro c hc
      have h2 : ∀ i, ∃ u : S, ρ (c • a) i = M * u := by
        intro i
        have : ρ (c • a) i ∈ (I * J).map o := by
          rw [hlin, Ideal.map_mul, Pi.smul_apply, smul_eq_mul, mul_comm (o c)]
          exact Ideal.mul_mem_mul (ha i) (Ideal.mem_map_of_mem _ hc)
        rw [hIJ, Ideal.map_span, Set.image_singleton, map_natCast, Ideal.mem_span_singleton] at this
        exact this
      choose u hu using h2
      obtain ⟨w, hw, h⟩ := key _ (hmem (c • a)) u (fun i => by
        rw [← hρ, hu i, Subring.coe_mul, Subring.coe_natCast])
      exact hrat _ w hw h
    have h3 : ∀ x ∈ I * J, ∃ a' ∈ I • (⊤ : Submodule O La), x • a = M • a' := by
      intro x hx
      refine Submodule.mul_induction_on hx ?_ ?_
      · intro b hb c hc'
        obtain ⟨a', h⟩ := hc c hc'
        exact ⟨b • a', Submodule.smul_mem_smul hb trivial, by rw [mul_smul, h, smul_comm]⟩
      · rintro x y ⟨a1, h1, e1⟩ ⟨a2, h2, e2⟩
        exact ⟨a1 + a2, add_mem h1 h2, by rw [add_smul, e1, e2, smul_add]⟩
    obtain ⟨a', ha', e⟩ := h3 M (by rw [hIJ]; exact Ideal.mem_span_singleton_self _)
    rw [Nat.cast_smul_eq_nsmul] at e
    have : a = a' := by
      apply hinj
      funext i
      rw [← sub_eq_zero]
      apply hM
      have := congrFun (congrArg φ e) i
      rw [map_nsmul, map_nsmul] at this
      rw [smul_sub]
      exact sub_eq_zero.2 this
    rw [this]
    exact ha'
  · intro y a a'
    have hz : (y.map S.subtype) *ᵥ φ a - φ a' ∈ N := sub_mem (hN4 y _ (hmem a)) (hmem a')
    have he : ∀ i, ((y *ᵥ ρ a - ρ a') i : R) = t * ((y.map S.subtype) *ᵥ φ a - φ a') i := by
      intro i
      simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, Matrix.map_apply, mul_sub, Finset.mul_sum]
      push_cast
      simp only [hρ, Subring.coe_subtype]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by ring
    constructor
    · rintro ⟨w, hw, h⟩
      refine ⟨fun i => ⟨t * w i, hN1 w hw i⟩, ?_⟩
      funext i
      apply Subtype.ext
      rw [he, h]
      simp only [Pi.smul_apply, nsmul_eq_mul, Subring.coe_mul, Subring.coe_natCast]
      ring
    · rintro ⟨s, h⟩
      refine key _ hz s fun i => ?_
      rw [← he, h]
      simp only [Pi.smul_apply, nsmul_eq_mul, Subring.coe_mul, Subring.coe_natCast]

/- English proof (translation)
Establish `hM' : (M : E) ≠ 0` using `by exact_mod_cast hM.ne'`. Establish `hle : FractionalIdeal.spanSingleton (NumberField.RingOfIntegers E)⁰ (M : E) ≤ 1`. Rewrite using `[FractionalIdeal.spanSingleton_le_iff_mem, FractionalIdeal.mem_one_iff]`. Conclude with `⟨M, map_natCast _ _⟩`. Take `⟨t, ht⟩` from `IsDedekindDomain.exists_add_spanSingleton_mul_eq hle (FractionalIdeal.spanSingleton_ne_zero_iff.2 hM') hA`.

Establish `h1 : (1 : E) ∈ (1 : FractionalIdeal (NumberField.RingOfIntegers E)⁰ E)` using `FractionalIdeal.one_mem_one _`. Rewrite `h1` using `[← ht, FractionalIdeal.mem_add]`. Take `⟨x, hx, y, hy, e⟩` from `h1`. Take `⟨m, rfl⟩` from `(FractionalIdeal.mem_spanSingleton _).1 hx`. Take `⟨a₀, ha₀, rfl⟩` from `FractionalIdeal.mem_singleton_mul.1 hy`.

Use `⟨t, a₀, m, ha₀, by rw [← e, Algebra.smul_def, mul_comm (M : E)], fun a ha => ?_⟩` and prove the remaining obligations. Establish `: t * a ∈ (1 : FractionalIdeal (NumberField.RingOfIntegers E)⁰ E)`. Rewrite using `[← ht, FractionalIdeal.mem_add]`. Conclude with `⟨0, FractionalIdeal.zero_mem _, _, FractionalIdeal.mem_singleton_mul.2 ⟨a, ha, rfl⟩, zero_add _⟩`. Take `⟨b, hb⟩` from `(FractionalIdeal.mem_one_iff _).1 this`.

Conclude with `⟨b, hb.symm⟩`.
-/
theorem exists_scale_coprime {E : Type} [Field E] [NumberField E]
    (A : FractionalIdeal (NumberField.RingOfIntegers E)⁰ E) (hA : A ≠ 0) (M : ℕ) (hM : 0 < M) :
    ∃ (t a₀ : E) (m : NumberField.RingOfIntegers E), a₀ ∈ A ∧ (1 : E) = M * algebraMap _ E m + t * a₀ ∧
      ∀ a ∈ A, ∃ b : NumberField.RingOfIntegers E, t * a = algebraMap _ E b := by
  have hM' : (M : E) ≠ 0 := by exact_mod_cast hM.ne'
  have hle : FractionalIdeal.spanSingleton (NumberField.RingOfIntegers E)⁰ (M : E) ≤ 1 := by
    rw [FractionalIdeal.spanSingleton_le_iff_mem, FractionalIdeal.mem_one_iff]
    exact ⟨M, map_natCast _ _⟩
  obtain ⟨t, ht⟩ := IsDedekindDomain.exists_add_spanSingleton_mul_eq hle
    (FractionalIdeal.spanSingleton_ne_zero_iff.2 hM') hA
  have h1 : (1 : E) ∈ (1 : FractionalIdeal (NumberField.RingOfIntegers E)⁰ E) := FractionalIdeal.one_mem_one _
  rw [← ht, FractionalIdeal.mem_add] at h1
  obtain ⟨x, hx, y, hy, e⟩ := h1
  obtain ⟨m, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 hx
  obtain ⟨a₀, ha₀, rfl⟩ := FractionalIdeal.mem_singleton_mul.1 hy
  refine ⟨t, a₀, m, ha₀, by rw [← e, Algebra.smul_def, mul_comm (M : E)], fun a ha => ?_⟩
  have : t * a ∈ (1 : FractionalIdeal (NumberField.RingOfIntegers E)⁰ E) := by
    rw [← ht, FractionalIdeal.mem_add]
    exact ⟨0, FractionalIdeal.zero_mem _, _, FractionalIdeal.mem_singleton_mul.2 ⟨a, ha, rfl⟩, zero_add _⟩
  obtain ⟨b, hb⟩ := (FractionalIdeal.mem_one_iff _).1 this
  exact ⟨b, hb.symm⟩

end Core

section Frame

/- English proof (translation)
Set `ψ : (Fin n → R') →+ (Fin n → R)` to `{ toFun := fun z => (β⁻¹ : GL (Fin n) R).1 *ᵥ (fun a => σ (z a)) map_zero' := by`. Establish `: (fun a => σ ((0 : Fin n → R') a)) = 0` using `by funext a; simp`. Rewrite using `[this, Matrix.mulVec_zero]`. Use the proof step `map_add' := fun x y => by`. Rewrite using `[← Matrix.mulVec_add]`.

Use `congr 1`. Use function extensionality and compare the values at `a`. Simplify using `}`. Establish `hψ : ∀ z, ψ z = (β⁻¹ : GL (Fin n) R).1 *ᵥ (fun a => σ (z a))` using `fun _ => rfl`. Establish `hψi : Function.Injective ψ`.

Introduce `x y h`. Use `congrArg (β.1 *ᵥ ·) h` as an intermediate fact. Simplify using `only [hψ, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] at this`. Use function extensionality and compare the values at `a`. Conclude with `hσ.1 (congrFun this a)`.

Establish `hψs : Function.Surjective ψ`. Introduce `x`. Use `choose z hz using fun a => hσ.2 ((β.1 *ᵥ x) a)`. Use `⟨z, ?_⟩` and prove the remaining obligations. Rewrite using `[hψ, funext hz, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]`.

Establish `hψm : ∀ (c : R') (z : Fin n → R'), ψ (fun i => c * z i) = fun i => σ c * ψ z i`. Introduce `c z`. Establish `: (fun a => σ (c * z a)) = σ c • fun a => σ (z a)` using `by funext a; simp`. Rewrite using `[hψ, this, Matrix.mulVec_smul]`. Both sides reduce to the same expression.

Establish `hgen : ∀ a, A a → ∀ s : Fin n → R, (∀ i, s i ∈ S) → (fun i => σ (j a) * s i) ∈ N.map ψ`. Introduce `a ha s hs`. Take `⟨z, rfl⟩` from `hψs s`. Rewrite using `[← hψm]`. Use `AddSubgroup.mem_map_of_mem _ ?_` and prove the remaining obligations.

Rewrite using `[hN]`. Conclude with `AddSubgroup.subset_closure ⟨a, ha, z, (hL z).2 hs, rfl⟩`. Establish `hind : ∀ (P : AddSubgroup (Fin n → R)), (∀ a, A a → ∀ s : Fin n → R, (∀ i, s i ∈ S) → (fun i => σ (j a) * s i) ∈ P) → N.map ψ ≤ P`. Introduce `P hP`. Rewrite using `[AddSubgroup.map_le_iff_le_comap, hN, AddSubgroup.closure_le]`.

Introduce and unpack `_ ⟨a, ha, z, hz, rfl⟩`. Rewrite using `[SetLike.mem_coe, AddSubgroup.mem_comap, hψm]`. Conclude with `hP a ha _ ((hL z).1 hz)`. Set `jv : (Fin n → K) →+ (Fin n → R')` to `{ toFun := fun v i => j (v i) map_zero' := by funext a; simp map_add' := fun x y => by funext a; simp }`. Establish `hjv : ∀ v, jv v = fun i => j (v i)` using `fun _ => rfl`.

Set `φ : La →+ (Fin n → R)` to `ψ.comp (jv.comp ι.toAddMonoidHom)`. Establish `hφ : ∀ a, φ a = ψ (fun i => j (ι a i))` using `fun _ => rfl`. Establish `hMu : σ (j (M : K)⁻¹) * (M : R) = 1`. Rewrite using `[← map_natCast (σ.comp j), RingHom.comp_apply, ← map_mul, ← map_mul, inv_mul_cancel₀ hM, map_one, map_one]`. Take `⟨ρ, r1, r2, r3, r4⟩` from `coord_core S o M (fun x hx => by rw [← one_mul x, ← hMu, mul_assoc, ← nsmul_eq_mul, hx, mul_zero]) (σ (j t)) (σ (j a₀)) m (by`.

Use `congrArg (σ.comp j) h1` as an intermediate fact. Simplify `this)` using `[ho]`. Use the proof step `(N.map ψ)`. Use the proof step `(fun w hw => by`. Use `hind ((AddSubgroup.pi Set.univ fun _ => S.toAddSubgroup).comap (DistribMulAction.toAddMonoidHom (Fin n → R) (σ (j t)))) (fun a ha s hs i _ => by` as an intermediate fact.

Take `⟨b, hb⟩` from `ht a ha`. Use `show σ (j t) * (σ (j a) * s i) ∈ S`. Rewrite using `[← mul_assoc, ← map_mul, ← map_mul, hb, ← ho]`. Conclude with `S.mul_mem (o b).2 (hs i)) hw`. Conclude with `fun i => this i trivial)`.

Use the proof step `(fun s => hgen a₀ ha₀ _ fun i => (s i).2)`. Use the proof step `(fun b w hw => hind ((N.map ψ).comap (DistribMulAction.toAddMonoidHom (Fin n → R) (o b : R))) (fun a ha s hs => by`. Use `hgen _ (hA b a ha) s hs` as an intermediate fact. Use `show (fun i => (o b : R) * (σ (j a) * s i)) ∈ N.map ψ`. Simplify `this) hw)` using `only [map_mul, ho, mul_assoc]`.

Use the proof step `(fun y w hw => hind ((N.map ψ).comap (Matrix.mulVecLin (y.map S.subtype)).toAddMonoidHom) (fun a ha s hs => by`. Use `hgen a ha (y.map S.subtype *ᵥ s) fun i => by` as an intermediate fact. Simplify using `only [Matrix.mulVec, dotProduct]`. Conclude with `S.sum_mem fun k _ => S.mul_mem (y i k).2 (hs k)`. Use `show y.map S.subtype *ᵥ (σ (j a) • s) ∈ N.map ψ`.

Rewrite using `[Matrix.mulVec_smul]`. Conclude with `this) hw)`. Use `φ`. Use the proof step `(fun b a => by`. Rewrite using `[hφ, hφ, ho, ← hψm]`.

Use `congr 1`. Use function extensionality and compare the values at `i`. Rewrite using `[map_smul, Pi.smul_apply, Algebra.smul_def, map_mul])`. Use the proof step `(hψi.comp (fun x y h => hinj (funext fun i => hj (congrFun h i))))`. Use the proof step `(fun a => AddSubgroup.mem_map_of_mem _ ((hrat _).2 ⟨a, rfl⟩))`.

Use the proof step `(by`. Introduce and unpack `_ ⟨z, hz, rfl⟩`. Take `⟨_, ⟨a, rfl⟩, w, hw, rfl⟩` from `happ z hz`. Conclude with `⟨a, _, AddSubgroup.mem_map_of_mem _ hw, by rw [map_add, map_nsmul, hφ]⟩)`. Use the proof step `(by`.

Introduce and unpack `a _ ⟨w, hw, rfl⟩ h`. Rewrite `h` using `[hφ, ← map_nsmul]`. Establish `h2` using `hψi h`. Establish `h3 : (fun i => j (((M : K)⁻¹ • ι a) i)) = w`. Use function extensionality and compare the values at `i`.

Use `congrFun h2 i` as an intermediate fact. Rewrite `this` using `[Pi.smul_apply, nsmul_eq_mul]`. Rewrite using `[Pi.smul_apply, smul_eq_mul, map_mul, this, ← mul_assoc, ← map_natCast j, ← map_mul, inv_mul_cancel₀ hM, map_one, one_mul]`. Take `⟨a', ha'⟩` from `(hrat _).1 (h3 ▸ hw)`. Use `⟨a', hinj ?_⟩` and prove the remaining obligations.

Rewrite using `[map_nsmul, ha', ← Nat.cast_smul_eq_nsmul K, smul_smul, mul_inv_cancel₀ hM, one_smul])`. Use `⟨ρ, r1, r2, r3, fun κ y hκ a a' => ?_⟩` and prove the remaining obligations. Rewrite using `[← r4]`. Establish `he : ψ (κ *ᵥ (fun i => j (ι a i)) - fun i => j (ι a' i)) = y.map S.subtype *ᵥ φ a - φ a'`. Rewrite using `[map_sub, hφ, hφ]`.

Use `congr 1`. Establish `: (fun c => σ ((κ *ᵥ fun i => j (ι a i)) c)) = κ.map σ *ᵥ fun c => σ (j (ι a c))`. Use function extensionality and compare the values at `c`. Conclude with `RingHom.map_mulVec σ κ _ c`. Rewrite using `[hψ, hψ, this, hκ, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, hw, h⟩`. Conclude with `⟨_, AddSubgroup.mem_map_of_mem _ hw, by rw [← he, h, map_nsmul]⟩`. Introduce and unpack `⟨_, ⟨w, hw, rfl⟩, h⟩`. Conclude with `⟨w, hw, hψi (by rw [he, h, map_nsmul])⟩`.
-/
theorem coord_frame {O K R' R : Type} [CommRing O] [Field K] [Algebra O K] [CommRing R'] [CommRing R]
    (j : K →+* R') (σ : R' →+* R) (hσ : Function.Bijective σ) (S : Subring R) (o : O →+* S)
    (ho : ∀ b, (o b : R) = σ (j (algebraMap O K b))) {n : ℕ} (β : GL (Fin n) R) (L : Set (Fin n → R'))
    (hL : ∀ z, z ∈ L ↔ ∀ i, (β⁻¹ : GL (Fin n) R).1.mulVec (fun a => σ (z a)) i ∈ S)
    (M : ℕ) (hM : (M : K) ≠ 0) (A : K → Prop) (hA : ∀ (b : O) (a : K), A a → A (algebraMap O K b * a))
    (t a₀ : K) (m : O) (ha₀ : A a₀) (h1 : (1 : K) = M * algebraMap O K m + t * a₀)
    (ht : ∀ a, A a → ∃ b : O, t * a = algebraMap O K b) (N : AddSubgroup (Fin n → R'))
    (hN : N = AddSubgroup.closure {w | ∃ a, A a ∧ ∃ z ∈ L, w = fun i => j a * z i})
    {La : Type} [AddCommGroup La] [Module O La] (ι : La →ₗ[O] (Fin n → K)) (hinj : Function.Injective ι)
    (hrat : ∀ v : Fin n → K, (fun i => j (v i)) ∈ N ↔ v ∈ LinearMap.range ι)
    (happ : ∀ z ∈ N, ∃ x ∈ LinearMap.range ι, ∃ w ∈ N, z = (fun i => j (x i)) + M • w)
    (hj : Function.Injective j) :
    ∃ ρ : La →+ (Fin n → S), (∀ (b : O) (a : La), ρ (b • a) = o b • ρ a) ∧
      (∀ s : Fin n → S, ∃ (a : La) (s' : Fin n → S), s = ρ a + M • s') ∧
      (∀ I J : Ideal O, I * J = Ideal.span {(M : O)} → ∀ a : La, (∀ i, ρ a i ∈ I.map o) →
        a ∈ I • (⊤ : Submodule O La)) ∧
      ∀ (κ : Matrix (Fin n) (Fin n) R') (y : Matrix (Fin n) (Fin n) S),
        κ.map σ = β.1 * y.map S.subtype * (β⁻¹ : GL (Fin n) R).1 → ∀ a a' : La,
        (∃ w ∈ N, κ *ᵥ (fun i => j (ι a i)) - (fun i => j (ι a' i)) = M • w) ↔
          ∃ s : Fin n → S, y *ᵥ ρ a - ρ a' = M • s := by
  let ψ : (Fin n → R') →+ (Fin n → R) :=
    { toFun := fun z => (β⁻¹ : GL (Fin n) R).1 *ᵥ (fun a => σ (z a))
      map_zero' := by
        have : (fun a => σ ((0 : Fin n → R') a)) = 0 := by funext a; simp
        rw [this, Matrix.mulVec_zero]
      map_add' := fun x y => by
        rw [← Matrix.mulVec_add]; congr 1; funext a; simp }
  have hψ : ∀ z, ψ z = (β⁻¹ : GL (Fin n) R).1 *ᵥ (fun a => σ (z a)) := fun _ => rfl
  have hψi : Function.Injective ψ := by
    intro x y h
    have := congrArg (β.1 *ᵥ ·) h
    simp only [hψ, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] at this
    funext a
    exact hσ.1 (congrFun this a)
  have hψs : Function.Surjective ψ := by
    intro x
    choose z hz using fun a => hσ.2 ((β.1 *ᵥ x) a)
    refine ⟨z, ?_⟩
    rw [hψ, funext hz, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have hψm : ∀ (c : R') (z : Fin n → R'), ψ (fun i => c * z i) = fun i => σ c * ψ z i := by
    intro c z
    have : (fun a => σ (c * z a)) = σ c • fun a => σ (z a) := by funext a; simp
    rw [hψ, this, Matrix.mulVec_smul]
    rfl
  have hgen : ∀ a, A a → ∀ s : Fin n → R, (∀ i, s i ∈ S) → (fun i => σ (j a) * s i) ∈ N.map ψ := by
    intro a ha s hs
    obtain ⟨z, rfl⟩ := hψs s
    rw [← hψm]
    refine AddSubgroup.mem_map_of_mem _ ?_
    rw [hN]
    exact AddSubgroup.subset_closure ⟨a, ha, z, (hL z).2 hs, rfl⟩
  have hind : ∀ (P : AddSubgroup (Fin n → R)),
      (∀ a, A a → ∀ s : Fin n → R, (∀ i, s i ∈ S) → (fun i => σ (j a) * s i) ∈ P) → N.map ψ ≤ P := by
    intro P hP
    rw [AddSubgroup.map_le_iff_le_comap, hN, AddSubgroup.closure_le]
    rintro _ ⟨a, ha, z, hz, rfl⟩
    rw [SetLike.mem_coe, AddSubgroup.mem_comap, hψm]
    exact hP a ha _ ((hL z).1 hz)
  let jv : (Fin n → K) →+ (Fin n → R') :=
    { toFun := fun v i => j (v i)
      map_zero' := by funext a; simp
      map_add' := fun x y => by funext a; simp }
  have hjv : ∀ v, jv v = fun i => j (v i) := fun _ => rfl
  let φ : La →+ (Fin n → R) := ψ.comp (jv.comp ι.toAddMonoidHom)
  have hφ : ∀ a, φ a = ψ (fun i => j (ι a i)) := fun _ => rfl
  have hMu : σ (j (M : K)⁻¹) * (M : R) = 1 := by
    rw [← map_natCast (σ.comp j), RingHom.comp_apply, ← map_mul, ← map_mul, inv_mul_cancel₀ hM, map_one, map_one]
  obtain ⟨ρ, r1, r2, r3, r4⟩ := coord_core S o M
    (fun x hx => by rw [← one_mul x, ← hMu, mul_assoc, ← nsmul_eq_mul, hx, mul_zero])
    (σ (j t)) (σ (j a₀)) m
    (by
      have := congrArg (σ.comp j) h1
      simpa [ho] using this)
    (N.map ψ)
    (fun w hw => by
      have := hind ((AddSubgroup.pi Set.univ fun _ => S.toAddSubgroup).comap
        (DistribMulAction.toAddMonoidHom (Fin n → R) (σ (j t)))) (fun a ha s hs i _ => by
          obtain ⟨b, hb⟩ := ht a ha
          show σ (j t) * (σ (j a) * s i) ∈ S
          rw [← mul_assoc, ← map_mul, ← map_mul, hb, ← ho]
          exact S.mul_mem (o b).2 (hs i)) hw
      exact fun i => this i trivial)
    (fun s => hgen a₀ ha₀ _ fun i => (s i).2)
    (fun b w hw => hind ((N.map ψ).comap (DistribMulAction.toAddMonoidHom (Fin n → R) (o b : R)))
      (fun a ha s hs => by
        have := hgen _ (hA b a ha) s hs
        show (fun i => (o b : R) * (σ (j a) * s i)) ∈ N.map ψ
        simpa only [map_mul, ho, mul_assoc] using this) hw)
    (fun y w hw => hind ((N.map ψ).comap (Matrix.mulVecLin (y.map S.subtype)).toAddMonoidHom)
      (fun a ha s hs => by
        have := hgen a ha (y.map S.subtype *ᵥ s) fun i => by
          simp only [Matrix.mulVec, dotProduct]
          exact S.sum_mem fun k _ => S.mul_mem (y i k).2 (hs k)
        show y.map S.subtype *ᵥ (σ (j a) • s) ∈ N.map ψ
        rw [Matrix.mulVec_smul]
        exact this) hw)
    φ
    (fun b a => by
      rw [hφ, hφ, ho, ← hψm]
      congr 1
      funext i
      rw [map_smul, Pi.smul_apply, Algebra.smul_def, map_mul])
    (hψi.comp (fun x y h => hinj (funext fun i => hj (congrFun h i))))
    (fun a => AddSubgroup.mem_map_of_mem _ ((hrat _).2 ⟨a, rfl⟩))
    (by
      rintro _ ⟨z, hz, rfl⟩
      obtain ⟨_, ⟨a, rfl⟩, w, hw, rfl⟩ := happ z hz
      exact ⟨a, _, AddSubgroup.mem_map_of_mem _ hw, by rw [map_add, map_nsmul, hφ]⟩)
    (by
      rintro a _ ⟨w, hw, rfl⟩ h
      rw [hφ, ← map_nsmul] at h
      have h2 := hψi h
      have h3 : (fun i => j (((M : K)⁻¹ • ι a) i)) = w := by
        funext i
        have := congrFun h2 i
        rw [Pi.smul_apply, nsmul_eq_mul] at this
        rw [Pi.smul_apply, smul_eq_mul, map_mul, this, ← mul_assoc, ← map_natCast j, ← map_mul,
          inv_mul_cancel₀ hM, map_one, one_mul]
      obtain ⟨a', ha'⟩ := (hrat _).1 (h3 ▸ hw)
      refine ⟨a', hinj ?_⟩
      rw [map_nsmul, ha', ← Nat.cast_smul_eq_nsmul K, smul_smul, mul_inv_cancel₀ hM, one_smul])
  refine ⟨ρ, r1, r2, r3, fun κ y hκ a a' => ?_⟩
  rw [← r4]
  have he : ψ (κ *ᵥ (fun i => j (ι a i)) - fun i => j (ι a' i)) = y.map S.subtype *ᵥ φ a - φ a' := by
    rw [map_sub, hφ, hφ]
    congr 1
    have : (fun c => σ ((κ *ᵥ fun i => j (ι a i)) c)) = κ.map σ *ᵥ fun c => σ (j (ι a c)) := by
      funext c
      exact RingHom.map_mulVec σ κ _ c
    rw [hψ, hψ, this, hκ, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Units.inv_mul, Matrix.one_mul]
  constructor
  · rintro ⟨w, hw, h⟩
    exact ⟨_, AddSubgroup.mem_map_of_mem _ hw, by rw [← he, h, map_nsmul]⟩
  · rintro ⟨_, ⟨w, hw, rfl⟩, h⟩
    exact ⟨w, hw, hψi (by rw [he, h, map_nsmul])⟩

end Frame

section Adelic

open NumberField IsDedekindDomain

/- English proof (translation)
Take `⟨t, a₀, m, ha₀, h1, ht⟩` from `exists_scale_coprime A hA M hM`. Take `⟨p1, p2, -, -⟩` from `GlobalTheory.AdLat.hat_rational_points_and_approx F E n Λ hfg hsp`. Rewrite `p1`, `p2` using `[← hhat, ← hran]`. Establish `hnt : Nontrivial (FiniteAdeleRing (𝓞 F) F)`. Take `⟨P, hP⟩` from `Ideal.exists_maximal (𝓞 F)`.

Set `v : HeightOneSpectrum (𝓞 F)` to `⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField F)⟩`. Use `⟨0, 1, fun h => ?_⟩` and prove the remaining obligations. Establish `: (0 : v.adicCompletion F) = 1` using `congrArg (fun x : FiniteAdeleRing (𝓞 F) F => x v) h`. Conclude with `zero_ne_one this`. Take `⟨ρ, r1, r2, r3, r4⟩` from `coord_frame (Algebra.TensorProduct.includeRight (R := F) (A := FiniteAdeleRing (𝓞 F) F) (B := E)).toRingHom (Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E).toAlgHom.toRingHom (Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E).bijective (Formalism.L2.Herm.intAf …`.

Conclude with `⟨ρ, r1, r2, r3, fun κ y hκ a a' => r4 κ y.1 hκ a a'⟩`.
-/
theorem coord_adelic (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (L : Set (Fin n → GlobalTheory.AdLat.RA F E))
    (hL : ∀ z, z ∈ L ↔ ∀ i, (β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)).1.mulVec
      (fun a => (Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E).toAlgHom.toRingHom (z a)) i ∈
        Formalism.L2.Herm.intAf F E)
    (M : ℕ) (hM : 0 < M) (A : FractionalIdeal (𝓞 E)⁰ E) (hA : A ≠ 0) (N : AddSubgroup (Fin n → GlobalTheory.AdLat.RA F E))
    (hN : N = AddSubgroup.closure {w | ∃ a : E, a ∈ A ∧ ∃ z ∈ L,
      w = fun i => ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] a) * z i})
    (Λ : Submodule (𝓞 E) (Fin n → E)) (hfg : Λ.FG) (hsp : Submodule.span E (Λ : Set (Fin n → E)) = ⊤)
    (hhat : N = GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E)))
    {La : Type} [AddCommGroup La] [Module (𝓞 E) La] (ι : La →ₗ[𝓞 E] (Fin n → E)) (hinj : Function.Injective ι)
    (hran : LinearMap.range ι = Λ) :
    ∃ ρ : La →+ (Fin n → Formalism.L2.Herm.intAf F E),
      (∀ (b : 𝓞 E) (a : La), ρ (b • a) = Formalism.L2.DIV.oToS F E b • ρ a) ∧
      (∀ s : Fin n → Formalism.L2.Herm.intAf F E, ∃ (a : La) (s' : Fin n → Formalism.L2.Herm.intAf F E), s = ρ a + M • s') ∧
      (∀ I J : Ideal (𝓞 E), I * J = Ideal.span {(M : 𝓞 E)} → ∀ a : La, (∀ i, ρ a i ∈ Formalism.L2.DIV.idS F I) →
        a ∈ I • (⊤ : Submodule (𝓞 E) La)) ∧
      ∀ (κ : Matrix (Fin n) (Fin n) (GlobalTheory.AdLat.RA F E)) (y : GL (Fin n) (Formalism.L2.Herm.intAf F E)),
        κ.map (Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E).toAlgHom.toRingHom =
          (Formalism.L2.DIV.frGL β y).1 → ∀ a a' : La,
        (∃ w ∈ N, κ *ᵥ GlobalTheory.AdLat.fv F (ι a) - GlobalTheory.AdLat.fv F (ι a') = M • w) ↔
          ∃ s : Fin n → Formalism.L2.Herm.intAf F E, y.1 *ᵥ ρ a - ρ a' = M • s := by
  obtain ⟨t, a₀, m, ha₀, h1, ht⟩ := exists_scale_coprime A hA M hM
  obtain ⟨p1, p2, -, -⟩ := GlobalTheory.AdLat.hat_rational_points_and_approx F E n Λ hfg hsp
  rw [← hhat, ← hran] at p1 p2
  have hnt : Nontrivial (FiniteAdeleRing (𝓞 F) F) := by
    obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 F)
    let v : HeightOneSpectrum (𝓞 F) := ⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP
      (RingOfIntegers.not_isField F)⟩
    refine ⟨0, 1, fun h => ?_⟩
    have : (0 : v.adicCompletion F) = 1 := congrArg (fun x : FiniteAdeleRing (𝓞 F) F => x v) h
    exact zero_ne_one this
  obtain ⟨ρ, r1, r2, r3, r4⟩ := coord_frame
    (Algebra.TensorProduct.includeRight (R := F) (A := FiniteAdeleRing (𝓞 F) F) (B := E)).toRingHom
    (Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E).toAlgHom.toRingHom
    (Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E).bijective
    (Formalism.L2.Herm.intAf F E) (Formalism.L2.DIV.oToS F E) (fun b => rfl) β L hL M
    (by exact_mod_cast hM.ne') (fun a => a ∈ A)
    (fun b a ha => by rw [← Algebra.smul_def]; exact A.val.smul_mem b ha)
    t a₀ m ha₀ h1 ht N hN ι hinj p1 (p2 M hM)
    (Algebra.TensorProduct.includeRight_injective (algebraMap F (FiniteAdeleRing (𝓞 F) F)).injective)
  exact ⟨ρ, r1, r2, r3, fun κ y hκ a a' => r4 κ y.1 hκ a a'⟩

end Adelic

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke
attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Unfold `gLat`. Rewrite using `[map_one, Units.val_one]`. Use extensionality with `z`. Simplify using `only [Set.mem_image, Matrix.one_mulVec, exists_eq_right]`.
-/
theorem gLat_one_eq {D : D7} (V : HSp D) :
    gLat V 1 = (latHat V : Set (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E)) := by
  unfold gLat
  rw [map_one, Units.val_one]
  ext z
  simp only [Set.mem_image, Matrix.one_mulVec, exists_eq_right]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem finR_rfl_val {D : D7} (V : HSp D) (κ : GA D V) :
    (LatticeBasisLifts.finR V rfl κ).1 = (finHom V κ).1.map (swapAE D) := rfl

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Introduce `D V r hr β hβ La _ _ ι hι M hM`. Substitute `hr` using the available equality. Take `⟨hfg, hsp, -, -, hhat, -⟩` from `GlobalTheory.Member.latG_lattice_and_completion D V 1`. Take `⟨ρ, r1, r2, r3, r4⟩` from `coord_adelic D.host.F D.host.E β (gLat V 1) (by rw [gLat_one_eq]; exact hβ) M hM D.host.AA (AA_ne_zero Formalism.IndefR.Fin.factPrincipalDatum D) (latGHat V 1) rfl (latG V 1) hfg hsp hhat ι hι.1 hι.2`. Use `⟨ρ, r1, r2, r3, fun κ y hκ a a' => r4 (finHom V κ).1 y ?_ a a'⟩` and prove the remaining obligations.

Rewrite using `[← hκ, finR_rfl_val]`. Both sides reduce to the same expression.
-/
theorem exists_lattice_coord : ∀ (D : D7) (V : HSp D) (r : ℕ) (hr : V.rank = r) (β : GL (Fin r) (EAf D)), LatticeBasisLifts.IsLatBasis V hr β → ∀ (La : Type) [AddCommGroup La] [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)), LatEmb V ι → ∀ M : ℕ, 0 < M → ∃ ρ : La →+ (Fin r → LatticeBasisLifts.OAf D), (∀ (b : 𝓞 D.host.E) (a : La), ρ (b • a) = Formalism.L2.DIV.oToS D.host.F D.host.E b • ρ a) ∧ (∀ s : Fin r → LatticeBasisLifts.OAf D, ∃ (a : La) (s' : Fin r → LatticeBasisLifts.OAf D), s = ρ a + M • s') ∧ (∀ I J : Ideal (𝓞 D.host.E), I * J = Ideal.span {(M : 𝓞 D.host.E)} → ∀ a : La, (∀ i, ρ a i ∈ Formalism.L2.DIV.idS D.host.F I) → a ∈ I • (⊤ : Submodule (𝓞 D.host.E) La)) ∧ ∀ (κ : GA D V) (y : GL (Fin r) (LatticeBasisLifts.OAf D)), LatticeBasisLifts.finR V hr κ = Formalism.L2.DIV.frGL β y → ∀ a a' : La, (∃ w ∈ latGHat V 1, (finHom V κ).1.mulVec (finVec V (ι a)) - finVec V (ι a') = M • w) ↔ ∃ s : Fin r → LatticeBasisLifts.OAf D, y.1.mulVec (ρ a) - ρ a' = M • s := by
  intro D V r hr β hβ La _ _ ι hι M hM
  subst hr
  obtain ⟨hfg, hsp, -, -, hhat, -⟩ := GlobalTheory.Member.latG_lattice_and_completion D V 1
  obtain ⟨ρ, r1, r2, r3, r4⟩ := coord_adelic D.host.F D.host.E β (gLat V 1)
    (by rw [gLat_one_eq]; exact hβ) M hM D.host.AA (AA_ne_zero Formalism.IndefR.Fin.factPrincipalDatum D)
    (latGHat V 1) rfl (latG V 1) hfg hsp hhat ι hι.1 hι.2
  refine ⟨ρ, r1, r2, r3, fun κ y hκ a a' => r4 (finHom V κ).1 y ?_ a a'⟩
  rw [← hκ, finR_rfl_val]
  rfl

end GlobalTheory.GeoActCompare
