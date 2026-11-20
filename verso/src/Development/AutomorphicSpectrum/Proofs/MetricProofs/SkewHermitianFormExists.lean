import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.BlockGLSupportedMemMirabolicSupported
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.HermTrace

section Field

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Use `set K := maximalRealSubfield E`. Use `set t := IsCMField.complexConj E`. Use `set y := conj K E x with hy`. Establish `hyy : conj K E y = x` using `conj_conj x`. Establish `fix : ∀ a : E, conj K E a = a → t a = a`.

Introduce `a ha`. Take `⟨b, rfl⟩` from `conj_eq_self_iff.1 ha`. Conclude with `(IsCMField.complexConj_eq_self_iff E _).2 b.2`. Establish `ha : t (x + y) = x + y` using `fix _ (by rw [map_add, hyy, ← hy, add_comm])`. Establish `hb : t (x * y) = x * y` using `fix _ (by rw [map_mul, hyy, ← hy, mul_comm])`.

Establish `hz : (t x - x) * (t x - y) = 0`. Establish `h0 : x * x - (x + y) * x + x * y = 0` using `by ring`. Establish `h1` using `congrArg t h0`. Rewrite `h1` using `[map_add, map_sub, map_mul, map_mul, ha, hb, map_zero]`. Take the linear combination `h1`.

Break down `mul_eq_zero.1 hz with h | h` into its components or cases. Establish `hx : t x = x` using `sub_eq_zero.1 h`. Establish `: x ∈ K` using `(IsCMField.complexConj_eq_self_iff E x).1 hx`. Establish `h2 : y = x` using `conj_eq_self_iff.2 ⟨⟨x, this⟩, rfl⟩`. Rewrite using `[h2, hx]`.

Conclude with `(sub_eq_zero.1 h).symm`.
-/
theorem quadConj_eq_complexConj (x : E) :
    conj (maximalRealSubfield E) E x = IsCMField.complexConj E x := by
  set K := maximalRealSubfield E
  set t := IsCMField.complexConj E
  set y := conj K E x with hy
  have hyy : conj K E y = x := conj_conj x
  have fix : ∀ a : E, conj K E a = a → t a = a := by
    intro a ha
    obtain ⟨b, rfl⟩ := conj_eq_self_iff.1 ha
    exact (IsCMField.complexConj_eq_self_iff E _).2 b.2
  have ha : t (x + y) = x + y := fix _ (by rw [map_add, hyy, ← hy, add_comm])
  have hb : t (x * y) = x * y := fix _ (by rw [map_mul, hyy, ← hy, mul_comm])
  have hz : (t x - x) * (t x - y) = 0 := by
    have h0 : x * x - (x + y) * x + x * y = 0 := by ring
    have h1 := congrArg t h0
    rw [map_add, map_sub, map_mul, map_mul, ha, hb, map_zero] at h1
    linear_combination h1
  rcases mul_eq_zero.1 hz with h | h
  · have hx : t x = x := sub_eq_zero.1 h
    have : x ∈ K := (IsCMField.complexConj_eq_self_iff E x).1 hx
    have h2 : y = x := conj_eq_self_iff.2 ⟨⟨x, this⟩, rfl⟩
    rw [h2, hx]
  · exact (sub_eq_zero.1 h).symm

/- English proof (translation)
Establish `hd : (0 : ℝ) < H.d` using `by exact_mod_cast H.d_prime.pos`. Establish `hsq : (H.rt : E) ^ 2 = -(H.d : E)`. Use `congrArg (algebraMap (𝓞 E) E) H.rt_sq` as an intermediate fact. Simplify using `using this`. Establish `h2 : (IsCMField.complexConj E (H.rt : E)) ^ 2 = (H.rt : E) ^ 2`.

Rewrite using `[← map_pow, hsq, map_neg, map_natCast]`. Break down `sq_eq_sq_iff_eq_or_eq_neg.1 h2 with h | h` into its components or cases. It suffices to derive a contradiction. Take `⟨φ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Establish `hc : starRingEnd ℂ (φ (H.rt : E)) = φ (H.rt : E)`.

Rewrite using `[← IsCMField.complexEmbedding_complexConj E φ, h]`. Take `⟨s, hs⟩` from `Complex.conj_eq_iff_real.1 hc`. Establish `h3` using `congrArg φ hsq`. Rewrite `h3` using `[map_pow, map_neg, map_natCast, hs]`. Establish `h4 : (s ^ 2 : ℝ) = -(H.d : ℝ)` using `by exact_mod_cast h3`.

Use polynomial arithmetic with `[sq_nonneg s]`. Conclude with `h`.
-/
theorem complexConj_rt (H : Host E) : IsCMField.complexConj E (H.rt : E) = -(H.rt : E) := by
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have hsq : (H.rt : E) ^ 2 = -(H.d : E) := by
    have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
    simpa using this
  have h2 : (IsCMField.complexConj E (H.rt : E)) ^ 2 = (H.rt : E) ^ 2 := by
    rw [← map_pow, hsq, map_neg, map_natCast]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h2 with h | h
  · exfalso
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have hc : starRingEnd ℂ (φ (H.rt : E)) = φ (H.rt : E) := by
      rw [← IsCMField.complexEmbedding_complexConj E φ, h]
    obtain ⟨s, hs⟩ := Complex.conj_eq_iff_real.1 hc
    have h3 := congrArg φ hsq
    rw [map_pow, map_neg, map_natCast, hs] at h3
    have h4 : (s ^ 2 : ℝ) = -(H.d : ℝ) := by exact_mod_cast h3
    nlinarith [sq_nonneg s]
  · exact h

/- English proof (translation)
Establish `nd` using `traceForm_nondegenerate ℚ E`. Establish `htc : ∀ z : E, Algebra.trace ℚ E (IsCMField.complexConj E z) = Algebra.trace ℚ E z` using `fun z => Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ) z`. Establish `: h₁ v u - (- IsCMField.complexConj E (h₁ u v)) = 0`. Apply `nd.1` to reduce the goal to its premises. Introduce `a`.

Establish `e1 : Algebra.trace ℚ E (a * IsCMField.complexConj E (h₁ u v)) = Algebra.trace ℚ E (IsCMField.complexConj E a * h₁ u v)`. Rewrite using `[← htc, map_mul, IsCMField.complexConj_apply_apply]`. Establish `e2 : B u (a • v) = B (IsCMField.complexConj E a • u) v`. Rewrite using `[hadj, IsCMField.complexConj_apply_apply]`. Rewrite using `[Algebra.traceForm_apply, mul_comm, mul_sub, map_sub, mul_neg, map_neg, e1, htr, htr, hskew (a • v) u, e2]`.

Expand and normalize the polynomial expressions, which then agree. Take the linear combination `this`.
-/
theorem sesq_skew {V : Type} [AddCommGroup V] [Module E V] [Module ℚ V]
    (B : LinearMap.BilinForm ℚ V)
    (hadj : ∀ (a : E) x y, B (a • x) y = B x (IsCMField.complexConj E a • y))
    (hskew : ∀ u v, B u v = - B v u) (h₁ : V → V → E)
    (htr : ∀ x y (a : E), Algebra.trace ℚ E (a * h₁ x y) = B (a • x) y) (u v : V) :
    h₁ v u = - IsCMField.complexConj E (h₁ u v) := by
  have nd := traceForm_nondegenerate ℚ E
  have htc : ∀ z : E, Algebra.trace ℚ E (IsCMField.complexConj E z) = Algebra.trace ℚ E z := fun z =>
    Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ) z
  have : h₁ v u - (- IsCMField.complexConj E (h₁ u v)) = 0 := by
    apply nd.1
    intro a
    have e1 : Algebra.trace ℚ E (a * IsCMField.complexConj E (h₁ u v)) =
        Algebra.trace ℚ E (IsCMField.complexConj E a * h₁ u v) := by
      rw [← htc, map_mul, IsCMField.complexConj_apply_apply]
    have e2 : B u (a • v) = B (IsCMField.complexConj E a • u) v := by
      rw [hadj, IsCMField.complexConj_apply_apply]
    rw [Algebra.traceForm_apply, mul_comm, mul_sub, map_sub, mul_neg, map_neg, e1, htr, htr,
      hskew (a • v) u, e2]
    ring
  linear_combination this

omit [IsCMField E] in

/- English proof (translation)
Take `⟨n, s, hs⟩` from `Module.Finite.exists_fin (R := ℤ) (M := Λ)`. Take `⟨y, hy0, hy⟩` from `exists_integral_multiples ℤ ℚ (L := E) (Finset.univ.image fun p : Fin n × Fin n => F (s p.1) (s p.2))`. Establish `step : ∀ g : Λ →+ E, (∀ i, g (s i) ∈ integralClosure ℤ E) → ∀ x, g x ∈ integralClosure ℤ E`. Introduce `g hg x`. Establish `hx : x ∈ Submodule.span ℤ (Set.range s)` using `hs ▸ Submodule.mem_top`.

Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x h`. Take `⟨i, rfl⟩` from `h`. Conclude with `hg i`. Consider the case `zero`.

Rewrite using `[map_zero]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy`. Rewrite using `[map_add]`. Conclude with `add_mem hx hy`.

Consider the case `smul a x _ hx`. Rewrite using `[map_zsmul]`. Conclude with `zsmul_mem hx a`. Establish `core : ∀ m : ℕ, (∀ i k, (m : E) * F (s i) (s k) ∈ integralClosure ℤ E) → ∀ x y, (m : E) * F x y ∈ integralClosure ℤ E`. Introduce `m hm x y`.

Set `gy : Λ → Λ →+ E` to `fun x => AddMonoidHom.mk' (fun y => (m : E) * F x y) (fun a b => by rw [h2, mul_add])`. Set `gx : Λ → Λ →+ E` to `fun y => AddMonoidHom.mk' (fun x => (m : E) * F x y) (fun a b => by rw [h1, mul_add])`. Conclude with `step (gy x) (fun k => step (gx (s k)) (fun i => hm i k) x) y`. Establish `hint : ∀ i k, IsIntegral ℤ (y • F (s i) (s k))` using `fun i k => hy _ (Finset.mem_image_of_mem _ (Finset.mem_univ (i, k)))`. Take `⟨m, rfl | rfl⟩` from `Int.eq_nat_or_neg y`.

Use `⟨m, by simpa using hy0, core m fun i k => ?_⟩` and prove the remaining obligations. Use `hint i k` as an intermediate fact. Rewrite `this` using `[zsmul_eq_mul, Int.cast_natCast]`. Then use the resulting hypothesis. Use `⟨m, by simpa using hy0, core m fun i k => ?_⟩` and prove the remaining obligations. Use `(hint i k).neg` as an intermediate fact.

Rewrite `this` using `[zsmul_eq_mul, Int.cast_neg, Int.cast_natCast, neg_mul, neg_neg]`. Then use the resulting hypothesis.
-/
theorem exists_nat_integral {Λ : Type} [AddCommGroup Λ] [Module.Finite ℤ Λ] (F : Λ → Λ → E)
    (h1 : ∀ x x' y, F (x + x') y = F x y + F x' y) (h2 : ∀ x y y', F x (y + y') = F x y + F x y') :
    ∃ m : ℕ, m ≠ 0 ∧ ∀ x y, (m : E) * F x y ∈ integralClosure ℤ E := by
  classical
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := ℤ) (M := Λ)
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (L := E)
    (Finset.univ.image fun p : Fin n × Fin n => F (s p.1) (s p.2))
  have step : ∀ g : Λ →+ E, (∀ i, g (s i) ∈ integralClosure ℤ E) →
      ∀ x, g x ∈ integralClosure ℤ E := by
    intro g hg x
    have hx : x ∈ Submodule.span ℤ (Set.range s) := hs ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem x h =>
      obtain ⟨i, rfl⟩ := h
      exact hg i
    | zero =>
      rw [map_zero]
      exact zero_mem _
    | add x y _ _ hx hy =>
      rw [map_add]
      exact add_mem hx hy
    | smul a x _ hx =>
      rw [map_zsmul]
      exact zsmul_mem hx a
  have core : ∀ m : ℕ, (∀ i k, (m : E) * F (s i) (s k) ∈ integralClosure ℤ E) →
      ∀ x y, (m : E) * F x y ∈ integralClosure ℤ E := by
    intro m hm x y
    let gy : Λ → Λ →+ E := fun x => AddMonoidHom.mk' (fun y => (m : E) * F x y)
      (fun a b => by rw [h2, mul_add])
    let gx : Λ → Λ →+ E := fun y => AddMonoidHom.mk' (fun x => (m : E) * F x y)
      (fun a b => by rw [h1, mul_add])
    exact step (gy x) (fun k => step (gx (s k)) (fun i => hm i k) x) y
  have hint : ∀ i k, IsIntegral ℤ (y • F (s i) (s k)) := fun i k =>
    hy _ (Finset.mem_image_of_mem _ (Finset.mem_univ (i, k)))
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg y
  · refine ⟨m, by simpa using hy0, core m fun i k => ?_⟩
    have := hint i k
    rwa [zsmul_eq_mul, Int.cast_natCast] at this
  · refine ⟨m, by simpa using hy0, core m fun i k => ?_⟩
    have := (hint i k).neg
    rwa [zsmul_eq_mul, Int.cast_neg, Int.cast_natCast, neg_mul, neg_neg] at this

end Field

/- English proof (translation)
Introduce `E _ _ _ H Λ _ _ N e B hadj hskew hnd`. Take `⟨h₁, ⟨htr, hadd1, hadd2, hsm1, hsm2⟩, -⟩` from `GlobalTheory.CompanionTheory.Ar.Flat.existsUnique_sesq_of_trace E (Fin N → E) B hadj`. Establish `hsk` using `sesq_skew B hadj hskew h₁ htr`. Take `⟨m, hm0, hint⟩` from `exists_nat_integral (fun x y : Λ => h₁ (e y) (e x)) (fun x x' y => by rw [map_add, hadd2]) (fun x y y' => by rw [map_add, hadd1])`. Establish `hrt0 : (H.rt : E) ≠ 0`.

Introduce `h0`. Establish `hsq : (H.rt : E) ^ 2 = -(H.d : E)`. Use `congrArg (algebraMap (𝓞 E) E) H.rt_sq` as an intermediate fact. Simplify using `using this`. Rewrite `hsq` using `[h0]`.

Establish `hd : (H.d : E) ≠ 0` using `Nat.cast_ne_zero.2 H.d_prime.ne_zero`. Apply `hd` to reduce the goal to its premises. Take the linear combination `hsq`. Use `set c : E := (m : E) * (H.rt : E) with hc`. Establish `hc0 : c ≠ 0` using `mul_ne_zero (Nat.cast_ne_zero.2 hm0) hrt0`.

Establish `htc : IsCMField.complexConj E c = -c`. Rewrite using `[hc, map_mul, map_natCast, complexConj_rt]`. Expand and normalize the polynomial expressions, which then agree. Set `S : (Fin N → E) →ₛₗ[conjHom (maximalRealSubfield E) E] (Fin N → E) →ₗ[E] E` to `LinearMap.mk₂'ₛₗ (conjHom (maximalRealSubfield E) E) (RingHom.id E) (fun v u => c * h₁ u v) (fun v v' u => by rw [hadd2, mul_add]) (fun a v u => by`. Rewrite using `[hsm2, smul_eq_mul]`.

Establish `: conjHom (maximalRealSubfield E) E a = IsCMField.complexConj E a` using `quadConj_eq_complexConj a`. Rewrite using `[this]`. Use the proof step `ring)`. Use the proof step `(fun v u u' => by rw [hadd1, mul_add])`. Use the proof step `(fun a v u => by`.

Rewrite using `[hsm1, RingHom.id_apply, smul_eq_mul]`. Use the proof step `ring)`. Establish `Sapp : ∀ v u, S v u = c * h₁ u v` using `fun _ _ => rfl`. Establish `hinj : Function.Injective S`. Introduce `v v' hvv`.

Establish `hz : ∀ w, h₁ w (v - v') = 0`. Introduce `w`. Establish `h3 : c * h₁ w v = c * h₁ w v'`. Rewrite using `[← Sapp, ← Sapp, hvv]`. Establish `h4` using `mul_left_cancel₀ hc0 h3`.

Establish `h5` using `hadd2 w (v - v') v'`. Rewrite `h5` using `[sub_add_cancel, h4]`. Take the linear combination `-h5`. Establish `: v - v' = 0` using `hnd _ fun w => by`. Establish `h6` using `htr w (v - v') 1`.

Rewrite `h6` using `[one_smul, hz, mul_zero, map_zero]`. Conclude with `h6.symm`. Conclude with `sub_eq_zero.1 this`. Establish `hsurj : Function.Surjective S`. Set `g0 : (Fin N → E) →+ (Fin N → E)` to `AddMonoidHom.mk' (fun u i => S u (Pi.single i 1)) (fun a b => by`.

Use function extensionality and compare the values at `i`. Use `show S (a + b) (Pi.single i 1) = S a (Pi.single i 1) + S b (Pi.single i 1)`. Rewrite using `[Sapp, Sapp, Sapp, hadd2, mul_add])`. Set `g : (Fin N → E) →ₗ[ℚ] (Fin N → E)` to `g0.toRatLinearMap`. Establish `gapp : ∀ u i, g u i = S u (Pi.single i 1)` using `fun _ _ => rfl`.

Establish `ginj : Function.Injective g`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `u hu`. Establish `: S u = S 0`. Apply `(Pi.basisFun E (Fin N)).ext` to reduce the goal to its premises.

Introduce `i`. Rewrite using `[Pi.basisFun_apply, map_zero, ← gapp, hu]`. Both sides reduce to the same expression. Conclude with `hinj (this.trans (by rw [map_zero]) |>.trans (map_zero S).symm)`. Establish `gsurj : Function.Surjective g` using `LinearMap.injective_iff_surjective.1 ginj`.

Introduce `f`. Take `⟨u, hu⟩` from `gsurj fun i => f (Pi.single i 1)`. Use `⟨u, (Pi.basisFun E (Fin N)).ext fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[Pi.basisFun_apply, ← gapp, hu]`. Use `⟨⟨S, ⟨fun x y => ?_⟩, hinj, hsurj⟩, m, hm0, ?_, ?_⟩` and prove the remaining obligations.

Establish `h7 : conjHom (maximalRealSubfield E) E (S x y) = IsCMField.complexConj E (S x y)` using `quadConj_eq_complexConj _`. Rewrite using `[h7, Sapp, Sapp, map_mul, htc, hsk y x]`. Expand and normalize the polynomial expressions, which then agree. Introduce `a u v`. Establish `h8 : ((m : E) * (H.rt : E))⁻¹ * S v u = h₁ u v`.

Rewrite using `[Sapp, ← hc, inv_mul_cancel_left₀ hc0]`. Use `show Algebra.trace ℚ E (a * (((m : E) * (H.rt : E))⁻¹ * S v u)) = _`. Rewrite using `[h8, htr]`. Introduce `x y show S (e x) (e y) ∈ integralClosure ℤ E`. Rewrite using `[Sapp, hc]`.

Establish `h9 : (H.rt : E) ∈ integralClosure ℤ E` using `(H.rt).isIntegral_coe`. Establish `h10` using `mul_mem h9 (hint x y)`. Use `h10 using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_hermitian_of_trace : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] (N : ℕ) (e : Λ →+ (Fin N → E)) (B : LinearMap.BilinForm ℚ (Fin N → E)), (∀ (a : E) u v, B (a • u) v = B u (IsCMField.complexConj E a • v)) → (∀ u v, B u v = - B v u) → (∀ u, (∀ v, B v u = 0) → u = 0) → ∃ (h : HermitianForm (maximalRealSubfield E) E (Fin N → E)) (m : ℕ), m ≠ 0 ∧ (∀ (a : E) u v, Algebra.trace ℚ E (a * (((m : E) * (H.rt : E))⁻¹ * h.toSesq v u)) = B (a • u) v) ∧ ∀ x y, h.toSesq (e x) (e y) ∈ integralClosure ℤ E := by
  intro E _ _ _ H Λ _ _ N e B hadj hskew hnd
  obtain ⟨h₁, ⟨htr, hadd1, hadd2, hsm1, hsm2⟩, -⟩ :=
    GlobalTheory.CompanionTheory.Ar.Flat.existsUnique_sesq_of_trace E (Fin N → E) B hadj
  have hsk := sesq_skew B hadj hskew h₁ htr
  obtain ⟨m, hm0, hint⟩ := exists_nat_integral (fun x y : Λ => h₁ (e y) (e x))
    (fun x x' y => by rw [map_add, hadd2]) (fun x y y' => by rw [map_add, hadd1])
  have hrt0 : (H.rt : E) ≠ 0 := by
    intro h0
    have hsq : (H.rt : E) ^ 2 = -(H.d : E) := by
      have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
      simpa using this
    rw [h0] at hsq
    have hd : (H.d : E) ≠ 0 := Nat.cast_ne_zero.2 H.d_prime.ne_zero
    apply hd
    linear_combination hsq
  set c : E := (m : E) * (H.rt : E) with hc
  have hc0 : c ≠ 0 := mul_ne_zero (Nat.cast_ne_zero.2 hm0) hrt0
  have htc : IsCMField.complexConj E c = -c := by
    rw [hc, map_mul, map_natCast, complexConj_rt]
    ring
  let S : (Fin N → E) →ₛₗ[conjHom (maximalRealSubfield E) E] (Fin N → E) →ₗ[E] E :=
    LinearMap.mk₂'ₛₗ (conjHom (maximalRealSubfield E) E) (RingHom.id E) (fun v u => c * h₁ u v)
      (fun v v' u => by rw [hadd2, mul_add])
      (fun a v u => by
        rw [hsm2, smul_eq_mul]
        have : conjHom (maximalRealSubfield E) E a = IsCMField.complexConj E a :=
          quadConj_eq_complexConj a
        rw [this]
        ring)
      (fun v u u' => by rw [hadd1, mul_add])
      (fun a v u => by
        rw [hsm1, RingHom.id_apply, smul_eq_mul]
        ring)
  have Sapp : ∀ v u, S v u = c * h₁ u v := fun _ _ => rfl
  have hinj : Function.Injective S := by
    intro v v' hvv
    have hz : ∀ w, h₁ w (v - v') = 0 := by
      intro w
      have h3 : c * h₁ w v = c * h₁ w v' := by
        rw [← Sapp, ← Sapp, hvv]
      have h4 := mul_left_cancel₀ hc0 h3
      have h5 := hadd2 w (v - v') v'
      rw [sub_add_cancel, h4] at h5
      linear_combination -h5
    have : v - v' = 0 := hnd _ fun w => by
      have h6 := htr w (v - v') 1
      rw [one_smul, hz, mul_zero, map_zero] at h6
      exact h6.symm
    exact sub_eq_zero.1 this
  have hsurj : Function.Surjective S := by
    let g0 : (Fin N → E) →+ (Fin N → E) := AddMonoidHom.mk' (fun u i => S u (Pi.single i 1))
      (fun a b => by
        funext i
        show S (a + b) (Pi.single i 1) = S a (Pi.single i 1) + S b (Pi.single i 1)
        rw [Sapp, Sapp, Sapp, hadd2, mul_add])
    let g : (Fin N → E) →ₗ[ℚ] (Fin N → E) := g0.toRatLinearMap
    have gapp : ∀ u i, g u i = S u (Pi.single i 1) := fun _ _ => rfl
    have ginj : Function.Injective g := by
      rw [injective_iff_map_eq_zero]
      intro u hu
      have : S u = S 0 := by
        apply (Pi.basisFun E (Fin N)).ext
        intro i
        rw [Pi.basisFun_apply, map_zero, ← gapp, hu]
        rfl
      exact hinj (this.trans (by rw [map_zero]) |>.trans (map_zero S).symm)
    have gsurj : Function.Surjective g := LinearMap.injective_iff_surjective.1 ginj
    intro f
    obtain ⟨u, hu⟩ := gsurj fun i => f (Pi.single i 1)
    refine ⟨u, (Pi.basisFun E (Fin N)).ext fun i => ?_⟩
    rw [Pi.basisFun_apply, ← gapp, hu]
  refine ⟨⟨S, ⟨fun x y => ?_⟩, hinj, hsurj⟩, m, hm0, ?_, ?_⟩
  · have h7 : conjHom (maximalRealSubfield E) E (S x y) = IsCMField.complexConj E (S x y) :=
      quadConj_eq_complexConj _
    rw [h7, Sapp, Sapp, map_mul, htc, hsk y x]
    ring
  · intro a u v
    have h8 : ((m : E) * (H.rt : E))⁻¹ * S v u = h₁ u v := by
      rw [Sapp, ← hc, inv_mul_cancel_left₀ hc0]
    show Algebra.trace ℚ E (a * (((m : E) * (H.rt : E))⁻¹ * S v u)) = _
    rw [h8, htr]
  · intro x y
    show S (e x) (e y) ∈ integralClosure ℤ E
    rw [Sapp, hc]
    have h9 : (H.rt : E) ∈ integralClosure ℤ E := (H.rt).isIntegral_coe
    have h10 := mul_mem h9 (hint x y)
    convert h10 using 1
    ring

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.HermTrace
