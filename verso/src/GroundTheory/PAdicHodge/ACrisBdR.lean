import Mathlib
import GroundTheory.PAdicHodge.FactorizationFactorialLe
import GroundTheory.PAdicHodge.BdRLattice
import GroundTheory.PowerSubgroups.CountableNeighbourhoods.PrecompleteOfSurjective

noncomputable section

namespace GroundTheory.PAdicHodge

open _root_.WittVector

namespace ACris

section Span

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]

local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)

def dpowSpan (ξ : AInf K p) : Submodule (AInf K p) 𝔸 :=
  Submodule.span (AInf K p) (Set.range fun n => dpow n ξ)

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨n, rfl⟩`.
-/
theorem dpow_mem_dpowSpan (ξ : AInf K p) (n : ℕ) : dpow n ξ ∈ dpowSpan ξ :=
  Submodule.subset_span ⟨n, rfl⟩

/- English proof (translation)
Rewrite using `[← dpow_zero ξ]`. Conclude with `dpow_mem_dpowSpan ξ 0`.
-/
theorem one_mem_dpowSpan (ξ : AInf K p) : (1 : 𝔸) ∈ dpowSpan ξ := by
  rw [← dpow_zero ξ]
  exact dpow_mem_dpowSpan ξ 0

/- English proof (translation)
Establish `h : dpowSpan ξ * dpowSpan ξ ≤ dpowSpan ξ`. Rewrite using `[dpowSpan, Submodule.span_mul_span, Submodule.span_le]`. Introduce and unpack `_ ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩`. Use `show dpow i ξ * dpow j ξ ∈ _`. Rewrite using `[dpow_mul_dpow, ← nsmul_eq_mul]`.

Conclude with `Submodule.smul_of_tower_mem _ _ (dpow_mem_dpowSpan ξ (i + j))`. Conclude with `h (Submodule.mul_mem_mul ha hb)`.
-/
theorem mul_mem_dpowSpan (ξ : AInf K p) {a b : 𝔸} (ha : a ∈ dpowSpan ξ) (hb : b ∈ dpowSpan ξ) :
    a * b ∈ dpowSpan ξ := by
  have h : dpowSpan ξ * dpowSpan ξ ≤ dpowSpan ξ := by
    rw [dpowSpan, Submodule.span_mul_span, Submodule.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
    show dpow i ξ * dpow j ξ ∈ _
    rw [dpow_mul_dpow, ← nsmul_eq_mul]
    exact Submodule.smul_of_tower_mem _ _ (dpow_mem_dpowSpan ξ (i + j))
  exact h (Submodule.mul_mem_mul ha hb)

/- English proof (translation)
Set `S : Subalgebra (AInf K p) 𝔸` to `(dpowSpan ξ).toSubalgebra (one_mem_dpowSpan ξ) (fun _ _ ha hb => mul_mem_dpowSpan ξ ha hb)`. Establish `h : ACrisZero K p ≤ S`. Rewrite using `[acrisZero_eq_adjoin hξ]`. Apply `Algebra.adjoin_le` to reduce the goal to its premises. Introduce and unpack `_ ⟨n, rfl⟩`.

Conclude with `dpow_mem_dpowSpan ξ n`. Conclude with `h hy`.
-/
theorem mem_dpowSpan {ξ : AInf K p} (hξ : RingHom.ker θ = Ideal.span {ξ}) {y : 𝔸}
    (hy : y ∈ ACrisZero K p) : y ∈ dpowSpan ξ := by
  let S : Subalgebra (AInf K p) 𝔸 := (dpowSpan ξ).toSubalgebra (one_mem_dpowSpan ξ)
    (fun _ _ ha hb => mul_mem_dpowSpan ξ ha hb)
  have h : ACrisZero K p ≤ S := by
    rw [acrisZero_eq_adjoin hξ]
    apply Algebra.adjoin_le
    rintro _ ⟨n, rfl⟩
    exact dpow_mem_dpowSpan ξ n
  exact h hy

/- English proof (translation)
Establish `hξm : ξ ∈ RingHom.ker θ` using `hξ ▸ Ideal.mem_span_singleton_self ξ`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨n, rfl⟩` from `hx`. Use `show ∃ y' ∈ ACrisZero K p, ∃ w : AInf K p, ∃ r : 𝔸, ((m - 1).factorial : 𝔸) * y' = algebraMap (AInf K p) 𝔸 w ∧ dpow n ξ = y' + algebraMap (AInf K p) 𝔸 (ξ ^ m) * r`.

Distinguish the cases in `hn : n < m`. Use `⟨dpow n ξ, dpow_mem hξm n, (((m - 1).factorial / n.factorial : ℕ) : AInf K p) * ξ ^ n, 0, ?_, by simp⟩` and prove the remaining obligations. Establish `hdvd : n.factorial ∣ (m - 1).factorial` using `Nat.factorial_dvd_factorial (by omega)`. Rewrite using `[map_mul, map_natCast, map_pow, ← factorial_mul_dpow, ← mul_assoc, ← Nat.cast_mul, Nat.div_mul_cancel hdvd]`. Use `⟨0, zero_mem _, 0, Ring.inverse (n.factorial : 𝔸) * algebraMap (AInf K p) 𝔸 ξ ^ (n - m), by simp, ?_⟩` and prove the remaining obligations.

Rewrite using `[zero_add, show dpow n ξ = Ring.inverse (n.factorial : 𝔸) * algebraMap (AInf K p) 𝔸 ξ ^ n from rfl, map_pow, ← mul_assoc, mul_comm (algebraMap (AInf K p) 𝔸 ξ ^ m), mul_assoc, ← pow_add, Nat.add_sub_cancel' (not_lt.1 hn)]`. Consider the case `zero => exact ⟨0, zero_mem _, 0, 0, by simp, by simp⟩`. Consider the case `add x z _ _ hx hz`. Take `⟨x', hx', wx, rx, hwx, hrx⟩` from `hx`. Take `⟨z', hz', wz, rz, hwz, hrz⟩` from `hz`.

Conclude with `⟨x' + z', add_mem hx' hz', wx + wz, rx + rz, by rw [mul_add, hwx, hwz, map_add], by rw [hrx, hrz]; ring⟩`. Consider the case `smul a x _ hx`. Take `⟨x', hx', wx, rx, hwx, hrx⟩` from `hx`. Use `⟨algebraMap (AInf K p) 𝔸 a * x', Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ a) hx', a * wx, algebraMap (AInf K p) 𝔸 a * rx, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, ← hwx]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Algebra.smul_def, hrx]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_decomp_of_mem_dpowSpan {ξ : AInf K p} (hξ : RingHom.ker θ = Ideal.span {ξ}) (m : ℕ)
    {y : 𝔸} (hy : y ∈ dpowSpan ξ) :
    ∃ y' ∈ ACrisZero K p, ∃ w : AInf K p, ∃ r : 𝔸,
      ((m - 1).factorial : 𝔸) * y' = algebraMap (AInf K p) 𝔸 w ∧
        y = y' + algebraMap (AInf K p) 𝔸 (ξ ^ m) * r := by
  have hξm : ξ ∈ RingHom.ker θ := hξ ▸ Ideal.mem_span_singleton_self ξ
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨n, rfl⟩ := hx
    show ∃ y' ∈ ACrisZero K p, ∃ w : AInf K p, ∃ r : 𝔸,
      ((m - 1).factorial : 𝔸) * y' = algebraMap (AInf K p) 𝔸 w ∧
        dpow n ξ = y' + algebraMap (AInf K p) 𝔸 (ξ ^ m) * r
    by_cases hn : n < m
    · refine ⟨dpow n ξ, dpow_mem hξm n, (((m - 1).factorial / n.factorial : ℕ) : AInf K p) * ξ ^ n,
        0, ?_, by simp⟩
      have hdvd : n.factorial ∣ (m - 1).factorial := Nat.factorial_dvd_factorial (by omega)
      rw [map_mul, map_natCast, map_pow, ← factorial_mul_dpow, ← mul_assoc, ← Nat.cast_mul,
        Nat.div_mul_cancel hdvd]
    · refine ⟨0, zero_mem _, 0, Ring.inverse (n.factorial : 𝔸) *
        algebraMap (AInf K p) 𝔸 ξ ^ (n - m), by simp, ?_⟩
      rw [zero_add, show dpow n ξ = Ring.inverse (n.factorial : 𝔸) * algebraMap (AInf K p) 𝔸 ξ ^ n
        from rfl, map_pow, ← mul_assoc, mul_comm (algebraMap (AInf K p) 𝔸 ξ ^ m),
        mul_assoc, ← pow_add, Nat.add_sub_cancel' (not_lt.1 hn)]
  | zero => exact ⟨0, zero_mem _, 0, 0, by simp, by simp⟩
  | add x z _ _ hx hz =>
    obtain ⟨x', hx', wx, rx, hwx, hrx⟩ := hx
    obtain ⟨z', hz', wz, rz, hwz, hrz⟩ := hz
    exact ⟨x' + z', add_mem hx' hz', wx + wz, rx + rz, by rw [mul_add, hwx, hwz, map_add],
      by rw [hrx, hrz]; ring⟩
  | smul a x _ hx =>
    obtain ⟨x', hx', wx, rx, hwx, hrx⟩ := hx
    refine ⟨algebraMap (AInf K p) 𝔸 a * x', Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ a) hx',
      a * wx, algebraMap (AInf K p) 𝔸 a * rx, ?_, ?_⟩
    · rw [map_mul, ← hwx]; ring
    · rw [Algebra.smul_def, hrx]; ring

/- English proof (translation)
The claim follows from `exists_decomp_of_mem_dpowSpan hξ m (mem_dpowSpan hξ hy)`.
-/
theorem exists_decomp {ξ : AInf K p} (hξ : RingHom.ker θ = Ideal.span {ξ}) (m : ℕ) {y : 𝔸}
    (hy : y ∈ ACrisZero K p) :
    ∃ y' ∈ ACrisZero K p, ∃ w : AInf K p, ∃ r : 𝔸,
      ((m - 1).factorial : 𝔸) * y' = algebraMap (AInf K p) 𝔸 w ∧
        y = y' + algebraMap (AInf K p) 𝔸 (ξ ^ m) * r :=
  exists_decomp_of_mem_dpowSpan hξ m (mem_dpowSpan hξ hy)

end Span

section Complete

variable {Q : Type*} [CommRing Q] (p : ℕ)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨s, rfl⟩`. Conclude with `⟨s, s.2, by simp⟩`. Introduce and unpack `⟨s, hs, h⟩`. Conclude with `⟨⟨s, hs⟩, Subtype.ext (by simpa using h)⟩`.
-/
theorem subring_pow_dvd_iff {S : Subring Q} (n : ℕ) (x : S) :
    (p : S) ^ n ∣ x ↔ ∃ s ∈ S, (x : Q) = (p : Q) ^ n * s := by
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨s, s.2, by simp⟩
  · rintro ⟨s, hs, h⟩
    exact ⟨⟨s, hs⟩, Subtype.ext (by simpa using h)⟩

/- English proof (translation)
Rewrite using `[Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`.
-/
private theorem mem_span_singleton_pow_smul_top {R : Type*} [CommRing R] (x y : R) (n : ℕ) :
    y ∈ (Ideal.span {x} ^ n • ⊤ : Submodule R R) ↔ x ^ n ∣ y := by
  rw [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

/- English proof (translation)
Use `first`. Consider the case `exact GroundTheory.Variant₂.N1.isPrecomplete_of_surjective ..`. Consider the case `(apply GroundTheory.Variant₂.N1.isPrecomplete_of_surjective <;> assumption)`.
-/
theorem isPrecomplete_of_surjective {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : Function.Surjective f) (a : A) [IsPrecomplete (Ideal.span {a}) A] :
    IsPrecomplete (Ideal.span {f a}) B := by
  first
  | exact GroundTheory.Variant₂.N1.isPrecomplete_of_surjective ..
  | (apply GroundTheory.Variant₂.N1.isPrecomplete_of_surjective <;> assumption)

/- English proof (translation)
Establish `hpv : IsUnit ((p : Q) ^ v)` using `hp.pow v`. Establish `haus : IsHausdorff (Ideal.span {(p : S)}) S`. Use `⟨fun x hx => ?_⟩` and prove the remaining obligations. Simplify using `only [smodEq_span_singleton_pow_iff, sub_zero] at hx`. Set `y : T` to `⟨(p : Q) ^ v * x, hv x x.2⟩`.

Establish `hy : y = 0`. Use `IsHausdorff.haus' (I := Ideal.span {(p : T)}) y fun n => ?_` and prove the remaining obligations. Rewrite using `[smodEq_span_singleton_pow_iff, sub_zero, subring_pow_dvd_iff]`. Take `⟨s, hs, h⟩` from `(subring_pow_dvd_iff p n x).1 (hx n)`. Conclude with `⟨(p : Q) ^ v * s, hv s hs, by simp only [y]; rw [h]; ring⟩`.

Apply `Subtype.ext` to reduce the goal to its premises. Establish `h0 : (p : Q) ^ v * x = 0` using `congrArg Subtype.val hy`. Simplify using `using (hpv.mul_right_eq_zero).1 h0`. Establish `prec : IsPrecomplete (Ideal.span {(p : S)}) S`. Use `⟨fun f hf => ?_⟩` and prove the remaining obligations.

Simplify using `only [smodEq_span_singleton_pow_iff] at hf ⊢`. Set `g : ℕ → T` to `fun k => ⟨(p : Q) ^ v * f k, hv _ (f k).2⟩`. Establish `hg : ∀ {m n}, m ≤ n → g m ≡ g n [SMOD (Ideal.span {(p : T)} ^ m • ⊤ : Submodule T T)]` using `fun {m n} hmn => by`. Rewrite using `[smodEq_span_singleton_pow_iff, subring_pow_dvd_iff]`. Take `⟨s, hs, h⟩` from `(subring_pow_dvd_iff p m _).1 (hf hmn)`.

Use `⟨(p : Q) ^ v * s, hv s hs, ?_⟩` and prove the remaining obligations. Simplify using `only [g]`. Move the coercions through the operations in `at h ⊢`. Rewrite using `[← mul_sub, h]`. Expand and normalize the polynomial expressions, which then agree.

Take `⟨LT, hLT⟩` from `IsPrecomplete.prec (I := Ideal.span {(p : T)}) inferInstance hg`. Establish `hLT' : ∀ k, ∃ t ∈ T, (p : Q) ^ v * f k - LT = (p : Q) ^ k * t` using `fun k => by`. Take `⟨t, ht, h⟩` from `(subring_pow_dvd_iff p k _).1 ((smodEq_span_singleton_pow_iff _ _ _ _).1 (hLT k))`. Conclude with `⟨t, ht, by simpa [g] using h⟩`. Take `⟨tv, htv, hv'⟩` from `hLT' v`.

Establish `hL : (f v : Q) - tv ∈ S` using `sub_mem (f v).2 (hTS htv)`. Use `⟨⟨(f v : Q) - tv, hL⟩, fun k => ?_⟩` and prove the remaining obligations. Rewrite using `[subring_pow_dvd_iff]`. Take `⟨t, ht, h⟩` from `hLT' (k + v)`. Take `⟨s, hs, hs'⟩` from `(subring_pow_dvd_iff p k _).1 (hf (Nat.le_add_right k v))`.

Use `⟨s + t, add_mem hs (hTS ht), ?_⟩` and prove the remaining obligations. Establish `e1 : (p : Q) ^ v * ((f (k + v) : Q) - ((f v : Q) - tv)) = (p : Q) ^ v * ((p : Q) ^ k * t)`. Take the linear combination `h - hv'`. Establish `e2 : (f (k + v) : Q) - ((f v : Q) - tv) = (p : Q) ^ k * t` using `hpv.mul_left_cancel e1`. Move the coercions through the operations in `at hs' ⊢`.

Take the linear combination `hs' + e2`. Conclude with `⟨⟩`.
-/
theorem isAdicComplete_of_pow_mul_mem {T S : Subring Q} (hTS : T ≤ S) (hp : IsUnit (p : Q)) (v : ℕ)
    (hv : ∀ s ∈ S, (p : Q) ^ v * s ∈ T) [hT : IsAdicComplete (Ideal.span {(p : T)}) T] :
    IsAdicComplete (Ideal.span {(p : S)}) S := by
  have hpv : IsUnit ((p : Q) ^ v) := hp.pow v

  have haus : IsHausdorff (Ideal.span {(p : S)}) S := by
    refine ⟨fun x hx => ?_⟩
    simp only [smodEq_span_singleton_pow_iff, sub_zero] at hx
    let y : T := ⟨(p : Q) ^ v * x, hv x x.2⟩
    have hy : y = 0 := by
      refine IsHausdorff.haus' (I := Ideal.span {(p : T)}) y fun n => ?_
      rw [smodEq_span_singleton_pow_iff, sub_zero, subring_pow_dvd_iff]
      obtain ⟨s, hs, h⟩ := (subring_pow_dvd_iff p n x).1 (hx n)
      exact ⟨(p : Q) ^ v * s, hv s hs, by simp only [y]; rw [h]; ring⟩
    apply Subtype.ext
    have h0 : (p : Q) ^ v * x = 0 := congrArg Subtype.val hy
    simpa using (hpv.mul_right_eq_zero).1 h0

  have prec : IsPrecomplete (Ideal.span {(p : S)}) S := by
    refine ⟨fun f hf => ?_⟩
    simp only [smodEq_span_singleton_pow_iff] at hf ⊢
    let g : ℕ → T := fun k => ⟨(p : Q) ^ v * f k, hv _ (f k).2⟩
    have hg : ∀ {m n}, m ≤ n → g m ≡ g n [SMOD (Ideal.span {(p : T)} ^ m • ⊤ : Submodule T T)] :=
      fun {m n} hmn => by
        rw [smodEq_span_singleton_pow_iff, subring_pow_dvd_iff]
        obtain ⟨s, hs, h⟩ := (subring_pow_dvd_iff p m _).1 (hf hmn)
        refine ⟨(p : Q) ^ v * s, hv s hs, ?_⟩
        simp only [g]
        push_cast at h ⊢
        rw [← mul_sub, h]; ring
    obtain ⟨LT, hLT⟩ := IsPrecomplete.prec (I := Ideal.span {(p : T)}) inferInstance hg
    have hLT' : ∀ k, ∃ t ∈ T, (p : Q) ^ v * f k - LT = (p : Q) ^ k * t := fun k => by
      obtain ⟨t, ht, h⟩ := (subring_pow_dvd_iff p k _).1
        ((smodEq_span_singleton_pow_iff _ _ _ _).1 (hLT k))
      exact ⟨t, ht, by simpa [g] using h⟩
    obtain ⟨tv, htv, hv'⟩ := hLT' v

    have hL : (f v : Q) - tv ∈ S := sub_mem (f v).2 (hTS htv)
    refine ⟨⟨(f v : Q) - tv, hL⟩, fun k => ?_⟩
    rw [subring_pow_dvd_iff]
    obtain ⟨t, ht, h⟩ := hLT' (k + v)
    obtain ⟨s, hs, hs'⟩ := (subring_pow_dvd_iff p k _).1 (hf (Nat.le_add_right k v))
    refine ⟨s + t, add_mem hs (hTS ht), ?_⟩
    have e1 : (p : Q) ^ v * ((f (k + v) : Q) - ((f v : Q) - tv)) =
        (p : Q) ^ v * ((p : Q) ^ k * t) := by
      linear_combination h - hv'
    have e2 : (f (k + v) : Q) - ((f v : Q) - tv) = (p : Q) ^ k * t := hpv.mul_left_cancel e1
    push_cast at hs' ⊢
    linear_combination hs' + e2
  exact ⟨⟩

end Complete

section ExtendComp

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]

/- English proof (translation)
Apply `DFunLike.coe_injective` to reduce the goal to its premises. Use `IsHausdorff.funext' I' fun n x => ?_` and prove the remaining obligations. Take `⟨a, ha⟩` from `Ideal.Quotient.mk_surjective (_root_.AdicCompletion.evalₐ J n x)`. Establish `h1 : Ideal.Quotient.mk (I ^ n) (AdicCompletion.extendRingHom J I f hf x) = Ideal.Quotient.mk (I ^ n) (f a)`. Rewrite using `[AdicCompletion.mk_extendRingHom, ← ha, Ideal.quotientMap_mk]`.

Establish `h2` using `Ideal.Quotient.eq.1 h1`. Establish `h3 : g (AdicCompletion.extendRingHom J I f hf x) - g (f a) ∈ I' ^ n`. Rewrite using `[← map_sub]`. Conclude with `(Ideal.pow_right_mono hg n).trans (Ideal.le_comap_pow g n) h2`. Rewrite using `[RingHom.coe_comp, Function.comp_apply, AdicCompletion.mk_extendRingHom, ← ha, Ideal.quotientMap_mk, Ideal.Quotient.eq.2 h3]`.

Both sides reduce to the same expression.
-/
theorem _root_.GroundTheory.PAdicHodge.AdicCompletion.extendRingHom_comp (J : Ideal A) (I : Ideal B)
    (I' : Ideal C) [IsAdicComplete I B] [IsAdicComplete I' C] (f : A →+* B) (hf : J ≤ I.comap f)
    (g : B →+* C) (hg : I ≤ I'.comap g) :
    g.comp (AdicCompletion.extendRingHom J I f hf) =
      AdicCompletion.extendRingHom J I' (g.comp f)
        (hf.trans (by rw [← Ideal.comap_comap]; exact Ideal.comap_mono hg)) := by
  apply DFunLike.coe_injective
  refine IsHausdorff.funext' I' fun n x => ?_
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (_root_.AdicCompletion.evalₐ J n x)
  have h1 : Ideal.Quotient.mk (I ^ n) (AdicCompletion.extendRingHom J I f hf x) =
      Ideal.Quotient.mk (I ^ n) (f a) := by
    rw [AdicCompletion.mk_extendRingHom, ← ha, Ideal.quotientMap_mk]
  have h2 := Ideal.Quotient.eq.1 h1
  have h3 : g (AdicCompletion.extendRingHom J I f hf x) - g (f a) ∈ I' ^ n := by
    rw [← map_sub]
    exact (Ideal.pow_right_mono hg n).trans (Ideal.le_comap_pow g n) h2
  rw [RingHom.coe_comp, Function.comp_apply, AdicCompletion.mk_extendRingHom, ← ha,
    Ideal.quotientMap_mk, Ideal.Quotient.eq.2 h3]
  rfl

end ExtendComp

section Quot

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p] [CharZero K]

local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)

variable (K p) in

abbrev kerAway : Ideal 𝔸 := RingHom.ker (fontaineThetaInvertP (normInteger K) p)

variable (K p) in

abbrev xiGen : AInf K p := IsPerfectoidField.kerThetaGenerator K p

/- English proof (translation)
The claim follows from `IsPerfectoidField.ker_fontaineTheta_eq_span_kerThetaGenerator K p`.
-/
theorem ker_eq_span_xiGen : RingHom.ker θ = Ideal.span {xiGen K p} :=
  IsPerfectoidField.ker_fontaineTheta_eq_span_kerThetaGenerator K p

/- English proof (translation)
Rewrite using `[kerAway, ker_fontaineThetaInvertP ker_eq_span_xiGen, Ideal.span_singleton_pow, map_pow]`.
-/
theorem kerAway_pow (m : ℕ) :
    kerAway K p ^ m = Ideal.span {algebraMap (AInf K p) 𝔸 (xiGen K p ^ m)} := by
  rw [kerAway, ker_fontaineThetaInvertP ker_eq_span_xiGen, Ideal.span_singleton_pow, map_pow]

/- English proof (translation)
Rewrite using `[Ideal.Quotient.eq_zero_iff_mem, kerAway_pow, Ideal.mem_span_singleton]`.
-/
theorem mk_eq_zero_iff (m : ℕ) (a : 𝔸) :
    Ideal.Quotient.mk (kerAway K p ^ m) a = 0 ↔ algebraMap (AInf K p) 𝔸 (xiGen K p ^ m) ∣ a := by
  rw [Ideal.Quotient.eq_zero_iff_mem, kerAway_pow, Ideal.mem_span_singleton]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Take `⟨s, hs⟩` from `IsPerfectoidField.exists_p_pow_mul_mem_of_dvd h`. Conclude with `IsPerfectoidField.mem_span_xi_pow_of_p_pow_mul_mem ker_eq_span_xiGen hs`. Introduce `h`.

Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton.1 h`. Rewrite using `[map_mul]`. Conclude with `dvd_mul_right _ _`.
-/
theorem algebraMap_dvd_iff (m : ℕ) (w : AInf K p) :
    algebraMap (AInf K p) 𝔸 (xiGen K p ^ m) ∣ algebraMap (AInf K p) 𝔸 w ↔
      w ∈ Ideal.span {xiGen K p ^ m} := by
  constructor
  · intro h
    obtain ⟨s, hs⟩ := IsPerfectoidField.exists_p_pow_mul_mem_of_dvd h
    exact IsPerfectoidField.mem_span_xi_pow_of_p_pow_mul_mem ker_eq_span_xiGen hs
  · intro h
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.1 h
    rw [map_mul]
    exact dvd_mul_right _ _

variable (K p) in

def latticeQ (m : ℕ) : Subring (𝔸 ⧸ kerAway K p ^ m) :=
  ((Ideal.Quotient.mk (kerAway K p ^ m)).comp (algebraMap (AInf K p) 𝔸)).range

variable (K p) in

def acrisQ (m : ℕ) : Subring (𝔸 ⧸ kerAway K p ^ m) :=
  (ACrisZero K p).toSubring.map (Ideal.Quotient.mk (kerAway K p ^ m))

/- English proof (translation)
Assemble the required witnesses or components as `⟨y, hy, rfl⟩`.
-/
theorem mk_mem_acrisQ (m : ℕ) {y : 𝔸} (hy : y ∈ ACrisZero K p) :
    Ideal.Quotient.mk (kerAway K p ^ m) y ∈ acrisQ K p m :=
  ⟨y, hy, rfl⟩

/- English proof (translation)
Introduce and unpack `_ ⟨w, rfl⟩`. Conclude with `mk_mem_acrisQ m (Subalgebra.algebraMap_mem _ w)`.
-/
theorem latticeQ_le (m : ℕ) : latticeQ K p m ≤ acrisQ K p m := by
  rintro _ ⟨w, rfl⟩
  exact mk_mem_acrisQ m (Subalgebra.algebraMap_mem _ w)

/- English proof (translation)
Use `(isUnit_natCast (K := K) (p := p) hp.out.ne_zero).map (Ideal.Quotient.mk (kerAway K p ^ m))` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis.
-/
theorem isUnit_p_quot (m : ℕ) : IsUnit (p : 𝔸 ⧸ kerAway K p ^ m) := by
  have := (isUnit_natCast (K := K) (p := p) hp.out.ne_zero).map (Ideal.Quotient.mk (kerAway K p ^ m))
  rwa [map_natCast] at this

/- English proof (translation)
Introduce and unpack `_ ⟨y, hy, rfl⟩`. Take `⟨y', -, w, r, hw, rfl⟩` from `exists_decomp ker_eq_span_xiGen m hy`. Use `set v := (m - 1).factorial.factorization p`. Establish `hcop : (ordCompl[p] (m - 1).factorial).Coprime p` using `Nat.coprime_comm.mp (Nat.coprime_ordCompl hp.out (Nat.factorial_ne_zero _))`. Establish `hu` using `WittVector.isUnit_natCast_of_coprime (R := PreTilt (normInteger K) p) hcop`.

Use `⟨↑hu.unit⁻¹ * w, ?_⟩` and prove the remaining obligations. Establish `hfac : ((p : 𝔸) ^ v * ((ordCompl[p] (m - 1).factorial : ℕ) : 𝔸)) = ((m - 1).factorial : 𝔸)`. Rewrite using `[← Nat.cast_pow, ← Nat.cast_mul, Nat.ordProj_mul_ordCompl_eq_self]`. Establish `hinv : algebraMap (AInf K p) 𝔸 ↑hu.unit⁻¹ * ((ordCompl[p] (m - 1).factorial : ℕ) : 𝔸) = 1`. Rewrite using `[← map_natCast (algebraMap (AInf K p) 𝔸), ← map_mul, mul_comm, IsUnit.mul_val_inv, map_one]`.

Establish `hz : Ideal.Quotient.mk (kerAway K p ^ m) (algebraMap (AInf K p) 𝔸 (xiGen K p ^ m) * r) = 0`. Rewrite using `[mk_eq_zero_iff]`. Conclude with `dvd_mul_right _ _`. Establish `hcalc : algebraMap (AInf K p) 𝔸 (↑hu.unit⁻¹ * w) = (p : 𝔸) ^ v * y'`. Rewrite using `[map_mul]`.

Combine the equalities or inequalities in the displayed calculation. Use `show Ideal.Quotient.mk _ (algebraMap (AInf K p) 𝔸 (↑hu.unit⁻¹ * w)) = _`. Rewrite using `[hcalc, map_mul, map_pow, map_natCast, map_add, hz, add_zero]`.
-/
theorem pow_mul_mem_latticeQ (m : ℕ) :
    ∀ s ∈ acrisQ K p m, (p : 𝔸 ⧸ kerAway K p ^ m) ^ ((m - 1).factorial.factorization p) * s ∈
      latticeQ K p m := by
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨y', -, w, r, hw, rfl⟩ := exists_decomp ker_eq_span_xiGen m hy
  set v := (m - 1).factorial.factorization p
  have hcop : (ordCompl[p] (m - 1).factorial).Coprime p :=
    Nat.coprime_comm.mp (Nat.coprime_ordCompl hp.out (Nat.factorial_ne_zero _))
  have hu := WittVector.isUnit_natCast_of_coprime (R := PreTilt (normInteger K) p) hcop
  refine ⟨↑hu.unit⁻¹ * w, ?_⟩
  have hfac : ((p : 𝔸) ^ v * ((ordCompl[p] (m - 1).factorial : ℕ) : 𝔸)) = ((m - 1).factorial : 𝔸) := by
    rw [← Nat.cast_pow, ← Nat.cast_mul, Nat.ordProj_mul_ordCompl_eq_self]
  have hinv : algebraMap (AInf K p) 𝔸 ↑hu.unit⁻¹ * ((ordCompl[p] (m - 1).factorial : ℕ) : 𝔸) = 1 := by
    rw [← map_natCast (algebraMap (AInf K p) 𝔸), ← map_mul, mul_comm, IsUnit.mul_val_inv, map_one]
  have hz : Ideal.Quotient.mk (kerAway K p ^ m) (algebraMap (AInf K p) 𝔸 (xiGen K p ^ m) * r) = 0 := by
    rw [mk_eq_zero_iff]; exact dvd_mul_right _ _
  have hcalc : algebraMap (AInf K p) 𝔸 (↑hu.unit⁻¹ * w) = (p : 𝔸) ^ v * y' := by
    rw [map_mul]
    calc algebraMap (AInf K p) 𝔸 ↑hu.unit⁻¹ * algebraMap (AInf K p) 𝔸 w
        = algebraMap (AInf K p) 𝔸 ↑hu.unit⁻¹ * (((m - 1).factorial : 𝔸) * y') := by rw [hw]
      _ = (algebraMap (AInf K p) 𝔸 ↑hu.unit⁻¹ * ((ordCompl[p] (m - 1).factorial : ℕ) : 𝔸)) *
          ((p : 𝔸) ^ v * y') := by rw [← hfac]; ring
      _ = (p : 𝔸) ^ v * y' := by rw [hinv, one_mul]
  show Ideal.Quotient.mk _ (algebraMap (AInf K p) 𝔸 (↑hu.unit⁻¹ * w)) = _
  rw [hcalc, map_mul, map_pow, map_natCast, map_add, hz, add_zero]

variable (K p) in

instance isAdicComplete_latticeQ (m : ℕ) :
    IsAdicComplete (Ideal.span {(p : latticeQ K p m)}) (latticeQ K p m) := by
  set f := (Ideal.Quotient.mk (kerAway K p ^ m)).comp (algebraMap (AInf K p) 𝔸)
  haveI hprec : IsPrecomplete (Ideal.span {(p : latticeQ K p m)}) (latticeQ K p m) := by
    have := isPrecomplete_of_surjective f.rangeRestrict f.rangeRestrict_surjective (p : AInf K p)
    rwa [map_natCast] at this
  haveI haus : IsHausdorff (Ideal.span {(p : latticeQ K p m)}) (latticeQ K p m) := by
    refine ⟨fun x hx => ?_⟩
    simp only [smodEq_span_singleton_pow_iff, sub_zero] at hx
    obtain ⟨w, hw⟩ := x.2
    have hmem : ∀ n : ℕ, w ∈ Ideal.span {(p : AInf K p) ^ n} ⊔ Ideal.span {xiGen K p ^ m} := by
      intro n
      obtain ⟨s, hs, h⟩ := (subring_pow_dvd_iff p n x).1 (hx n)
      obtain ⟨wn, rfl⟩ := hs
      have h0 : f (w - (p : AInf K p) ^ n * wn) = 0 := by
        rw [map_sub, map_mul, map_pow, map_natCast, hw, h, sub_self]
      rw [RingHom.comp_apply, mk_eq_zero_iff, algebraMap_dvd_iff] at h0
      have := Submodule.add_mem_sup (Ideal.mul_mem_right wn (Ideal.span {(p : AInf K p) ^ n})
        (Ideal.mem_span_singleton_self ((p : AInf K p) ^ n))) h0
      rwa [add_sub_cancel] at this
    have := IsPerfectoidField.mem_span_xi_pow_of_forall_mem_sup ker_eq_span_xiGen hmem
    apply Subtype.ext
    rw [← hw, ZeroMemClass.coe_zero, RingHom.comp_apply, mk_eq_zero_iff]
    exact (algebraMap_dvd_iff m w).2 this
  exact ⟨⟩

variable (K p) in

instance isAdicComplete_acrisQ (m : ℕ) :
    IsAdicComplete (Ideal.span {(p : acrisQ K p m)}) (acrisQ K p m) :=
  isAdicComplete_of_pow_mul_mem p (latticeQ_le m) (isUnit_p_quot m) _ (pow_mul_mem_latticeQ m)

end Quot

section Iota

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p] [CharZero K]

local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)

variable (K p) in

def iotaZero (m : ℕ) : ACrisZero K p →+* acrisQ K p m :=
  ((Ideal.Quotient.mk (kerAway K p ^ m)).comp (ACrisZero K p).val.toRingHom).codRestrict
    (acrisQ K p m) fun y => mk_mem_acrisQ m y.2

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_iotaZero (m : ℕ) (y : ACrisZero K p) :
    (iotaZero K p m y : 𝔸 ⧸ kerAway K p ^ m) = Ideal.Quotient.mk (kerAway K p ^ m) (y : 𝔸) :=
  rfl

/- English proof (translation)
Rewrite using `[Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_natCast]`. Conclude with `Ideal.mem_span_singleton_self _`.
-/
theorem span_p_le_comap_iotaZero (m : ℕ) :
    Ideal.span {(p : ACrisZero K p)} ≤ (Ideal.span {(p : acrisQ K p m)}).comap (iotaZero K p m) := by
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_natCast]
  exact Ideal.mem_span_singleton_self _

variable (K p) in

def embedding₂ (m : ℕ) : ACris K p →+* acrisQ K p m :=
  AdicCompletion.extendRingHom _ _ (iotaZero K p m) (span_p_le_comap_iotaZero m)

variable (K p) in

def iotaQ (m : ℕ) : ACris K p →+* 𝔸 ⧸ kerAway K p ^ m :=
  (acrisQ K p m).subtype.comp (embedding₂ K p m)

/- English proof (translation)
Rewrite using `[iotaQ, RingHom.comp_apply, embedding₂, AdicCompletion.extendRingHom_of]`. Both sides reduce to the same expression.
-/
theorem iotaQ_of (m : ℕ) (y : ACrisZero K p) :
    iotaQ K p m (_root_.AdicCompletion.of _ _ y) = Ideal.Quotient.mk (kerAway K p ^ m) (y : 𝔸) := by
  rw [iotaQ, RingHom.comp_apply, embedding₂, AdicCompletion.extendRingHom_of]
  rfl

def acrisQFactor {m n : ℕ} (hle : m ≤ n) : acrisQ K p n →+* acrisQ K p m :=
  ((Ideal.Quotient.factorPow (kerAway K p) hle).comp (acrisQ K p n).subtype).codRestrict
    (acrisQ K p m) fun s => by
      obtain ⟨y, hy, hys⟩ := s.2
      rw [RingHom.comp_apply, Subring.subtype_apply, ← hys]
      exact ⟨y, hy, rfl⟩

/- English proof (translation)
Use extensionality with `y`. Both sides reduce to the same expression.
-/
theorem acrisQFactor_comp_iotaZero {m n : ℕ} (hle : m ≤ n) :
    (acrisQFactor hle).comp (iotaZero K p n) = iotaZero K p m := by
  ext y
  rfl

/- English proof (translation)
Establish `hg : Ideal.span {(p : acrisQ K p n)} ≤ (Ideal.span {(p : acrisQ K p m)}).comap (acrisQFactor (K` using `K) hle) := by`. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_natCast]`. Conclude with `Ideal.mem_span_singleton_self _`. Establish `h` using `AdicCompletion.extendRingHom_comp _ _ _ (iotaZero K p n) (span_p_le_comap_iotaZero n) (acrisQFactor hle) hg`. Simplify using `only [acrisQFactor_comp_iotaZero] at h`.

Rewrite using `[iotaQ, iotaQ, embedding₂, embedding₂, ← h]`. Both sides reduce to the same expression.
-/
theorem iotaQ_compat {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow (kerAway K p) hle).comp (iotaQ K p n) = iotaQ K p m := by
  have hg : Ideal.span {(p : acrisQ K p n)} ≤
      (Ideal.span {(p : acrisQ K p m)}).comap (acrisQFactor (K := K) hle) := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_natCast]
    exact Ideal.mem_span_singleton_self _
  have h := AdicCompletion.extendRingHom_comp _ _ _ (iotaZero K p n) (span_p_le_comap_iotaZero n)
    (acrisQFactor hle) hg
  simp only [acrisQFactor_comp_iotaZero] at h
  rw [iotaQ, iotaQ, embedding₂, embedding₂, ← h]
  rfl

variable (K p) in

def iota : ACris K p →+* BDeRhamPlus (normInteger K) p :=
  _root_.AdicCompletion.liftRingHom (kerAway K p) (iotaQ K p) fun hle => iotaQ_compat hle

/- English proof (translation)
The claim follows from `_root_.AdicCompletion.evalₐ_liftRingHom _ _ _ m y`.
-/
theorem evalₐ_iota (m : ℕ) (y : ACris K p) :
    _root_.AdicCompletion.evalₐ (kerAway K p) m (iota K p y) = iotaQ K p m y :=
  _root_.AdicCompletion.evalₐ_liftRingHom _ _ _ m y

/- English proof (translation)
Apply `_root_.AdicCompletion.ext_evalₐ` to reduce the goal to its premises. Introduce `m`. Rewrite using `[evalₐ_iota, iotaQ_of]`. Conclude with `(_root_.AdicCompletion.evalₐ_of _ m (y : 𝔸)).symm`.
-/
theorem iota_of (y : ACrisZero K p) :
    iota K p (_root_.AdicCompletion.of _ _ y) = toBDeRhamPlus (normInteger K) p (y : 𝔸) := by
  apply _root_.AdicCompletion.ext_evalₐ
  intro m
  rw [evalₐ_iota, iotaQ_of]
  exact (_root_.AdicCompletion.evalₐ_of _ m (y : 𝔸)).symm

/- English proof (translation)
Rewrite using `[AdicCompletion.algebraMap_apply, iota_of]`. Both sides reduce to the same expression.
-/
theorem iota_algebraMap (w : AInf K p) :
    iota K p (algebraMap (AInf K p) (ACris K p) w) = wittToBDeRhamPlus (normInteger K) p w := by
  rw [AdicCompletion.algebraMap_apply, iota_of]
  rfl

end Iota

end ACris

end GroundTheory.PAdicHodge
