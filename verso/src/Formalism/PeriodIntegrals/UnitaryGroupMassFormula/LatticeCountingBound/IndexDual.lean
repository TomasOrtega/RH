import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.IndexDefs

noncomputable section

open NumberField Matrix

namespace PI.UnitaryGroupMassFormula.LCG

namespace DIdx

def qI {S : Type} [CommRing S] (𝔞 : Ideal S) (a : S) : Ideal S where
  carrier := {y | ∀ c ∈ 𝔞, c * y ∈ Ideal.span {a}}
  add_mem' := by
    intro y y' hy hy' c hc
    rw [mul_add]
    exact add_mem (hy c hc) (hy' c hc)
  zero_mem' := by
    intro c _
    rw [mul_zero]
    exact zero_mem _
  smul_mem' := by
    intro r y hy c hc
    rw [smul_eq_mul, mul_left_comm]
    exact Ideal.mul_mem_left _ r (hy c hc)

def aI {K : Type} [Field K] [NumberField K] {k : ℕ} (X : Submodule (𝓞 K) (Fin k → K)) (x : Fin k → K) :
    Ideal (𝓞 K) where
  carrier := {c | c • x ∈ X}
  add_mem' := by
    intro c c' hc hc'
    rw [Set.mem_ofPred_eq, add_smul]
    exact add_mem hc hc'
  zero_mem' := by
    rw [Set.mem_ofPred_eq, zero_smul]
    exact zero_mem _
  smul_mem' := by
    intro r c hc
    rw [Set.mem_ofPred_eq, smul_eq_mul, mul_smul]
    exact X.smul_mem r hc

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem absNorm_eq_index {S : Type} [CommRing S] [IsDedekindDomain S] [Module.Free ℤ S] [Module.Finite ℤ S]
    (I : Ideal S) : Ideal.absNorm I = I.toAddSubgroup.index := rfl

/- English proof (translation)
Establish `hle : Ideal.span {a} ≤ qI 𝔞 a`. Introduce `y hy c _`. Take `⟨z, rfl⟩` from `Ideal.mem_span_singleton'.mp hy`. Rewrite using `[Ideal.mem_span_singleton']`. Conclude with `⟨c * z, by ring⟩`.

Establish `hmul : 𝔞 * qI 𝔞 a ≤ Ideal.span {a}` using `Ideal.mul_le.mpr fun r hr s hs => hs r hr`. Establish `hq0 : qI 𝔞 a ≠ ⊥`. Introduce `h`. Establish `: a ∈ qI 𝔞 a` using `hle (Ideal.mem_span_singleton_self a)`. Rewrite `this` using `[h, Ideal.mem_bot]`.

Conclude with `ha0 this`. Establish `hNq : Ideal.absNorm (qI 𝔞 a) ≠ 0` using `fun h => hq0 (Ideal.absNorm_eq_zero_iff.mp h)`. Establish `hNa : Ideal.absNorm (Ideal.span {a}) ≠ 0`. Introduce `h`. Rewrite `h` using `[Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]`.

Conclude with `ha0 h`. Establish `hN𝔞 : Ideal.absNorm 𝔞 ≠ 0` using `fun h => h𝔞 (Ideal.absNorm_eq_zero_iff.mp h)`. Establish `hrel : (Ideal.span {a}).toAddSubgroup.relIndex (qI 𝔞 a).toAddSubgroup * Ideal.absNorm (qI 𝔞 a) = Ideal.absNorm (Ideal.span {a})`. Rewrite using `[absNorm_eq_index, absNorm_eq_index]`. Conclude with `AddSubgroup.relIndex_mul_index ((Submodule.toAddSubgroup_le _ _).mpr hle)`.

Establish `hdvd : Ideal.absNorm (Ideal.span {a}) ∣ Ideal.absNorm 𝔞 * Ideal.absNorm (qI 𝔞 a)`. Use `Ideal.absNorm_dvd_absNorm_of_le hmul` as an intermediate fact. Rewrite `this` using `[map_mul]`. Then use the resulting hypothesis. Establish `hr0 : (Ideal.span {a}).toAddSubgroup.relIndex (qI 𝔞 a).toAddSubgroup ≠ 0`. Introduce `h`.

Rewrite `hrel` using `[h, zero_mul]`. Conclude with `hNa hrel.symm`. Use `⟨hle, hr0, ?_⟩` and prove the remaining obligations. Establish `h1 : (Ideal.span {a}).toAddSubgroup.relIndex (qI 𝔞 a).toAddSubgroup * Ideal.absNorm (qI 𝔞 a) ≤ Ideal.absNorm 𝔞 * Ideal.absNorm (qI 𝔞 a)`. Rewrite using `[hrel]`.

Conclude with `Nat.le_of_dvd (Nat.pos_of_ne_zero (mul_ne_zero hN𝔞 hNq)) hdvd`. Conclude with `Nat.le_of_mul_le_mul_right h1 (Nat.pos_of_ne_zero hNq)`.
-/
theorem quot_le (K : Type) [Field K] [NumberField K] (𝔞 : Ideal (𝓞 K)) (h𝔞 : 𝔞 ≠ ⊥) (a : 𝓞 K)
    (ha0 : a ≠ 0) :
    Ideal.span {a} ≤ qI 𝔞 a ∧
    (Ideal.span {a}).toAddSubgroup.relIndex (qI 𝔞 a).toAddSubgroup ≠ 0 ∧
    (Ideal.span {a}).toAddSubgroup.relIndex (qI 𝔞 a).toAddSubgroup ≤ Ideal.absNorm 𝔞 := by
  have hle : Ideal.span {a} ≤ qI 𝔞 a := by
    intro y hy c _
    obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    rw [Ideal.mem_span_singleton']
    exact ⟨c * z, by ring⟩
  have hmul : 𝔞 * qI 𝔞 a ≤ Ideal.span {a} := Ideal.mul_le.mpr fun r hr s hs => hs r hr
  have hq0 : qI 𝔞 a ≠ ⊥ := by
    intro h
    have : a ∈ qI 𝔞 a := hle (Ideal.mem_span_singleton_self a)
    rw [h, Ideal.mem_bot] at this
    exact ha0 this
  have hNq : Ideal.absNorm (qI 𝔞 a) ≠ 0 := fun h => hq0 (Ideal.absNorm_eq_zero_iff.mp h)
  have hNa : Ideal.absNorm (Ideal.span {a}) ≠ 0 := by
    intro h
    rw [Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot] at h
    exact ha0 h
  have hN𝔞 : Ideal.absNorm 𝔞 ≠ 0 := fun h => h𝔞 (Ideal.absNorm_eq_zero_iff.mp h)
  have hrel : (Ideal.span {a}).toAddSubgroup.relIndex (qI 𝔞 a).toAddSubgroup * Ideal.absNorm (qI 𝔞 a) =
      Ideal.absNorm (Ideal.span {a}) := by
    rw [absNorm_eq_index, absNorm_eq_index]
    exact AddSubgroup.relIndex_mul_index ((Submodule.toAddSubgroup_le _ _).mpr hle)
  have hdvd : Ideal.absNorm (Ideal.span {a}) ∣ Ideal.absNorm 𝔞 * Ideal.absNorm (qI 𝔞 a) := by
    have := Ideal.absNorm_dvd_absNorm_of_le hmul
    rwa [map_mul] at this
  have hr0 : (Ideal.span {a}).toAddSubgroup.relIndex (qI 𝔞 a).toAddSubgroup ≠ 0 := by
    intro h
    rw [h, zero_mul] at hrel
    exact hNa hrel.symm
  refine ⟨hle, hr0, ?_⟩
  have h1 : (Ideal.span {a}).toAddSubgroup.relIndex (qI 𝔞 a).toAddSubgroup * Ideal.absNorm (qI 𝔞 a) ≤
      Ideal.absNorm 𝔞 * Ideal.absNorm (qI 𝔞 a) := by
    rw [hrel]
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero (mul_ne_zero hN𝔞 hNq)) hdvd
  exact Nat.le_of_mul_le_mul_right h1 (Nat.pos_of_ne_zero hNq)

/- English proof (translation)
Introduce `_ ht s hs` and use `ht s (h hs)`.
-/
theorem dualL_anti {K : Type} [Field K] [NumberField K] {k : ℕ} {X Y : Submodule (𝓞 K) (Fin k → K)}
    (h : X ≤ Y) : dualL Y ≤ dualL X :=
  fun _ ht s hs => ht s (h hs)

/- English proof (translation)
Simplify using `only [dotProduct, Pi.smul_apply, Algebra.smul_def, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => by ring` and prove the remaining obligations.
-/
theorem smul_dot {K : Type} [Field K] [NumberField K] {k : ℕ} (c : 𝓞 K) (x t : Fin k → K) :
    (c • x) ⬝ᵥ t = algebraMap (𝓞 K) K c * (x ⬝ᵥ t) := by
  simp only [dotProduct, Pi.smul_apply, Algebra.smul_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => by ring

/- English proof (translation)
Establish `hX1Y : X ⊔ Submodule.span (𝓞 K) {x} ≤ Y` using `sup_le hXY ((Submodule.span_singleton_le_iff_mem _ _).mpr hxY)`. Establish `hxX1 : x ∈ X ⊔ Submodule.span (𝓞 K) {x}` using `Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)`. Establish `hneX1 : X.toAddSubgroup.relIndex (X ⊔ Submodule.span (𝓞 K) {x}).toAddSubgroup ≠ 0` using `fun h => hne (AddSubgroup.relIndex_eq_zero_of_le_right ((Submodule.toAddSubgroup_le _ _).mpr hX1Y) h)`. Set `g : 𝓞 K →+ (Fin k → K)` to `AddMonoidHom.mk' (fun c => c • x) (fun c c' => add_smul c c' x)`. Establish `e1 : (aI X x).toAddSubgroup = X.toAddSubgroup.comap g`.

Use extensionality with `c`. Conclude with `Iff.rfl`. Establish `hrange : g.range ≤ (X ⊔ Submodule.span (𝓞 K) {x}).toAddSubgroup`. Introduce and unpack `_ ⟨c, rfl⟩`. Conclude with `(X ⊔ Submodule.span (𝓞 K) {x}).smul_mem c hxX1`.

Establish `hN : Ideal.absNorm (aI X x) = X.toAddSubgroup.relIndex g.range`. Rewrite using `[absNorm_eq_index, e1, AddSubgroup.index_comap]`. Establish `hNne : Ideal.absNorm (aI X x) ≠ 0`. Rewrite using `[hN]`. Conclude with `fun h => hneX1 (AddSubgroup.relIndex_eq_zero_of_le_right hrange h)`.

Establish `hNle : Ideal.absNorm (aI X x) ≤ X.toAddSubgroup.relIndex (X ⊔ Submodule.span (𝓞 K) {x}).toAddSubgroup`. Rewrite using `[hN]`. Conclude with `AddSubgroup.relIndex_le_of_le_right hrange hneX1`. Establish `h𝔞 : aI X x ≠ ⊥`. Introduce `h`.

Rewrite `hNne` using `[h, Ideal.absNorm_bot]`. Conclude with `hNne rfl`. Take `⟨a, ha, ha0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot h𝔞`. Establish `hax : a • x ∈ X` using `ha`. Take `⟨hle, hq0, hqle⟩` from `quot_le K (aI X x) h𝔞 a ha0`.

Set `ψ : (Fin k → K) →+ K` to `AddMonoidHom.mk' (fun t => algebraMap (𝓞 K) K a * (x ⬝ᵥ t)) (fun t t' => by simp only [dotProduct_add, mul_add])`. Set `mO : 𝓞 K →+ K` to `(algebraMap (𝓞 K) K).toAddMonoidHom`. Establish `hinj : Function.Injective mO` using `IsFractionRing.injective (𝓞 K) K`. Establish `ha0K : algebraMap (𝓞 K) K a ≠ 0` using `fun h => ha0 (hinj (h.trans (map_zero _).symm))`. Establish `claim1 : (dualL (X ⊔ Submodule.span (𝓞 K) {x})).toAddSubgroup = ((Ideal.span {a}).toAddSubgroup.map mO).comap ψ ⊓ (dualL X).toAddSubgroup`.

Use extensionality with `t`. Prove the components needed by the constructor for the conclusion. Introduce `ht`. Use `⟨?_, dualL_anti le_sup_left ht⟩` and prove the remaining obligations. Take `⟨o, ho⟩` from `ht x hxX1`.

Use `⟨a * o, Ideal.mul_mem_right o _ (Ideal.mem_span_singleton_self a), ?_⟩` and prove the remaining obligations. Use `show algebraMap (𝓞 K) K (a * o) = algebraMap (𝓞 K) K a * (x ⬝ᵥ t)`. Rewrite using `[map_mul, ho]`. Introduce and unpack `⟨⟨r, hr, hrt⟩, htX⟩`. Take `⟨o, rfl⟩` from `Ideal.mem_span_singleton'.mp hr`.

Establish `hrt' : algebraMap (𝓞 K) K a * algebraMap (𝓞 K) K o = algebraMap (𝓞 K) K a * (x ⬝ᵥ t)`. Rewrite using `[← map_mul, mul_comm a o]`. Conclude with `hrt`. Establish `hxt : x ⬝ᵥ t = algebraMap (𝓞 K) K o` using `(mul_left_cancel₀ ha0K hrt').symm`. Introduce `s hs`.

Take `⟨s0, hs0, s1, hs1, rfl⟩` from `Submodule.mem_sup.mp hs`. Take `⟨c, rfl⟩` from `Submodule.mem_span_singleton.mp hs1`. Rewrite using `[add_dotProduct, smul_dot, hxt, ← map_mul]`. Conclude with `add_mem (htX s0 hs0) ⟨c * o, rfl⟩`. Establish `claim2 : (dualL X).toAddSubgroup.map ψ ≤ (qI (aI X x) a).toAddSubgroup.map mO`.

Introduce and unpack `_ ⟨t, ht, rfl⟩`. Take `⟨o, ho⟩` from `(show t ∈ dualL X from ht) (a • x) hax`. Use `⟨o, ?_, ?_⟩` and prove the remaining obligations. Introduce `c hc`. Take `⟨o', ho'⟩` from `(show t ∈ dualL X from ht) (c • x) hc`.

Establish `: c * o = o' * a`. Apply `hinj` to reduce the goal to its premises. Use `show algebraMap (𝓞 K) K (c * o) = algebraMap (𝓞 K) K (o' * a)`. Rewrite using `[map_mul, map_mul, ho, ho', smul_dot, smul_dot]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this, Ideal.mem_span_singleton']`. Conclude with `⟨o', rfl⟩`. Use `show algebraMap (𝓞 K) K o = algebraMap (𝓞 K) K a * (x ⬝ᵥ t)`. Rewrite using `[ho, smul_dot]`. Establish `hmapQ : ((Ideal.span {a}).toAddSubgroup.map mO).relIndex ((qI (aI X x) a).toAddSubgroup.map mO) = (Ideal.span {a}).toAddSubgroup.relIndex (qI (aI X x) a).toAddSubgroup` using `AddSubgroup.relIndex_map_map_of_injective _ _ hinj`.

Establish `hrel : (dualL (X ⊔ Submodule.span (𝓞 K) {x})).toAddSubgroup.relIndex (dualL X).toAddSubgroup = ((Ideal.span {a}).toAddSubgroup.map mO).relIndex ((dualL X).toAddSubgroup.map ψ)`. Rewrite using `[claim1, AddSubgroup.inf_relIndex_right, AddSubgroup.relIndex_comap]`. Establish `hQne : ((Ideal.span {a}).toAddSubgroup.map mO).relIndex ((qI (aI X x) a).toAddSubgroup.map mO) ≠ 0`. Rewrite using `[hmapQ]`. Conclude with `hq0`.

Rewrite using `[hrel]`. Use `⟨fun h => hQne (AddSubgroup.relIndex_eq_zero_of_le_right claim2 h), ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem step (K : Type) [Field K] [NumberField K] (k : ℕ) (X Y : Submodule (𝓞 K) (Fin k → K)) (hXY : X ≤ Y)
    (hne : X.toAddSubgroup.relIndex Y.toAddSubgroup ≠ 0) (x : Fin k → K) (hxY : x ∈ Y) :
    (dualL (X ⊔ Submodule.span (𝓞 K) {x})).toAddSubgroup.relIndex (dualL X).toAddSubgroup ≠ 0 ∧
    (dualL (X ⊔ Submodule.span (𝓞 K) {x})).toAddSubgroup.relIndex (dualL X).toAddSubgroup ≤
      X.toAddSubgroup.relIndex (X ⊔ Submodule.span (𝓞 K) {x}).toAddSubgroup := by
  have hX1Y : X ⊔ Submodule.span (𝓞 K) {x} ≤ Y :=
    sup_le hXY ((Submodule.span_singleton_le_iff_mem _ _).mpr hxY)
  have hxX1 : x ∈ X ⊔ Submodule.span (𝓞 K) {x} :=
    Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)
  have hneX1 : X.toAddSubgroup.relIndex (X ⊔ Submodule.span (𝓞 K) {x}).toAddSubgroup ≠ 0 := fun h =>
    hne (AddSubgroup.relIndex_eq_zero_of_le_right ((Submodule.toAddSubgroup_le _ _).mpr hX1Y) h)

  let g : 𝓞 K →+ (Fin k → K) := AddMonoidHom.mk' (fun c => c • x) (fun c c' => add_smul c c' x)
  have e1 : (aI X x).toAddSubgroup = X.toAddSubgroup.comap g := by
    ext c
    exact Iff.rfl
  have hrange : g.range ≤ (X ⊔ Submodule.span (𝓞 K) {x}).toAddSubgroup := by
    rintro _ ⟨c, rfl⟩
    exact (X ⊔ Submodule.span (𝓞 K) {x}).smul_mem c hxX1
  have hN : Ideal.absNorm (aI X x) = X.toAddSubgroup.relIndex g.range := by
    rw [absNorm_eq_index, e1, AddSubgroup.index_comap]
  have hNne : Ideal.absNorm (aI X x) ≠ 0 := by
    rw [hN]
    exact fun h => hneX1 (AddSubgroup.relIndex_eq_zero_of_le_right hrange h)
  have hNle : Ideal.absNorm (aI X x) ≤ X.toAddSubgroup.relIndex (X ⊔ Submodule.span (𝓞 K) {x}).toAddSubgroup := by
    rw [hN]
    exact AddSubgroup.relIndex_le_of_le_right hrange hneX1
  have h𝔞 : aI X x ≠ ⊥ := by
    intro h
    rw [h, Ideal.absNorm_bot] at hNne
    exact hNne rfl
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔞
  have hax : a • x ∈ X := ha
  obtain ⟨hle, hq0, hqle⟩ := quot_le K (aI X x) h𝔞 a ha0

  let ψ : (Fin k → K) →+ K := AddMonoidHom.mk' (fun t => algebraMap (𝓞 K) K a * (x ⬝ᵥ t))
    (fun t t' => by simp only [dotProduct_add, mul_add])
  let mO : 𝓞 K →+ K := (algebraMap (𝓞 K) K).toAddMonoidHom
  have hinj : Function.Injective mO := IsFractionRing.injective (𝓞 K) K
  have ha0K : algebraMap (𝓞 K) K a ≠ 0 := fun h => ha0 (hinj (h.trans (map_zero _).symm))
  have claim1 : (dualL (X ⊔ Submodule.span (𝓞 K) {x})).toAddSubgroup =
      ((Ideal.span {a}).toAddSubgroup.map mO).comap ψ ⊓ (dualL X).toAddSubgroup := by
    ext t
    constructor
    · intro ht
      refine ⟨?_, dualL_anti le_sup_left ht⟩
      obtain ⟨o, ho⟩ := ht x hxX1
      refine ⟨a * o, Ideal.mul_mem_right o _ (Ideal.mem_span_singleton_self a), ?_⟩
      show algebraMap (𝓞 K) K (a * o) = algebraMap (𝓞 K) K a * (x ⬝ᵥ t)
      rw [map_mul, ho]
    · rintro ⟨⟨r, hr, hrt⟩, htX⟩
      obtain ⟨o, rfl⟩ := Ideal.mem_span_singleton'.mp hr
      have hrt' : algebraMap (𝓞 K) K a * algebraMap (𝓞 K) K o = algebraMap (𝓞 K) K a * (x ⬝ᵥ t) := by
        rw [← map_mul, mul_comm a o]
        exact hrt
      have hxt : x ⬝ᵥ t = algebraMap (𝓞 K) K o := (mul_left_cancel₀ ha0K hrt').symm
      intro s hs
      obtain ⟨s0, hs0, s1, hs1, rfl⟩ := Submodule.mem_sup.mp hs
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hs1
      rw [add_dotProduct, smul_dot, hxt, ← map_mul]
      exact add_mem (htX s0 hs0) ⟨c * o, rfl⟩
  have claim2 : (dualL X).toAddSubgroup.map ψ ≤ (qI (aI X x) a).toAddSubgroup.map mO := by
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨o, ho⟩ := (show t ∈ dualL X from ht) (a • x) hax
    refine ⟨o, ?_, ?_⟩
    · intro c hc
      obtain ⟨o', ho'⟩ := (show t ∈ dualL X from ht) (c • x) hc
      have : c * o = o' * a := by
        apply hinj
        show algebraMap (𝓞 K) K (c * o) = algebraMap (𝓞 K) K (o' * a)
        rw [map_mul, map_mul, ho, ho', smul_dot, smul_dot]
        ring
      rw [this, Ideal.mem_span_singleton']
      exact ⟨o', rfl⟩
    · show algebraMap (𝓞 K) K o = algebraMap (𝓞 K) K a * (x ⬝ᵥ t)
      rw [ho, smul_dot]
  have hmapQ : ((Ideal.span {a}).toAddSubgroup.map mO).relIndex ((qI (aI X x) a).toAddSubgroup.map mO) =
      (Ideal.span {a}).toAddSubgroup.relIndex (qI (aI X x) a).toAddSubgroup :=
    AddSubgroup.relIndex_map_map_of_injective _ _ hinj
  have hrel : (dualL (X ⊔ Submodule.span (𝓞 K) {x})).toAddSubgroup.relIndex (dualL X).toAddSubgroup =
      ((Ideal.span {a}).toAddSubgroup.map mO).relIndex ((dualL X).toAddSubgroup.map ψ) := by
    rw [claim1, AddSubgroup.inf_relIndex_right, AddSubgroup.relIndex_comap]
  have hQne : ((Ideal.span {a}).toAddSubgroup.map mO).relIndex ((qI (aI X x) a).toAddSubgroup.map mO) ≠ 0 := by
    rw [hmapQ]; exact hq0
  rw [hrel]
  refine ⟨fun h => hQne (AddSubgroup.relIndex_eq_zero_of_le_right claim2 h), ?_⟩
  calc ((Ideal.span {a}).toAddSubgroup.map mO).relIndex ((dualL X).toAddSubgroup.map ψ)
      ≤ ((Ideal.span {a}).toAddSubgroup.map mO).relIndex ((qI (aI X x) a).toAddSubgroup.map mO) :=
        AddSubgroup.relIndex_le_of_le_right claim2 hQne
    _ = (Ideal.span {a}).toAddSubgroup.relIndex (qI (aI X x) a).toAddSubgroup := hmapQ
    _ ≤ Ideal.absNorm (aI X x) := hqle
    _ ≤ _ := hNle

end DIdx

open DIdx in
/- English proof (translation)
Introduce `K _ _ k X Y hXY hne`. It suffices to establish `H : ∀ m : ℕ, ∀ X Y : Submodule (𝓞 K) (Fin k → K), X ≤ Y → X.toAddSubgroup.relIndex Y.toAddSubgroup = m → m ≠ 0 → (dualL Y).toAddSubgroup.relIndex (dualL X).toAddSubgroup ≠ 0 ∧ (dualL Y).toAddSubgroup.relIndex (dualL X).toAddSubgroup ≤ X.toAddSubgroup.relIndex Y.toAddSubgroup from …`. Introduce `m`. Proceed by induction on `m using Nat.strong_induction_on with`. Consider the case `_ m ih`.

Introduce `X Y hXY hm hm0`. Distinguish the cases in `hYX : Y ≤ X`. Establish `e : X = Y` using `le_antisymm hXY hYX`. Substitute `e` using the available equality. Rewrite using `[AddSubgroup.relIndex_self, AddSubgroup.relIndex_self]`.

Conclude with `⟨one_ne_zero, le_rfl⟩`. Take `⟨x, hxY, hxX⟩` from `Set.not_subset.mp hYX`. Establish `hX1Y : X ⊔ Submodule.span (𝓞 K) {x} ≤ Y` using `sup_le hXY ((Submodule.span_singleton_le_iff_mem _ _).mpr hxY)`. Establish `hXX1 : X ≤ X ⊔ Submodule.span (𝓞 K) {x}` using `le_sup_left`. Establish `hxX1 : x ∈ X ⊔ Submodule.span (𝓞 K) {x}` using `Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)`.

Take `⟨h0, hle⟩` from `step K k X Y hXY (by rw [hm]; exact hm0) x hxY`. Establish `hmul` using `AddSubgroup.relIndex_mul_relIndex _ _ _ ((Submodule.toAddSubgroup_le _ _).mpr hXX1) ((Submodule.toAddSubgroup_le _ _).mpr hX1Y)`. Rewrite `hmul` using `[hm]`. Establish `hb0 : (X ⊔ Submodule.span (𝓞 K) {x}).toAddSubgroup.relIndex Y.toAddSubgroup ≠ 0`. Introduce `h`.

Rewrite `hmul` using `[h, mul_zero]`. Conclude with `hm0 hmul.symm`. Establish `ha0 : X.toAddSubgroup.relIndex (X ⊔ Submodule.span (𝓞 K) {x}).toAddSubgroup ≠ 0`. Introduce `h`. Rewrite `hmul` using `[h, zero_mul]`.

Conclude with `hm0 hmul.symm`. Establish `ha1 : X.toAddSubgroup.relIndex (X ⊔ Submodule.span (𝓞 K) {x}).toAddSubgroup ≠ 1`. Introduce `h`. Rewrite `h` using `[AddSubgroup.relIndex_eq_one]`. Conclude with `hxX (h hxX1)`.

Establish `hlt : (X ⊔ Submodule.span (𝓞 K) {x}).toAddSubgroup.relIndex Y.toAddSubgroup < m`. Rewrite using `[← hmul]`. Establish `h2 : 2 ≤ X.toAddSubgroup.relIndex (X ⊔ Submodule.span (𝓞 K) {x}).toAddSubgroup` using `by omega`. Establish `hbpos` using `Nat.pos_of_ne_zero hb0`. Use the polynomial consequences of the given equalities and inequalities.

Take `⟨ih0, ihle⟩` from `ih _ hlt (X ⊔ Submodule.span (𝓞 K) {x}) Y hX1Y rfl hb0`. Establish `hdmul` using `AddSubgroup.relIndex_mul_relIndex _ _ _ ((Submodule.toAddSubgroup_le _ _).mpr (DIdx.dualL_anti hX1Y)) ((Submodule.toAddSubgroup_le _ _).mpr (DIdx.dualL_anti hXX1))`. Rewrite using `[← hdmul, hm, ← hmul]`. Use `⟨mul_ne_zero ih0 h0, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_comm (X.toAddSubgroup.relIndex _)]`.

Conclude with `Nat.mul_le_mul ihle hle`.
-/
theorem dual_index_formula : DualIdx := by
  intro K _ _ k X Y hXY hne
  suffices H : ∀ m : ℕ, ∀ X Y : Submodule (𝓞 K) (Fin k → K), X ≤ Y →
      X.toAddSubgroup.relIndex Y.toAddSubgroup = m → m ≠ 0 →
      (dualL Y).toAddSubgroup.relIndex (dualL X).toAddSubgroup ≠ 0 ∧
        (dualL Y).toAddSubgroup.relIndex (dualL X).toAddSubgroup ≤ X.toAddSubgroup.relIndex Y.toAddSubgroup from
    H _ X Y hXY rfl hne
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro X Y hXY hm hm0
  by_cases hYX : Y ≤ X
  · have e : X = Y := le_antisymm hXY hYX
    subst e
    rw [AddSubgroup.relIndex_self, AddSubgroup.relIndex_self]
    exact ⟨one_ne_zero, le_rfl⟩
  · obtain ⟨x, hxY, hxX⟩ := Set.not_subset.mp hYX
    have hX1Y : X ⊔ Submodule.span (𝓞 K) {x} ≤ Y :=
      sup_le hXY ((Submodule.span_singleton_le_iff_mem _ _).mpr hxY)
    have hXX1 : X ≤ X ⊔ Submodule.span (𝓞 K) {x} := le_sup_left
    have hxX1 : x ∈ X ⊔ Submodule.span (𝓞 K) {x} :=
      Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)
    obtain ⟨h0, hle⟩ := step K k X Y hXY (by rw [hm]; exact hm0) x hxY
    have hmul := AddSubgroup.relIndex_mul_relIndex _ _ _ ((Submodule.toAddSubgroup_le _ _).mpr hXX1)
      ((Submodule.toAddSubgroup_le _ _).mpr hX1Y)
    rw [hm] at hmul
    have hb0 : (X ⊔ Submodule.span (𝓞 K) {x}).toAddSubgroup.relIndex Y.toAddSubgroup ≠ 0 := by
      intro h; rw [h, mul_zero] at hmul; exact hm0 hmul.symm
    have ha0 : X.toAddSubgroup.relIndex (X ⊔ Submodule.span (𝓞 K) {x}).toAddSubgroup ≠ 0 := by
      intro h; rw [h, zero_mul] at hmul; exact hm0 hmul.symm
    have ha1 : X.toAddSubgroup.relIndex (X ⊔ Submodule.span (𝓞 K) {x}).toAddSubgroup ≠ 1 := by
      intro h
      rw [AddSubgroup.relIndex_eq_one] at h
      exact hxX (h hxX1)
    have hlt : (X ⊔ Submodule.span (𝓞 K) {x}).toAddSubgroup.relIndex Y.toAddSubgroup < m := by
      rw [← hmul]
      have h2 : 2 ≤ X.toAddSubgroup.relIndex (X ⊔ Submodule.span (𝓞 K) {x}).toAddSubgroup := by omega
      have hbpos := Nat.pos_of_ne_zero hb0
      nlinarith
    obtain ⟨ih0, ihle⟩ := ih _ hlt (X ⊔ Submodule.span (𝓞 K) {x}) Y hX1Y rfl hb0
    have hdmul := AddSubgroup.relIndex_mul_relIndex _ _ _ ((Submodule.toAddSubgroup_le _ _).mpr (DIdx.dualL_anti hX1Y))
      ((Submodule.toAddSubgroup_le _ _).mpr (DIdx.dualL_anti hXX1))
    rw [← hdmul, hm, ← hmul]
    refine ⟨mul_ne_zero ih0 h0, ?_⟩
    rw [mul_comm (X.toAddSubgroup.relIndex _)]
    exact Nat.mul_le_mul ihle hle

end PI.UnitaryGroupMassFormula.LCG
