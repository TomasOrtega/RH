import Mathlib

namespace GlobalTheory.ASwap

variable {A : Type} [CommRing A] [IsDomain A]

noncomputable def mulMap (a b c : A) (hc : a * b = c) :
    (A ⧸ Ideal.span {a}) →ₗ[A] (A ⧸ Ideal.span {c}) :=
  Submodule.mapQ (Ideal.span {a}) (Ideal.span {c}) (LinearMap.lsmul A A b) (by
    intro x hx
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hx
    simp only [Submodule.mem_comap, LinearMap.lsmul_apply, smul_eq_mul]
    exact Submodule.mem_span_singleton.mpr ⟨r, by rw [← hc]; ring⟩)

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma mulMap_mk (a b c : A) (hc : a * b = c) (x : A) :
    mulMap a b c hc (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (b * x) := rfl

/- English proof (translation)
Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `q hq`. Proceed by induction on `q using Submodule.Quotient.induction_on with`. Consider the case `H x`. Express the relevant statement in the definitionally equal form `mulMap a b c hc (Ideal.Quotient.mk _ x) = 0 at hq`.

Rewrite `hq` using `[mulMap_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']`. Take `⟨r, hr⟩` from `hq`. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk _ x = 0`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']`. Use `⟨r, ?_⟩` and prove the remaining obligations.

Apply `mul_left_cancel₀ hb` to reduce the goal to its premises. Rewrite using `[← hr, ← hc]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma mulMap_injective (a b c : A) (hb : b ≠ 0) (hc : a * b = c) :
    Function.Injective (mulMap a b c hc) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro q hq
  induction q using Submodule.Quotient.induction_on with
  | H x =>
    change mulMap a b c hc (Ideal.Quotient.mk _ x) = 0 at hq
    rw [mulMap_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at hq
    obtain ⟨r, hr⟩ := hq
    change Ideal.Quotient.mk _ x = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
    refine ⟨r, ?_⟩
    apply mul_left_cancel₀ hb
    rw [← hr, ← hc]; ring

/- English proof (translation)
Use extensionality with `z`. Simplify using `only [Submodule.mem_map, LinearMap.mem_ker, LinearMap.lsmul_apply, Submodule.mem_inf]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨q, hq, rfl⟩`. Proceed by induction on `q using Submodule.Quotient.induction_on with`.

Consider the case `H x`. Use `⟨b * x, ⟨?_, ?_⟩, rfl⟩` and prove the remaining obligations. Establish `hq' : Ideal.Quotient.mk (Ideal.span {a}) (b * x) = 0` using `hq`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.mp hq'`. Conclude with `Ideal.mem_span_singleton'.mpr ⟨x, mul_comm _ _⟩`.

Introduce and unpack `⟨t, ⟨hta, htb⟩, rfl⟩`. Take `⟨x, rfl⟩` from `Ideal.mem_span_singleton'.mp htb`. Use `⟨Ideal.Quotient.mk _ x, ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk (Ideal.span {a}) (b * x) = 0`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem, mul_comm]`.

Conclude with `hta`. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk _ (b * x) = Ideal.Quotient.mk _ (x * b)`. Rewrite using `[mul_comm]`.
-/
lemma map_mulMap_ker (a b c : A) (hc : a * b = c) :
    (LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b)).map (mulMap a b c hc) =
      Submodule.map (Submodule.mkQ (Ideal.span {c})) (Ideal.span {a} ⊓ Ideal.span {b} : Submodule A A) := by
  ext z
  simp only [Submodule.mem_map, LinearMap.mem_ker, LinearMap.lsmul_apply, Submodule.mem_inf]
  constructor
  · rintro ⟨q, hq, rfl⟩
    induction q using Submodule.Quotient.induction_on with
    | H x =>
      refine ⟨b * x, ⟨?_, ?_⟩, rfl⟩
      · have hq' : Ideal.Quotient.mk (Ideal.span {a}) (b * x) = 0 := hq
        exact Ideal.Quotient.eq_zero_iff_mem.mp hq'
      · exact Ideal.mem_span_singleton'.mpr ⟨x, mul_comm _ _⟩
  · rintro ⟨t, ⟨hta, htb⟩, rfl⟩
    obtain ⟨x, rfl⟩ := Ideal.mem_span_singleton'.mp htb
    refine ⟨Ideal.Quotient.mk _ x, ?_, ?_⟩
    · change Ideal.Quotient.mk (Ideal.span {a}) (b * x) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem, mul_comm]; exact hta
    · change Ideal.Quotient.mk _ (b * x) = Ideal.Quotient.mk _ (x * b)
      rw [mul_comm]

noncomputable def kerEquiv (a b : A) (ha : a ≠ 0) (hb : b ≠ 0) :
    LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b) ≃ₗ[A]
      LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {b}) a) :=
  (Submodule.equivMapOfInjective _ (mulMap_injective a b (a * b) hb rfl) _).trans
    ((LinearEquiv.ofEq _ _ (by
        rw [map_mulMap_ker, map_mulMap_ker b a (a * b) (mul_comm b a), inf_comm])).trans
      (Submodule.equivMapOfInjective _ (mulMap_injective b a (a * b) ha (mul_comm b a)) _).symm)

/- English proof (translation)
Use extensionality with `z`. Simplify using `only [LinearMap.mem_range, LinearMap.lsmul_apply, Submodule.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨q, rfl⟩`. Proceed by induction on `q using Submodule.Quotient.induction_on with`.

Consider the case `H x => exact ⟨x * b, Ideal.mem_span_singleton'.mpr ⟨x, rfl⟩, by`. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk _ (x * b) = Ideal.Quotient.mk _ (b * x)`. Rewrite using `[mul_comm]⟩`. Introduce and unpack `⟨t, ht, rfl⟩`. Take `⟨x, rfl⟩` from `Ideal.mem_span_singleton'.mp ht`.

Conclude with `⟨Ideal.Quotient.mk _ x, by`. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk _ (b * x) = Ideal.Quotient.mk _ (x * b)`. Rewrite using `[mul_comm]⟩`.
-/
lemma range_lsmul_eq (a b : A) :
    LinearMap.range (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b) =
      Submodule.map (Submodule.mkQ (Ideal.span {a})) (Ideal.span {b} : Submodule A A) := by
  ext z
  simp only [LinearMap.mem_range, LinearMap.lsmul_apply, Submodule.mem_map]
  constructor
  · rintro ⟨q, rfl⟩
    induction q using Submodule.Quotient.induction_on with
    | H x => exact ⟨x * b, Ideal.mem_span_singleton'.mpr ⟨x, rfl⟩, by
        change Ideal.Quotient.mk _ (x * b) = Ideal.Quotient.mk _ (b * x); rw [mul_comm]⟩
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨x, rfl⟩ := Ideal.mem_span_singleton'.mp ht
    exact ⟨Ideal.Quotient.mk _ x, by
        change Ideal.Quotient.mk _ (b * x) = Ideal.Quotient.mk _ (x * b); rw [mul_comm]⟩

noncomputable def cokerEquiv (a b : A) :
    ((A ⧸ Ideal.span {a}) ⧸ LinearMap.range (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b)) ≃ₗ[A]
      A ⧸ (Ideal.span {a} ⊔ Ideal.span {b} : Submodule A A) :=
  (Submodule.quotEquivOfEq _ _ (range_lsmul_eq a b)).trans
    (Submodule.quotientQuotientEquivQuotientSup _ _)

end GlobalTheory.ASwap

/- English proof (translation)
Introduce `A _ _ a b ha hb`. Use `⟨(GlobalTheory.ASwap.kerEquiv a b ha hb).length_eq, ?_⟩` and prove the remaining obligations. Conclude with `((GlobalTheory.ASwap.cokerEquiv a b).trans ((Submodule.quotEquivOfEq _ _ (sup_comm _ _)).trans (GlobalTheory.ASwap.cokerEquiv b a).symm)).length_eq`.
-/
theorem GlobalTheory.kernel_cokernel_length_swap :
    ∀ (A : Type) [CommRing A] [IsDomain A] (a b : A), a ≠ 0 → b ≠ 0 → Module.length A (LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b)) = Module.length A (LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {b}) a)) ∧ Module.length A ((A ⧸ Ideal.span {a}) ⧸ LinearMap.range (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b)) = Module.length A ((A ⧸ Ideal.span {b}) ⧸ LinearMap.range (LinearMap.lsmul A (A ⧸ Ideal.span {b}) a)) := by
  intro A _ _ a b ha hb
  refine ⟨(GlobalTheory.ASwap.kerEquiv a b ha hb).length_eq, ?_⟩
  exact ((GlobalTheory.ASwap.cokerEquiv a b).trans ((Submodule.quotEquivOfEq _ _ (sup_comm _ _)).trans
    (GlobalTheory.ASwap.cokerEquiv b a).symm)).length_eq
