import Mathlib
open scoped TensorProduct

namespace GlobalTheory.ValuativeQuotient

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/- English proof (translation)
Introduce `V K B _ _ _ _ _ _ _ _ JK`. Establish `hloc` using `IsLocalization.tensorRight (S := B) K (nonZeroDivisors V)`. Use `set M := Algebra.algebraMapSubmonoid B (nonZeroDivisors V) with hM`. Establish `hmap : ∀ I : Ideal B, I.map (Algebra.TensorProduct.includeRight : B →ₐ[V] K ⊗[V] B) = I.map (algebraMap B (K ⊗[V] B))` using `fun I => rfl`. Establish `hsmul : ∀ (J : Ideal B) (v : V) (b : B), v • Ideal.Quotient.mk J b = Ideal.Quotient.mk J (algebraMap V B v * b)`.

Introduce `J v b`. Rewrite using `[← Algebra.smul_def, ← Ideal.Quotient.mkₐ_eq_mk V, map_smul]`. Establish `hflat : ∀ J : Ideal B, Module.Flat V (B ⧸ J) ↔ ∀ m ∈ M, ∀ b : B, m * b ∈ J → b ∈ J`. Introduce `J`. Rewrite using `[Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, Submodule.eq_bot_iff]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `h m ⟨v, hv, rfl⟩ b hb`. Establish `h0` using `h (Ideal.Quotient.mk J b) ((Submodule.mem_torsion_iff _).mpr ⟨⟨v, hv⟩, by show v • Ideal.Quotient.mk J b = 0`. Rewrite using `[hsmul, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hb⟩)`.

Conclude with `Ideal.Quotient.eq_zero_iff_mem.mp h0`. Introduce `h x hx`. Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Take `⟨⟨v, hv⟩, hvb⟩` from `(Submodule.mem_torsion_iff _).mp hx`. Express the relevant statement in the definitionally equal form `v • Ideal.Quotient.mk J b = 0 at hvb`.

Rewrite `hvb` using `[hsmul, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.mpr (h _ ⟨v, hv, rfl⟩ b hvb)`. Use `⟨JK.comap (algebraMap B (K ⊗[V] B)), ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hflat]`. Introduce `m hm b hb`.

Rewrite `hb` using `[Ideal.mem_comap, map_mul]`. Conclude with `(Ideal.unit_mul_mem_iff_mem JK (IsLocalization.map_units (K ⊗[V] B) ⟨m, hm⟩)).mp hb`. Rewrite using `[hmap]`. Conclude with `IsLocalization.map_comap M (K ⊗[V] B) JK`. Introduce and unpack `J' ⟨hJ'f, hJ'⟩`.

Rewrite `hJ'` using `[hmap]`. Rewrite `hJ'f` using `[hflat]`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[← hJ']`. Conclude with `Ideal.le_comap_map`.

Introduce `b hb`. Rewrite `hb` using `[Ideal.mem_comap, ← hJ', IsLocalization.mem_map_algebraMap_iff M]`. Take `⟨⟨x, m⟩, hxm⟩` from `hb`. Rewrite `hxm` using `[← map_mul, IsLocalization.eq_iff_exists M]`. Take `⟨c, hc⟩` from `hxm`.

Apply `hJ'f (c * m) (M.mul_mem c.2 m.2)` to reduce the goal to its premises. Establish `: (c : B) * (m : B) * b = c * x.1` using `by rw [← hc]; ring`. Rewrite using `[this]`. Conclude with `J'.mul_mem_left _ x.2`.
-/
theorem main : ∀ (V K B : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field K]
    [Algebra V K] [IsFractionRing V K] [CommRing B] [Algebra V B] (JK : Ideal (K ⊗[V] B)),
    ∃! J : Ideal B, Module.Flat V (B ⧸ J) ∧
      J.map (Algebra.TensorProduct.includeRight : B →ₐ[V] K ⊗[V] B) = JK := by
  intro V K B _ _ _ _ _ _ _ _ JK
  have hloc := IsLocalization.tensorRight (S := B) K (nonZeroDivisors V)
  set M := Algebra.algebraMapSubmonoid B (nonZeroDivisors V) with hM
  have hmap : ∀ I : Ideal B,
      I.map (Algebra.TensorProduct.includeRight : B →ₐ[V] K ⊗[V] B) =
        I.map (algebraMap B (K ⊗[V] B)) := fun I => rfl
  have hsmul : ∀ (J : Ideal B) (v : V) (b : B),
      v • Ideal.Quotient.mk J b = Ideal.Quotient.mk J (algebraMap V B v * b) := by
    intro J v b
    rw [← Algebra.smul_def, ← Ideal.Quotient.mkₐ_eq_mk V, map_smul]
  have hflat : ∀ J : Ideal B, Module.Flat V (B ⧸ J) ↔ ∀ m ∈ M, ∀ b : B, m * b ∈ J → b ∈ J := by
    intro J
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, Submodule.eq_bot_iff]
    constructor
    · rintro h m ⟨v, hv, rfl⟩ b hb
      have h0 := h (Ideal.Quotient.mk J b) ((Submodule.mem_torsion_iff _).mpr
        ⟨⟨v, hv⟩, by
          show v • Ideal.Quotient.mk J b = 0
          rw [hsmul, Ideal.Quotient.eq_zero_iff_mem]
          exact hb⟩)
      exact Ideal.Quotient.eq_zero_iff_mem.mp h0
    · intro h x hx
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨⟨v, hv⟩, hvb⟩ := (Submodule.mem_torsion_iff _).mp hx
      change v • Ideal.Quotient.mk J b = 0 at hvb
      rw [hsmul, Ideal.Quotient.eq_zero_iff_mem] at hvb
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (h _ ⟨v, hv, rfl⟩ b hvb)
  refine ⟨JK.comap (algebraMap B (K ⊗[V] B)), ⟨?_, ?_⟩, ?_⟩
  · rw [hflat]
    intro m hm b hb
    rw [Ideal.mem_comap, map_mul] at hb
    exact (Ideal.unit_mul_mem_iff_mem JK (IsLocalization.map_units (K ⊗[V] B) ⟨m, hm⟩)).mp hb
  · rw [hmap]
    exact IsLocalization.map_comap M (K ⊗[V] B) JK
  · rintro J' ⟨hJ'f, hJ'⟩
    rw [hmap] at hJ'
    rw [hflat] at hJ'f
    apply le_antisymm
    · rw [← hJ']
      exact Ideal.le_comap_map
    · intro b hb
      rw [Ideal.mem_comap, ← hJ', IsLocalization.mem_map_algebraMap_iff M] at hb
      obtain ⟨⟨x, m⟩, hxm⟩ := hb
      rw [← map_mul, IsLocalization.eq_iff_exists M] at hxm
      obtain ⟨c, hc⟩ := hxm
      apply hJ'f (c * m) (M.mul_mem c.2 m.2)
      have : (c : B) * (m : B) * b = c * x.1 := by rw [← hc]; ring
      rw [this]
      exact J'.mul_mem_left _ x.2

end GlobalTheory.ValuativeQuotient
