import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom

/- English proof (translation)
Establish `hs : Function.Surjective ((Ideal.Quotient.mk M).comp a)`. Introduce `y`. Take `⟨r, rfl⟩` from `Ideal.Quotient.mk_surjective y`. Take `⟨c, hc⟩` from `hd r`. Conclude with `⟨c, (Ideal.Quotient.eq.2 hc).symm⟩`.

Establish `hker : RingHom.ker ((Ideal.Quotient.mk M).comp a) ≤ RingHom.ker ((Ideal.Quotient.mk K).comp f)`. Introduce `c hc`. Rewrite `hc`, the goal using `[RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hk c hc`. Use `⟨(RingHom.liftOfSurjective _ hs ⟨_, hker⟩).comp (Ideal.Quotient.mk M), ?_⟩` and prove the remaining obligations.

Introduce `r c hc`. Rewrite using `[RingHom.comp_apply, Ideal.Quotient.eq.2 hc]`. Conclude with `RingHom.liftOfSurjective_comp_apply _ hs ⟨_, hker⟩ c`.
-/
private theorem UpperTheory.Reformulated.B.LevelOfCongruence.level {C R T : Type} [CommRing C] [CommRing R] [CommRing T]
    (a : C →+* R) (f : C →+* T) (M : Ideal R) (K : Ideal T)
    (hd : ∀ r : R, ∃ c, r - a c ∈ M) (hk : ∀ c, a c ∈ M → f c ∈ K) :
    ∃ g : R →+* T ⧸ K, ∀ r c, r - a c ∈ M → g r = Ideal.Quotient.mk K (f c) := by
  have hs : Function.Surjective ((Ideal.Quotient.mk M).comp a) := by
    intro y
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨c, hc⟩ := hd r
    exact ⟨c, (Ideal.Quotient.eq.2 hc).symm⟩
  have hker : RingHom.ker ((Ideal.Quotient.mk M).comp a) ≤
      RingHom.ker ((Ideal.Quotient.mk K).comp f) := by
    intro c hc
    rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem] at hc ⊢
    exact hk c hc
  refine ⟨(RingHom.liftOfSurjective _ hs ⟨_, hker⟩).comp (Ideal.Quotient.mk M), ?_⟩
  intro r c hc
  rw [RingHom.comp_apply, Ideal.Quotient.eq.2 hc]
  exact RingHom.liftOfSurjective_comp_apply _ hs ⟨_, hker⟩ c

/- English proof (translation)
Introduce `C R _ _ _ _ x h T _ J _ f hx`. Establish `hk : ∀ (n : ℕ) (c : C), algebraMap C R c ∈ IsLocalRing.maximalIdeal R ^ n → f c ∈ J ^ n`. Introduce `n c hc`. Establish `h1 : c ∈ x ^ n`. Rewrite using `[← h.comap_pow n]`.

Conclude with `hc`. Conclude with `Ideal.le_comap_pow f n (Ideal.pow_right_mono hx n h1)`. Use `choose g hg using fun n : ℕ => UpperTheory.Reformulated.B.LevelOfCongruence.level (algebraMap C R) f (IsLocalRing.maximalIdeal R ^ n) (J ^ n) (h.dense n) (hk n)`. Establish `hc : ∀ {m n : ℕ} (hle : m ≤ n), (Ideal.Quotient.factorPow J hle).comp (g n) = g m`. Introduce `m n hle`.

Use extensionality with `r`. Take `⟨c, hc⟩` from `h.dense n r`. Rewrite using `[RingHom.comp_apply, hg n r c hc, hg m r c (Ideal.pow_le_pow_right hle hc)]`. Both sides reduce to the same expression. Use `⟨IsAdicComplete.liftRingHom J g hc, ?_, ?_⟩` and prove the remaining obligations.

Apply `DFunLike.coe_injective` to reduce the goal to its premises. Apply `IsHausdorff.funext' J` to reduce the goal to its premises. Introduce `n c`. Rewrite using `[RingHom.comp_apply, IsAdicComplete.mk_liftRingHom]`. Conclude with `hg n _ c (by simp)`.

Introduce `r hr`. Establish `h0` using `IsAdicComplete.mk_liftRingHom J g hc 1 r`. Rewrite `h0` using `[hg 1 r 0 (by simpa using hr), map_zero, map_zero, Ideal.Quotient.eq_zero_iff_mem, pow_one]`. Conclude with `h0`.
-/
theorem UpperTheory.Reformulated.B.LevelOfCongruence.cu_ex :
    ∀ {C R : Type} [inst : CommRing C] [inst_1 : CommRing R] [inst_2 : Algebra C R] [inst_3 : IsLocalRing R] {x : Ideal C},
      UpperTheory.V.CA.IsCplAt x R →
        ∀ {T : Type} [inst_4 : CommRing T] (J : Ideal T) [IsAdicComplete J T] (f : C →+* T),
          x ≤ Ideal.comap f J →
            ∃ (F : R →+* T), F.comp (Algebra.algebraMap C R) = f ∧ IsLocalRing.maximalIdeal R ≤ Ideal.comap F J := by
  intro C R _ _ _ _ x h T _ J _ f hx
  have hk : ∀ (n : ℕ) (c : C), algebraMap C R c ∈ IsLocalRing.maximalIdeal R ^ n → f c ∈ J ^ n := by
    intro n c hc
    have h1 : c ∈ x ^ n := by
      rw [← h.comap_pow n]
      exact hc
    exact Ideal.le_comap_pow f n (Ideal.pow_right_mono hx n h1)
  choose g hg using fun n : ℕ => UpperTheory.Reformulated.B.LevelOfCongruence.level (algebraMap C R) f
    (IsLocalRing.maximalIdeal R ^ n) (J ^ n) (h.dense n) (hk n)
  have hc : ∀ {m n : ℕ} (hle : m ≤ n), (Ideal.Quotient.factorPow J hle).comp (g n) = g m := by
    intro m n hle
    ext r
    obtain ⟨c, hc⟩ := h.dense n r
    rw [RingHom.comp_apply, hg n r c hc, hg m r c (Ideal.pow_le_pow_right hle hc)]
    rfl
  refine ⟨IsAdicComplete.liftRingHom J g hc, ?_, ?_⟩
  · apply DFunLike.coe_injective
    apply IsHausdorff.funext' J
    intro n c
    rw [RingHom.comp_apply, IsAdicComplete.mk_liftRingHom]
    exact hg n _ c (by simp)
  · intro r hr
    have h0 := IsAdicComplete.mk_liftRingHom J g hc 1 r
    rw [hg 1 r 0 (by simpa using hr), map_zero, map_zero, Ideal.Quotient.eq_zero_iff_mem,
      pow_one] at h0
    exact h0
