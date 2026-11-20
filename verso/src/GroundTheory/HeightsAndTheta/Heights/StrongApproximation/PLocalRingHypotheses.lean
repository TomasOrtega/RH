import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StrongApproximation.Statements
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.StrongApprox

open NumberField IsDedekindDomain TensorProduct ReciprocityTheory.ChartRestriction.G.SA

/- English proof (translation)
Introduce `F E _ _ _ _ _ c h2 hc v`. Establish `: Module.Finite F E` using `Module.finite_of_finrank_eq_succ h2`. Establish `hcc : ∀ x, c (c x) = x`. Establish `hcard : Fintype.card (E ≃ₐ[F] E) ≤ 2` using `h2 ▸ AlgEquiv.card_le`. Establish `hpos` using `orderOf_pos c`.

Establish `hle : orderOf c ≤ Fintype.card (E ≃ₐ[F] E)` using `orderOf_le_card_univ`. Establish `hne : orderOf c ≠ 1` using `fun h => hc (orderOf_eq_one_iff.mp h)`. Establish `ho : orderOf c = 2` using `by omega`. Introduce `x`. Establish `h` using `pow_orderOf_eq_one c`.

Rewrite `h` using `[ho, pow_two]`. Conclude with `DFunLike.congr_fun h x`. Establish `htmul : ∀ (a : v.adicCompletion F) (b : E), sigV c v (a ⊗ₜ b) = a ⊗ₜ c b`. Introduce `a b`. Simplify using `[sigV]`.

Establish `hsig_incl : ∀ x : E, sigV c v (inclV E v x) = inclV E v (c x)`. Introduce `x`. Simplify using `[inclV, htmul]`. Establish `hinv : ∀ x, sigV c v (sigV c v x) = x`. Introduce `x`.

Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b => rw [htmul, htmul, hcc]`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`. Choose the witnesses or unpack the hypotheses as in `⟨α, hα⟩ : ∃ α, c α ≠ α := by`.

Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `hc (AlgEquiv.ext h)`. Use `set β : E := α - c α with hβdef`. Establish `hcβ : c β = -β` using `by simp [hβdef, hcc]`.

Establish `hβ0 : β ≠ 0` using `sub_ne_zero.mpr (Ne.symm hα)`. Establish `h2F : (2 : F) ≠ 0` using `two_ne_zero`. Establish `h2k : (2 : v.adicCompletion F) ≠ 0`. Rewrite using `[← map_ofNat (algebraMap F (v.adicCompletion F)) 2]`. Conclude with `fun h => h2F ((algebraMap F (v.adicCompletion F)).injective (h.trans (map_zero _).symm))`.

Use `set t : Kv E v := (1 : v.adicCompletion F) ⊗ₜ β with htdef`. Establish `ht : IsUnit t` using `(isUnit_iff_ne_zero.mpr hβ0).map (Algebra.TensorProduct.includeRight : E →ₐ[F] Kv E v)`. Establish `hσt : sigV c v t = -t` using `by rw [htdef, htmul, hcβ, TensorProduct.tmul_neg]`. Establish `hli : LinearIndependent F ![(1 : E), β]`. Rewrite using `[LinearIndependent.pair_iff]`.

Introduce `s u hsu`. Establish `hsu' : algebraMap F E s + algebraMap F E u * β = 0`. Simplify `hsu` using `[Algebra.smul_def]`. Establish `hc' : algebraMap F E s + algebraMap F E u * -β = 0`. Use `congrArg c hsu'` as an intermediate fact.

Rewrite `this` using `[map_add, map_mul, AlgEquiv.commutes, AlgEquiv.commutes, hcβ, map_zero]`. Then use the resulting hypothesis. Establish `hs : algebraMap F E (2 * s) = 0`. Rewrite using `[map_mul, map_ofNat]`. Take the linear combination `hsu' + hc'`. Establish `hs0 : s = 0`.

Use `(algebraMap F E).injective (hs.trans (map_zero _).symm)` as an intermediate fact. Conclude with `(mul_eq_zero.mp this).resolve_left h2F`. Substitute `hs0` using the available equality. Rewrite `hsu'` using `[map_zero, zero_add]`. Establish `hu : algebraMap F E u = 0` using `(mul_eq_zero.mp hsu').resolve_right hβ0`.

Conclude with `⟨rfl, (algebraMap F E).injective (hu.trans (map_zero _).symm)⟩`. Set `B : Module.Basis (Fin 2) F E` to `basisOfLinearIndependentOfCardEqFinrank hli (by simp [h2])`. Establish `hB : ∀ i, B i = ![(1 : E), β] i` using `fun i => by`. Simplify using `[B, coe_basisOfLinearIndependentOfCardEqFinrank]`. Set `BK : Module.Basis (Fin 2) (v.adicCompletion F) (Kv E v)` to `Algebra.TensorProduct.basis _ B`.

Establish `hdecomp : ∀ x : Kv E v, ∃ a b : v.adicCompletion F, x = algebraMap _ _ a + algebraMap _ _ b * t`. Introduce `x`. Use `⟨BK.repr x 0, BK.repr x 1, ?_⟩` and prove the remaining obligations. Use `conv_lhs => rw [← BK.sum_repr x]`. Rewrite using `[Fin.sum_univ_two, Algebra.smul_def, Algebra.smul_def]`.

Simplify using `[BK, Algebra.TensorProduct.basis_apply, hB, htdef]`. Establish `hinj : Function.Injective (algebraMap (v.adicCompletion F) (Kv E v))`. Establish `: Nontrivial (Kv E v)` using `⟨⟨0, t, (ht.ne_zero).symm⟩⟩`. Conclude with `(algebraMap (v.adicCompletion F) (Kv E v)).injective`. Establish `hfix : ∀ x, sigV c v x = x ↔ x ∈ Set.range (algebraMap (v.adicCompletion F) (Kv E v))`.

Introduce `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Take `⟨a, b, rfl⟩` from `hdecomp x`. Rewrite `hx` using `[map_add, map_mul, AlgHom.commutes, AlgHom.commutes, hσt]`.

Establish `h2b : algebraMap _ (Kv E v) (2 * b) * t = 0`. Rewrite using `[map_mul, map_ofNat]`. Take the linear combination `-hx`. Establish `hb : b = 0`. Use `(ht.mul_left_eq_zero).mp h2b` as an intermediate fact.

Rewrite `this` using `[← map_zero (algebraMap (v.adicCompletion F) (Kv E v))]`. Conclude with `(mul_eq_zero.mp (hinj this)).resolve_left h2k`. Conclude with `⟨a, by simp [hb]⟩`. Introduce and unpack `⟨a, rfl⟩`. Conclude with `AlgHom.commutes _ a`.

Establish `hrank : Module.finrank (v.adicCompletion F) (Kv E v) = 2`. Rewrite using `[Module.finrank_baseChange, h2]`. Establish `hred : IsReduced (Kv E v)`. Establish `: Algebra.IsSeparable F E` using `inferInstance`. Establish `: Algebra.FormallyUnramified F E` using `Algebra.FormallyUnramified.of_isSeparable F E`.

Conclude with `Algebra.FormallyUnramified.isReduced_of_field (v.adicCompletion F) (Kv E v)`. Use `⟨hinv, hfix, hrank, hred, h2k, hsig_incl, ?_⟩` and prove the remaining obligations. Introduce `N J x y`. Simplify using `only [hf, map_sum, map_mul, Matrix.map_apply, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hsig_incl]`. Both sides reduce to the same expression.
-/
theorem LocalRingHypotheses.proof : LocalRingHypotheses.Statement := by
  intro F E _ _ _ _ _ c h2 hc v
  have : Module.Finite F E := Module.finite_of_finrank_eq_succ h2

  have hcc : ∀ x, c (c x) = x := by
    have hcard : Fintype.card (E ≃ₐ[F] E) ≤ 2 := h2 ▸ AlgEquiv.card_le
    have hpos := orderOf_pos c
    have hle : orderOf c ≤ Fintype.card (E ≃ₐ[F] E) := orderOf_le_card_univ
    have hne : orderOf c ≠ 1 := fun h => hc (orderOf_eq_one_iff.mp h)
    have ho : orderOf c = 2 := by omega
    intro x
    have h := pow_orderOf_eq_one c
    rw [ho, pow_two] at h
    exact DFunLike.congr_fun h x
  have htmul : ∀ (a : v.adicCompletion F) (b : E), sigV c v (a ⊗ₜ b) = a ⊗ₜ c b := by
    intro a b
    simp [sigV]
  have hsig_incl : ∀ x : E, sigV c v (inclV E v x) = inclV E v (c x) := by
    intro x
    simp [inclV, htmul]

  have hinv : ∀ x, sigV c v (sigV c v x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rw [htmul, htmul, hcc]
    | add x y hx hy => rw [map_add, map_add, hx, hy]

  obtain ⟨α, hα⟩ : ∃ α, c α ≠ α := by
    by_contra h
    push Not at h
    exact hc (AlgEquiv.ext h)
  set β : E := α - c α with hβdef
  have hcβ : c β = -β := by simp [hβdef, hcc]
  have hβ0 : β ≠ 0 := sub_ne_zero.mpr (Ne.symm hα)
  have h2F : (2 : F) ≠ 0 := two_ne_zero
  have h2k : (2 : v.adicCompletion F) ≠ 0 := by
    rw [← map_ofNat (algebraMap F (v.adicCompletion F)) 2]
    exact fun h => h2F ((algebraMap F (v.adicCompletion F)).injective (h.trans (map_zero _).symm))

  set t : Kv E v := (1 : v.adicCompletion F) ⊗ₜ β with htdef
  have ht : IsUnit t :=
    (isUnit_iff_ne_zero.mpr hβ0).map (Algebra.TensorProduct.includeRight : E →ₐ[F] Kv E v)
  have hσt : sigV c v t = -t := by rw [htdef, htmul, hcβ, TensorProduct.tmul_neg]

  have hli : LinearIndependent F ![(1 : E), β] := by
    rw [LinearIndependent.pair_iff]
    intro s u hsu
    have hsu' : algebraMap F E s + algebraMap F E u * β = 0 := by
      simpa [Algebra.smul_def] using hsu
    have hc' : algebraMap F E s + algebraMap F E u * -β = 0 := by
      have := congrArg c hsu'
      rwa [map_add, map_mul, AlgEquiv.commutes, AlgEquiv.commutes, hcβ, map_zero] at this
    have hs : algebraMap F E (2 * s) = 0 := by
      rw [map_mul, map_ofNat]
      linear_combination hsu' + hc'
    have hs0 : s = 0 := by
      have := (algebraMap F E).injective (hs.trans (map_zero _).symm)
      exact (mul_eq_zero.mp this).resolve_left h2F
    subst hs0
    rw [map_zero, zero_add] at hsu'
    have hu : algebraMap F E u = 0 := (mul_eq_zero.mp hsu').resolve_right hβ0
    exact ⟨rfl, (algebraMap F E).injective (hu.trans (map_zero _).symm)⟩
  let B : Module.Basis (Fin 2) F E := basisOfLinearIndependentOfCardEqFinrank hli (by simp [h2])
  have hB : ∀ i, B i = ![(1 : E), β] i := fun i => by
    simp [B, coe_basisOfLinearIndependentOfCardEqFinrank]
  let BK : Module.Basis (Fin 2) (v.adicCompletion F) (Kv E v) := Algebra.TensorProduct.basis _ B

  have hdecomp : ∀ x : Kv E v, ∃ a b : v.adicCompletion F,
      x = algebraMap _ _ a + algebraMap _ _ b * t := by
    intro x
    refine ⟨BK.repr x 0, BK.repr x 1, ?_⟩
    conv_lhs => rw [← BK.sum_repr x]
    rw [Fin.sum_univ_two, Algebra.smul_def, Algebra.smul_def]
    simp [BK, Algebra.TensorProduct.basis_apply, hB, htdef]
  have hinj : Function.Injective (algebraMap (v.adicCompletion F) (Kv E v)) := by
    have : Nontrivial (Kv E v) := ⟨⟨0, t, (ht.ne_zero).symm⟩⟩
    exact (algebraMap (v.adicCompletion F) (Kv E v)).injective

  have hfix : ∀ x, sigV c v x = x ↔ x ∈ Set.range (algebraMap (v.adicCompletion F) (Kv E v)) := by
    intro x
    constructor
    · intro hx
      obtain ⟨a, b, rfl⟩ := hdecomp x
      rw [map_add, map_mul, AlgHom.commutes, AlgHom.commutes, hσt] at hx
      have h2b : algebraMap _ (Kv E v) (2 * b) * t = 0 := by
        rw [map_mul, map_ofNat]
        linear_combination -hx
      have hb : b = 0 := by
        have := (ht.mul_left_eq_zero).mp h2b
        rw [← map_zero (algebraMap (v.adicCompletion F) (Kv E v))] at this
        exact (mul_eq_zero.mp (hinj this)).resolve_left h2k
      exact ⟨a, by simp [hb]⟩
    · rintro ⟨a, rfl⟩
      exact AlgHom.commutes _ a

  have hrank : Module.finrank (v.adicCompletion F) (Kv E v) = 2 := by
    rw [Module.finrank_baseChange, h2]

  have hred : IsReduced (Kv E v) := by
    have : Algebra.IsSeparable F E := inferInstance
    have : Algebra.FormallyUnramified F E := Algebra.FormallyUnramified.of_isSeparable F E
    exact Algebra.FormallyUnramified.isReduced_of_field (v.adicCompletion F) (Kv E v)
  refine ⟨hinv, hfix, hrank, hred, h2k, hsig_incl, ?_⟩
  intro N J x y
  simp only [hf, map_sum, map_mul, Matrix.map_apply, Function.comp_apply, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, hsig_incl]
  rfl

end GroundTheory.Heights₂.Heights.StrongApprox
