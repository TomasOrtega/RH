import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsHermRingRat
import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitEqNormCompletionTensorOfIsInertAt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianValuationSplitCriterionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianSplitRankOneStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitOrderFgIdealProductStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MaxEvenLatticeRankOneSplitStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjugationInvariantValuationFieldStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorFixedByInvolutionIsBaseStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitLocalTensorProductSwapStatement

noncomputable section
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct NNReal

namespace GlobalTheory.CompanionTheory.KFin.Base

/- English proof (translation)
Rewrite using `[hH.symm, hH.add_right, map_add, ← hH.symm, ← hH.symm]`.
-/
theorem herm_add_left {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] {c : R →+* R} {h : V → V → R} (hH : IsHerm c h)
    (x y z : V) : h (x + y) z = h x z + h y z := by
  rw [hH.symm, hH.add_right, map_add, ← hH.symm, ← hH.symm]

/- English proof (translation)
Rewrite using `[hH.symm, hH.smul_right, map_mul, ← hH.symm]`.
-/
theorem herm_smul_left {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] {c : R →+* R} {h : V → V → R} (hH : IsHerm c h)
    (a : R) (x z : V) : h (a • x) z = c a * h x z := by
  rw [hH.symm, hH.smul_right, map_mul, ← hH.symm]

/- English proof (translation)
Unfold `HasBase`. Introduce `V _ _ _ h hH hP hiso L L' hL hL'`. Establish `hanis : ∀ z : V, h z z = 0 → z = 0`. Introduce `z hz`. Assume the negation of the conclusion as `hne`.

Establish `hex : ∃ y, h z y ≠ 0`. Assume the negation of the conclusion as `hall`. Simplify using `only [not_exists, ne_eq, not_not] at hall`. Conclude with `hne (hP.nondeg z hall)`. Take `⟨y, hy⟩` from `hex`.

Take `⟨b, hb⟩` from `hf _ hy`. Conclude with `hiso z (b • y) hz (by rw [hH.smul_right, mul_comm]; exact hb)`. Establish `key : ∀ (z w : V) (a b : R), a ∈ 𝔬 → b ∈ 𝔬 → h z z = a + c a → h w w = b + c b → h z w ∈ 𝔬` using `GlobalTheory.T.hermitian_valuation_split_criterion c 𝔬 W hf hinv hfix hck h𝔬 hWc hW0 hN h hH hanis`. Establish `h0 : ∀ x : V, h x 0 = 0` using `fun x => by simpa using hH.smul_right 0 x 0`. Set `M : Submodule 𝔬 V` to `{ carrier := {z | ∃ a ∈ 𝔬, h z z = a + c a} add_mem' := by`.

Introduce and unpack `z w ⟨a, ha, hz⟩ ⟨b, hb, hw⟩`. Use `⟨a + b + h z w, add_mem (add_mem ha hb) (key z w a b ha hb hz hw), ?_⟩` and prove the remaining obligations. Rewrite using `[herm_add_left hH, hH.add_right, hH.add_right, hz, hw, hH.symm z w, map_add, map_add]`. Expand and normalize the polynomial expressions, which then agree. Use the proof step `zero_mem' := ⟨0, zero_mem _, by rw [h0, map_zero, add_zero]⟩`.

Use the proof step `smul_mem' := by`. Introduce and unpack `r z ⟨a, ha, hz⟩`. Use `⟨c r * r * a, ?_, ?_⟩` and prove the remaining obligations. Establish `hr : W (r : R) ≤ 1` using `(h𝔬 r).1 r.2`. Rewrite using `[h𝔬, map_mul, map_mul, hWc]`.

Conclude with `mul_le_one' (mul_le_one' hr hr) ((h𝔬 a).1 ha)`. Rewrite using `[Subring.smul_def, herm_smul_left hH, hH.smul_right, hz, map_mul, map_mul, hinv]`. Use `ring }`. Establish `hLM : ∀ N : Submodule 𝔬 V, IsEvenInt c 𝔬 h N → N ≤ M`. Introduce `N hN' x hx`.

Unfold `IsEvenInt at hN'`. Conclude with `hN'.2 x hx`. Establish `hMe : IsEvenInt c 𝔬 h M`. Unfold `IsEvenInt`. Use `⟨?_, fun x hx => hx⟩` and prove the remaining obligations.

Introduce and unpack `x ⟨a, ha, hx⟩ y ⟨b, hb, hy⟩`. Conclude with `key x y a b ha hb hx hy`. Establish `heq : ∀ N : Submodule 𝔬 V, IsMaxEven c 𝔬 h N → N = M`. Introduce `N hN'`. Unfold `IsMaxEven at hN'`.

Conclude with `le_antisymm (hLM N hN'.2.1) (hN'.2.2 M hMe (hLM N hN'.2.1))`. Use `⟨LinearEquiv.refl R V, ?_⟩` and prove the remaining obligations. Unfold `IsIsomOnto`. Use `⟨fun x y => rfl, fun z => ?_⟩` and prove the remaining obligations. Rewrite using `[heq L hL, heq L' hL']`.

Both sides reduce to the same expression.
-/
theorem hasBase_of_field {k R : Type} [Field k] [CommRing R] [Algebra k R] (c : R →+* R) (𝔬 : Subring R) (W : Valuation R ℝ≥0)
    (hf : ∀ a : R, a ≠ 0 → ∃ b : R, a * b = 1) (hinv : ∀ a, c (c a) = a)
    (hfix : ∀ a, c a = a → ∃ x : k, algebraMap k R x = a)
    (hck : ∀ x : k, c (algebraMap k R x) = algebraMap k R x) (h𝔬 : ∀ a, a ∈ 𝔬 ↔ W a ≤ 1)
    (hWc : ∀ a, W (c a) = W a) (hW0 : ∀ a, W a = 0 → a = 0)
    (hN : ∀ e : k, W (algebraMap k R e) < 1 → ∃ u : k, u * u + u + e = 0) : HasBase c 𝔬 := by
  unfold HasBase
  intro V _ _ _ h hH hP hiso L L' hL hL'
  have hanis : ∀ z : V, h z z = 0 → z = 0 := by
    intro z hz
    by_contra hne
    have hex : ∃ y, h z y ≠ 0 := by
      by_contra hall
      simp only [not_exists, ne_eq, not_not] at hall
      exact hne (hP.nondeg z hall)
    obtain ⟨y, hy⟩ := hex
    obtain ⟨b, hb⟩ := hf _ hy
    exact hiso z (b • y) hz (by rw [hH.smul_right, mul_comm]; exact hb)
  have key : ∀ (z w : V) (a b : R), a ∈ 𝔬 → b ∈ 𝔬 → h z z = a + c a → h w w = b + c b → h z w ∈ 𝔬 :=
    GlobalTheory.T.hermitian_valuation_split_criterion c 𝔬 W hf hinv hfix hck h𝔬 hWc hW0 hN h hH hanis
  have h0 : ∀ x : V, h x 0 = 0 := fun x => by simpa using hH.smul_right 0 x 0
  let M : Submodule 𝔬 V :=
    { carrier := {z | ∃ a ∈ 𝔬, h z z = a + c a}
      add_mem' := by
        rintro z w ⟨a, ha, hz⟩ ⟨b, hb, hw⟩
        refine ⟨a + b + h z w, add_mem (add_mem ha hb) (key z w a b ha hb hz hw), ?_⟩
        rw [herm_add_left hH, hH.add_right, hH.add_right, hz, hw, hH.symm z w, map_add, map_add]
        ring
      zero_mem' := ⟨0, zero_mem _, by rw [h0, map_zero, add_zero]⟩
      smul_mem' := by
        rintro r z ⟨a, ha, hz⟩
        refine ⟨c r * r * a, ?_, ?_⟩
        · have hr : W (r : R) ≤ 1 := (h𝔬 r).1 r.2
          rw [h𝔬, map_mul, map_mul, hWc]
          exact mul_le_one' (mul_le_one' hr hr) ((h𝔬 a).1 ha)
        · rw [Subring.smul_def, herm_smul_left hH, hH.smul_right, hz, map_mul, map_mul, hinv]
          ring }
  have hLM : ∀ N : Submodule 𝔬 V, IsEvenInt c 𝔬 h N → N ≤ M := by
    intro N hN' x hx
    unfold IsEvenInt at hN'
    exact hN'.2 x hx
  have hMe : IsEvenInt c 𝔬 h M := by
    unfold IsEvenInt
    refine ⟨?_, fun x hx => hx⟩
    rintro x ⟨a, ha, hx⟩ y ⟨b, hb, hy⟩
    exact key x y a b ha hb hx hy
  have heq : ∀ N : Submodule 𝔬 V, IsMaxEven c 𝔬 h N → N = M := by
    intro N hN'
    unfold IsMaxEven at hN'
    exact le_antisymm (hLM N hN'.2.1) (hN'.2.2 M hMe (hLM N hN'.2.1))
  refine ⟨LinearEquiv.refl R V, ?_⟩
  unfold IsIsomOnto
  refine ⟨fun x y => rfl, fun z => ?_⟩
  rw [heq L hL, heq L' hL']
  rfl

/- English proof (translation)
Unfold `HasBase`. Introduce `V _ _ _ h hH hP hiso L L' hL hL'`. Break down `GlobalTheory.T.hermitian_split_rank_one φ c hc h hH hP hiso with hsub | ⟨w₀, hspan, hunit⟩` into its components or cases. Use `⟨LinearEquiv.refl R V, ?_⟩` and prove the remaining obligations. Unfold `IsIsomOnto`.

Use `⟨fun _ _ => rfl, fun z => ?_⟩` and prove the remaining obligations. Rewrite using `[Subsingleton.elim z 0, LinearEquiv.refl_apply]`. Conclude with `⟨fun _ => L'.zero_mem, fun _ => L.zero_mem⟩`. Set `f : R →ₗ[𝔬] V` to `{ toFun := fun r => r • w₀ map_add' := fun a b => add_smul a b w₀ map_smul' := fun s r => by`. Simplify using `only [RingHom.id_apply, Subring.smul_def, smul_eq_mul, mul_smul] }`.

Establish `hf : ∀ r, f r = r • w₀` using `fun r => rfl`. Establish `finj : Function.Injective f`. Introduce `a b hab`. Rewrite `hab` using `[hf, hf]`. Establish `h1` using `congrArg (h w₀) hab`.

Rewrite `h1` using `[hH.smul_right, hH.smul_right]`. Conclude with `hunit.mul_left_injective h1`. Establish `fsurj : Function.Surjective f` using `fun x => by`. Take `⟨r, hr⟩` from `hspan x`. Conclude with `⟨r, by rw [hf, hr]⟩`.

Establish `desc : ∀ N : Submodule 𝔬 V, IsMaxEven c 𝔬 h N → ∃ α β : k, (α ≠ 0 ∧ β ≠ 0 ∧ ∃ u ∈ O, u⁻¹ ∈ O ∧ α * β * (φ (h w₀ w₀)).1 = u) ∧ ∀ r : R, r • w₀ ∈ N ↔ (∃ x ∈ O, (φ r).1 = α * x) ∧ ∃ y ∈ O, (φ r).2 = β * y`. Introduce `N hN`. Establish `hNfg : N.FG`. Establish `h'` using `hN`. Unfold `IsMaxEven IsLat at h'`.

Conclude with `h'.1.1`. Establish `hfg : (N.comap f).FG`. Apply `Submodule.fg_of_fg_map_injective f finj` to reduce the goal to its premises. Rewrite using `[Submodule.map_comap_eq_of_surjective fsurj]`. Conclude with `hNfg`.

Take `⟨α, β, hαβ⟩` from `GlobalTheory.T.split_order_fg_ideal_product O φ 𝔬 h𝔬 (N.comap f) hfg`. Establish `hαβ' : ∀ r : R, r • w₀ ∈ N ↔ (∃ x ∈ O, (φ r).1 = α * x) ∧ ∃ y ∈ O, (φ r).2 = β * y` using `fun r => hαβ r`. Conclude with `⟨α, β, GlobalTheory.T.max_even_lattice_rank_one_split O φ c 𝔬 hc h𝔬 h hH w₀ hspan hunit N hN α β hαβ', hαβ'⟩`. Take `⟨α, β, ⟨hα, hβ, u, hu, hu', hud⟩, hL1⟩` from `desc L hL`. Take `⟨α', β', ⟨hα', hβ', u', hu2, hu2', hud'⟩, hL2⟩` from `desc L' hL'`.

Establish `hd0 : (φ (h w₀ w₀)).1 ≠ 0`. Introduce `h0`. Take `⟨t, ht⟩` from `hunit.exists_right_inv`. Establish `h2` using `congrArg (fun x => (φ x).1) ht`. Simplify using `only [map_mul, Prod.fst_mul, map_one, Prod.fst_one, h0, zero_mul] at h2`.

Conclude with `zero_ne_one h2`. Establish `hs : α' / α * (α / α') = 1` using `by field_simp`. Set `us : Rˣ` to `{ val := φ.symm (α' / α, α / α') inv := φ.symm (α / α', α' / α) val_inv := by`. Apply `φ.injective` to reduce the goal to its premises. Apply the tactic sequence `rw [map_mul, map_one, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, Prod.mk_mul_mk, hs, mul_comm (α / α') (α' / α), hs] <;> rfl`.

Use `inv_val := by`. Apply `φ.injective` to reduce the goal to its premises. Apply the tactic sequence `rw [map_mul, map_one, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, Prod.mk_mul_mk, mul_comm (α / α') (α' / α), hs] <;> rfl }`. Set `p : V ≃ₗ[R] V` to `LinearEquiv.smulOfUnit us`. Establish `hp : ∀ x, p x = φ.symm (α' / α, α / α') • x` using `fun x => rfl`.

Use `⟨p, ?_⟩` and prove the remaining obligations. Unfold `IsIsomOnto`. Use `⟨fun x y => ?_, fun z => ?_⟩` and prove the remaining obligations. Establish `hcs : c (φ.symm (α' / α, α / α')) * φ.symm (α' / α, α / α') = 1`. Apply `φ.injective` to reduce the goal to its premises.

Apply the tactic sequence `rw [map_mul, hc, RingEquiv.apply_symm_apply, map_one, Prod.swap_prod_mk, Prod.mk_mul_mk, mul_comm (α / α') (α' / α), hs] <;> rfl`. Rewrite using `[hp, hp, herm_smul_left hH, hH.smul_right, ← mul_assoc, hcs, one_mul]`. Take `⟨r, rfl⟩` from `hspan z`. Rewrite using `[hp, smul_smul, hL1, hL2]`. Establish `e1 : (φ (φ.symm (α' / α, α / α') * r)).1 = α' / α * (φ r).1`.

Rewrite using `[map_mul, RingEquiv.apply_symm_apply]`. Both sides reduce to the same expression. Establish `e2 : (φ (φ.symm (α' / α, α / α') * r)).2 = α / α' * (φ r).2`. Rewrite using `[map_mul, RingEquiv.apply_symm_apply]`. Both sides reduce to the same expression.

Rewrite using `[e1, e2]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨x, hx, hx1⟩, ⟨y, hy, hy1⟩⟩`. Use `⟨⟨x, hx, ?_⟩, ⟨u * u'⁻¹ * y, mul_mem (mul_mem hu hu2') hy, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[hx1]`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[hy1, ← hud, ← hud']`. Apply the tactic sequence `field_simp <;> ring`. Introduce and unpack `⟨⟨x, hx, hx1⟩, ⟨y, hy, hy1⟩⟩`. Use `⟨⟨x, hx, ?_⟩, ⟨u' * u⁻¹ * y, mul_mem (mul_mem hu2 hu') hy, ?_⟩⟩` and prove the remaining obligations.

Establish `h3 : (φ r).1 = α / α' * (α' / α * (φ r).1)` using `by field_simp`. Rewrite using `[h3, hx1]`. Clear the denominators using the available nonvanishing facts. Establish `h3 : (φ r).2 = α' / α * (α / α' * (φ r).2)` using `by field_simp`. Rewrite using `[h3, hy1, ← hud, ← hud']`.

Apply the tactic sequence `field_simp <;> ring`.
-/
theorem hasBase_of_split {k R : Type} [Field k] [CommRing R] (O : ValuationSubring k) (φ : R ≃+* k × k) (c : R →+* R)
    (𝔬 : Subring R) (hc : ∀ r, φ (c r) = (φ r).swap) (h𝔬 : ∀ r, r ∈ 𝔬 ↔ (φ r).1 ∈ O ∧ (φ r).2 ∈ O) : HasBase c 𝔬 := by
  unfold HasBase
  intro V _ _ _ h hH hP hiso L L' hL hL'
  rcases GlobalTheory.T.hermitian_split_rank_one φ c hc h hH hP hiso with hsub | ⟨w₀, hspan, hunit⟩
  · refine ⟨LinearEquiv.refl R V, ?_⟩
    unfold IsIsomOnto
    refine ⟨fun _ _ => rfl, fun z => ?_⟩
    rw [Subsingleton.elim z 0, LinearEquiv.refl_apply]
    exact ⟨fun _ => L'.zero_mem, fun _ => L.zero_mem⟩
  · let f : R →ₗ[𝔬] V :=
      { toFun := fun r => r • w₀
        map_add' := fun a b => add_smul a b w₀
        map_smul' := fun s r => by
          simp only [RingHom.id_apply, Subring.smul_def, smul_eq_mul, mul_smul] }
    have hf : ∀ r, f r = r • w₀ := fun r => rfl
    have finj : Function.Injective f := by
      intro a b hab
      rw [hf, hf] at hab
      have h1 := congrArg (h w₀) hab
      rw [hH.smul_right, hH.smul_right] at h1
      exact hunit.mul_left_injective h1
    have fsurj : Function.Surjective f := fun x => by
      obtain ⟨r, hr⟩ := hspan x
      exact ⟨r, by rw [hf, hr]⟩
    have desc : ∀ N : Submodule 𝔬 V, IsMaxEven c 𝔬 h N → ∃ α β : k,
        (α ≠ 0 ∧ β ≠ 0 ∧ ∃ u ∈ O, u⁻¹ ∈ O ∧ α * β * (φ (h w₀ w₀)).1 = u) ∧
        ∀ r : R, r • w₀ ∈ N ↔ (∃ x ∈ O, (φ r).1 = α * x) ∧ ∃ y ∈ O, (φ r).2 = β * y := by
      intro N hN
      have hNfg : N.FG := by
        have h' := hN
        unfold IsMaxEven IsLat at h'
        exact h'.1.1
      have hfg : (N.comap f).FG := by
        apply Submodule.fg_of_fg_map_injective f finj
        rw [Submodule.map_comap_eq_of_surjective fsurj]
        exact hNfg
      obtain ⟨α, β, hαβ⟩ := GlobalTheory.T.split_order_fg_ideal_product O φ 𝔬 h𝔬 (N.comap f) hfg
      have hαβ' : ∀ r : R, r • w₀ ∈ N ↔ (∃ x ∈ O, (φ r).1 = α * x) ∧ ∃ y ∈ O, (φ r).2 = β * y :=
        fun r => hαβ r
      exact ⟨α, β, GlobalTheory.T.max_even_lattice_rank_one_split O φ c 𝔬 hc h𝔬 h hH w₀ hspan hunit N hN α β hαβ', hαβ'⟩
    obtain ⟨α, β, ⟨hα, hβ, u, hu, hu', hud⟩, hL1⟩ := desc L hL
    obtain ⟨α', β', ⟨hα', hβ', u', hu2, hu2', hud'⟩, hL2⟩ := desc L' hL'
    have hd0 : (φ (h w₀ w₀)).1 ≠ 0 := by
      intro h0
      obtain ⟨t, ht⟩ := hunit.exists_right_inv
      have h2 := congrArg (fun x => (φ x).1) ht
      simp only [map_mul, Prod.fst_mul, map_one, Prod.fst_one, h0, zero_mul] at h2
      exact zero_ne_one h2
    have hs : α' / α * (α / α') = 1 := by field_simp
    let us : Rˣ :=
      { val := φ.symm (α' / α, α / α')
        inv := φ.symm (α / α', α' / α)
        val_inv := by
          apply φ.injective
          rw [map_mul, map_one, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, Prod.mk_mul_mk, hs,
            mul_comm (α / α') (α' / α), hs] <;> rfl
        inv_val := by
          apply φ.injective
          rw [map_mul, map_one, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, Prod.mk_mul_mk,
            mul_comm (α / α') (α' / α), hs] <;> rfl }
    let p : V ≃ₗ[R] V := LinearEquiv.smulOfUnit us
    have hp : ∀ x, p x = φ.symm (α' / α, α / α') • x := fun x => rfl
    refine ⟨p, ?_⟩
    unfold IsIsomOnto
    refine ⟨fun x y => ?_, fun z => ?_⟩
    · have hcs : c (φ.symm (α' / α, α / α')) * φ.symm (α' / α, α / α') = 1 := by
        apply φ.injective
        rw [map_mul, hc, RingEquiv.apply_symm_apply, map_one, Prod.swap_prod_mk, Prod.mk_mul_mk,
          mul_comm (α / α') (α' / α), hs] <;> rfl
      rw [hp, hp, herm_smul_left hH, hH.smul_right, ← mul_assoc, hcs, one_mul]
    · obtain ⟨r, rfl⟩ := hspan z
      rw [hp, smul_smul, hL1, hL2]
      have e1 : (φ (φ.symm (α' / α, α / α') * r)).1 = α' / α * (φ r).1 := by
        rw [map_mul, RingEquiv.apply_symm_apply]; rfl
      have e2 : (φ (φ.symm (α' / α, α / α') * r)).2 = α / α' * (φ r).2 := by
        rw [map_mul, RingEquiv.apply_symm_apply]; rfl
      rw [e1, e2]
      constructor
      · rintro ⟨⟨x, hx, hx1⟩, ⟨y, hy, hy1⟩⟩
        refine ⟨⟨x, hx, ?_⟩, ⟨u * u'⁻¹ * y, mul_mem (mul_mem hu hu2') hy, ?_⟩⟩
        · rw [hx1]
          field_simp
        · rw [hy1, ← hud, ← hud']
          field_simp <;> ring
      · rintro ⟨⟨x, hx, hx1⟩, ⟨y, hy, hy1⟩⟩
        refine ⟨⟨x, hx, ?_⟩, ⟨u' * u⁻¹ * y, mul_mem (mul_mem hu2 hu') hy, ?_⟩⟩
        · have h3 : (φ r).1 = α / α' * (α' / α * (φ r).1) := by field_simp
          rw [h3, hx1]
          field_simp
        · have h3 : (φ r).2 = α' / α * (α / α' * (φ r).2) := by field_simp
          rw [h3, hy1, ← hud, ← hud']
          field_simp <;> ring

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hcm v`. Distinguish the cases in `hF : IsField (Fv F v ⊗[F] E)`. Take `⟨W, hW, hWc⟩` from `GlobalTheory.T.conjugation_invariant_valuation_field hcm v hF`. Use `hasBase_of_field (k := Fv F v) (sigR (Fv F v) σ) (intLoc F E v) W (fun a ha => hF.mul_inv_cancel ha) ?_ (fun a ha => GlobalTheory.T.tensor_fixed_by_involution_is_base hcm (Fv F v) a ha) ?_ ?_ hWc ?_ ?_` and prove the remaining obligations. Introduce `a`.

Proceed by induction on `a using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x y => simp [sigR, GlobalTheory.AdelicU.cm_conj_conj hcm]`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`. Introduce `x`.

Simplify using `[sigR, Algebra.TensorProduct.algebraMap_apply]`. Introduce `a`. Rewrite using `[hW]`. Conclude with `mem_intLoc_iff_absFin_le_one`. Introduce `a ha`.

Assume the negation of the conclusion as `hne`. Take `⟨b, hb⟩` from `hF.mul_inv_cancel hne`. Establish `h2` using `congrArg W hb`. Rewrite `h2` using `[map_mul, ha, zero_mul, map_one]`. Conclude with `zero_ne_one h2`.

Introduce `e he replace he : ‖e‖₊ < 1 := by`. Rewrite `he` using `[hW]`. Simplify `he` using `[Algebra.TensorProduct.algebraMap_apply, absFin_tmul_one]`. Establish `he1 : e ∈ HeightOneSpectrum.adicCompletionIntegers F v` using `nnnorm_le_one_iff_mem.1 he.le`. Establish `hv : Valued.v e < 1`.

Establish `hle1 : Valued.v e ≤ 1` using `he1`. Break down `lt_or_eq_of_le hle1 with h1 | h1` into its components or cases. Conclude with `h1`. It suffices to derive a contradiction. Establish `he0 : e ≠ 0`.

Introduce `h0`. Rewrite `h1` using `[h0, map_zero]`. Conclude with `zero_ne_one h1`. Establish `hinvm : e⁻¹ ∈ HeightOneSpectrum.adicCompletionIntegers F v` using `by show Valued.v e⁻¹ ≤ 1`. Rewrite using `[map_inv₀, h1, inv_one]`.

Establish `hle` using `nnnorm_le_one_iff_mem.2 hinvm`. Establish `h2 : ‖e * e⁻¹‖₊ = 1` using `by rw [mul_inv_cancel₀ he0, nnnorm_one]`. Rewrite `h2` using `[nnnorm_mul]`. Establish `h3 : ‖e‖₊ * ‖e⁻¹‖₊ < 1` using `lt_of_le_of_lt (mul_le_of_le_one_right zero_le hle) he`. Rewrite `h3` using `[h2]`.

Conclude with `lt_irrefl _ h3`. Take `⟨a, ha⟩` from `GlobalTheory.InertUnitNorm.exists_root_quadratic_of_approx v 1 ⟨e, he1⟩ 0 (by simpa using hv) (by simp)`. Use `⟨(a : Fv F v), ?_⟩` and prove the remaining obligations. Establish `h2 : (a : Fv F v) ^ 2 + 1 * (a : Fv F v) + e = 0`. Establish `h3` using `congrArg Subtype.val ha`.

Simplify using `using h3`. Take the linear combination `h2`. Take `⟨φ, hφc, hφ𝔬⟩` from `GlobalTheory.T.split_local_tensor_product_swap hcm v hF`. Conclude with `hasBase_of_split (HeightOneSpectrum.adicCompletionIntegers F v) φ _ _ hφc hφ𝔬`.
-/
theorem hasBase_place : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}, IsCMExt F E σ → ∀ (v : HeightOneSpectrum (𝓞 F)), HasBase (sigR (Fv F v) σ) (intLoc F E v) := by
  intro F E _ _ _ _ _ σ hcm v
  by_cases hF : IsField (Fv F v ⊗[F] E)
  · obtain ⟨W, hW, hWc⟩ := GlobalTheory.T.conjugation_invariant_valuation_field hcm v hF
    refine hasBase_of_field (k := Fv F v) (sigR (Fv F v) σ) (intLoc F E v) W
      (fun a ha => hF.mul_inv_cancel ha) ?_ (fun a ha => GlobalTheory.T.tensor_fixed_by_involution_is_base hcm (Fv F v) a ha) ?_ ?_ hWc ?_ ?_
    · intro a
      induction a using TensorProduct.induction_on with
      | zero => simp
      | tmul x y => simp [sigR, GlobalTheory.AdelicU.cm_conj_conj hcm]
      | add x y hx hy => rw [map_add, map_add, hx, hy]
    · intro x
      simp [sigR, Algebra.TensorProduct.algebraMap_apply]
    · intro a
      rw [hW]
      exact mem_intLoc_iff_absFin_le_one
    · intro a ha
      by_contra hne
      obtain ⟨b, hb⟩ := hF.mul_inv_cancel hne
      have h2 := congrArg W hb
      rw [map_mul, ha, zero_mul, map_one] at h2
      exact zero_ne_one h2
    · intro e he
      replace he : ‖e‖₊ < 1 := by
        rw [hW] at he
        simpa [Algebra.TensorProduct.algebraMap_apply, absFin_tmul_one] using he
      have he1 : e ∈ HeightOneSpectrum.adicCompletionIntegers F v := nnnorm_le_one_iff_mem.1 he.le
      have hv : Valued.v e < 1 := by
        have hle1 : Valued.v e ≤ 1 := he1
        rcases lt_or_eq_of_le hle1 with h1 | h1
        · exact h1
        · exfalso
          have he0 : e ≠ 0 := by
            intro h0
            rw [h0, map_zero] at h1
            exact zero_ne_one h1
          have hinvm : e⁻¹ ∈ HeightOneSpectrum.adicCompletionIntegers F v := by
            show Valued.v e⁻¹ ≤ 1
            rw [map_inv₀, h1, inv_one]
          have hle := nnnorm_le_one_iff_mem.2 hinvm
          have h2 : ‖e * e⁻¹‖₊ = 1 := by rw [mul_inv_cancel₀ he0, nnnorm_one]
          rw [nnnorm_mul] at h2
          have h3 : ‖e‖₊ * ‖e⁻¹‖₊ < 1 := lt_of_le_of_lt (mul_le_of_le_one_right zero_le hle) he
          rw [h2] at h3
          exact lt_irrefl _ h3
      obtain ⟨a, ha⟩ := GlobalTheory.InertUnitNorm.exists_root_quadratic_of_approx v 1 ⟨e, he1⟩ 0
        (by simpa using hv) (by simp)
      refine ⟨(a : Fv F v), ?_⟩
      have h2 : (a : Fv F v) ^ 2 + 1 * (a : Fv F v) + e = 0 := by
        have h3 := congrArg Subtype.val ha
        simpa using h3
      linear_combination h2
  · obtain ⟨φ, hφc, hφ𝔬⟩ := GlobalTheory.T.split_local_tensor_product_swap hcm v hF
    exact hasBase_of_split (HeightOneSpectrum.adicCompletionIntegers F v) φ _ _ hφc hφ𝔬

end GlobalTheory.CompanionTheory.KFin.Base
