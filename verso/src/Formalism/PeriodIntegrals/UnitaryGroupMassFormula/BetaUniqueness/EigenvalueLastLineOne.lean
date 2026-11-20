import Mathlib
import Formalism.PeriodIntegrals.BetaLUniq
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.Skeleton
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.Lemmas
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.EqZeroOfNormLtOne
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.FlagVectorMemLocalization
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.WAniso
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.CMNorm

noncomputable section

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat IsDedekindDomain
open PI.UnitaryGroupMassFormula.BetaLUniq.EigA PI.UnitaryGroupMassFormula.BetaLUniq.EigB

namespace PI.UnitaryGroupMassFormula.BetaLUniq

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E}

/- English proof (translation)
Take `⟨ξ', hA'⟩` from `hA'`. Take `⟨ξ'', hA''⟩` from `hA''`. Use `set X' := Xsp F' with hX'`. Set `γ : S.V →ₗ[E] S.V` to `(β₁.symm : S.V →ₗ[E] S.V) ∘ₗ (β₂ : S.V →ₗ[E] S.V)`. Establish `hγ : ∀ x, γ x = β₁.symm (β₂ x)` using `fun x => rfl`.

Establish `hγX : ∀ x ∈ X', γ x ∈ X'`. Introduce `x hx`. Rewrite using `[hγ]`. Apply `symm_mem_X hP1.2.1` to reduce the goal to its premises. Rewrite using `[← Xflag_r, ← hP2.2.1 r]`.

Conclude with `Submodule.mem_map_of_mem (by rw [Xflag_r]; exact hx)`. Establish `hγΛ : ∀ x ∈ Λ, γ x ∈ Λ`. Introduce `x hx`. Rewrite using `[hγ]`. Apply `symm_mem hP1.1` to reduce the goal to its premises.

Establish `h2` using `hP2.1.2`. Unfold `Formalism.HermitianLatticesTheory.gmap at h2`. Rewrite using `[← h2]`. Conclude with `⟨x, hx, rfl⟩`. Establish `hiso2 : ∀ x y, S.hT (β₂ x) (β₂ y) = S.hT x y` using `hP2.1.1`.

Establish `hiso1 : ∀ x y, S.hT (β₁.symm x) (β₁.symm y) = S.hT x y`. Introduce `x y`. Use `hP1.1.1 (β₁.symm x) (β₁.symm y)` as an intermediate fact. Simplify using `using this.symm`. Establish `hγiso : ∀ x y, S.hT (γ x) (γ y) = S.hT x y`.

Introduce `x y`. Rewrite using `[hγ, hγ, hiso1, hiso2]`. Establish `hXXplus : X' ≤ Xplus F'` using `le_sup_left`. Establish `hvo : v ∈ orth S X'`. Rewrite `hv`, the goal using `[mem_orth]`.

Conclude with `fun x hx => hv x (hXXplus hx)`. Use `set x₀ := γ v - μ • v with hx₀`. Establish `hx₀X : x₀ ∈ X'` using `hμ`. Establish `hγv : γ v = μ • v + x₀` using `by rw [hx₀]; abel`. Establish `hstar : star μ * μ = 1`.

Establish `h1` using `hγiso v v`. Rewrite `h1` using `[hγv]`. Establish `e1 : S.hT x₀ v = 0` using `(mem_orth S).mp hvo x₀ hx₀X`. Establish `e2 : S.hT v x₀ = 0` using `by rw [hT_swap, e1, star_zero]`. Establish `e3 : S.hT x₀ x₀ = 0` using `hT_X F' hx₀X hx₀X`.

Simplify using `only [map_add, LinearMap.add_apply, hT_smul_left, hT_smul_right, e1, e2, e3] at h1`. Establish `h2 : (star μ * μ - 1) * S.hT v v = 0` using `by linear_combination h1`. Break down `mul_eq_zero.mp h2 with h | h` into its components or cases. Conclude with `sub_eq_zero.mp h`. Conclude with `absurd h hvv`.

Establish `hnorm` using `hCM μ hstar`. Establish `hqv : (X'.mkQ v) ≠ 0`. Rewrite using `[Submodule.mkQ_apply, Ne, Submodule.Quotient.mk_eq_zero]`. Conclude with `hvX`. Choose the witnesses or unpack the hypotheses as in `⟨f, hf⟩ : ∃ f : Module.Dual E (S.V ⧸ X'), f (X'.mkQ v) ≠ 0 := by`.

Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `hqv ((Module.forall_dual_apply_eq_zero_iff E _).mp h)`. Set `π : S.V →ₗ[E] E` to `(f (X'.mkQ v))⁻¹ • (f ∘ₗ X'.mkQ)`. Establish `hπv : π v = 1`.

Simplify using `only [π, LinearMap.smul_apply, LinearMap.comp_apply, smul_eq_mul]`. Conclude with `inv_mul_cancel₀ hf`. Establish `hπX : ∀ x ∈ X', π x = 0`. Introduce `x hx`. Simplify using `only [π, LinearMap.smul_apply, LinearMap.comp_apply, smul_eq_mul, (Submodule.Quotient.mk_eq_zero X').mpr hx, Submodule.mkQ_apply, map_zero, mul_zero]`.

Use `set W : Submodule E S.V := Submodule.span E {v} ⊔ X' with hW`. Establish `hdec : ∀ y ∈ W, y - π y • v ∈ X'`. Introduce `y hy`. Take `⟨a, ha, x, hx, rfl⟩` from `Submodule.mem_sup.mp hy`. Take `⟨c, rfl⟩` from `Submodule.mem_span_singleton.mp ha`.

Establish `: π (c • v + x) = c` using `by rw [map_add, map_smul, hπv, hπX x hx, smul_eq_mul]; ring`. Rewrite using `[this]`. Simplify using `using hx`. Establish `hWeq : ∀ y ∈ W, y = π y • v + (y - π y • v)` using `fun y _ => by abel`. Establish `hvW : v ∈ W` using `Submodule.mem_sup_left (Submodule.mem_span_singleton_self v)`.

Establish `hXW : X' ≤ W` using `le_sup_right`. Establish `hγW : ∀ y ∈ W, γ y ∈ W ∧ π (γ y) = μ * π y`. Introduce `y hy`. Establish `h1` using `hWeq y hy`. Establish `h2 : γ y = (π y * μ) • v + (π y • x₀ + γ (y - π y • v))` using `by conv_lhs => rw [h1]`.

Rewrite using `[map_add, map_smul, hγv, smul_add, smul_smul]`. Normalize the expressions using the abelian group laws. Prove the components needed by the constructor for the conclusion. Rewrite using `[h2]`. Conclude with `W.add_mem (W.smul_mem _ hvW) (hXW (X'.add_mem (X'.smul_mem _ hx₀X) (hγX _ (hdec y hy))))`.

Rewrite using `[h2, map_add, map_smul, hπv, map_add, map_smul, hπX _ hx₀X, hπX _ (hγX _ (hdec y hy))]`. Simplify using `only [smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hWo : W ≤ orth S X'`. Apply `sup_le` to reduce the goal to its premises.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ rfl`. Conclude with `hvo`. Introduce `x hx`. Rewrite using `[mem_orth]`.

Introduce `y hy`. Conclude with `hT_X F' hy hx`. Set `I : Submodule (𝓞 E) E` to `(Λ ⊓ toO S W).map (π.restrictScalars (𝓞 E))`. Establish `hmemI : ∀ c, c ∈ I ↔ ∃ y ∈ Λ, y ∈ W ∧ π y = c`. Introduce `c`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, ⟨hyΛ, hyW⟩, rfl⟩`. Conclude with `⟨y, hyΛ, hyW, rfl⟩`. Introduce and unpack `⟨y, hyΛ, hyW, rfl⟩`. Conclude with `⟨y, ⟨hyΛ, hyW⟩, rfl⟩`.

Establish `hIfg : I.FG`. Establish `hN : IsNoetherian (𝓞 E) Λ` using `isNoetherian_of_fg_of_noetherian Λ hL.fg`. Establish `h1` using `(IsNoetherian.noetherian ((toO S W).comap Λ.subtype)).map Λ.subtype`. Rewrite `h1` using `[Submodule.map_comap_subtype]`. Conclude with `h1.map _`.

Establish `hI0 : I ≠ ⊥`. Take `⟨a, ha, haΛ⟩` from `exists_smul_mem S Λ hL v`. Introduce `hbot`. Establish `: π (a • v) ∈ I` using `(hmemI _).mpr ⟨a • v, haΛ, W.smul_of_tower_mem a hvW, rfl⟩`. Rewrite `this` using `[hbot, Submodule.mem_bot, smulO, map_smul, hπv, smul_eq_mul, mul_one]`.

Conclude with `ha (algebraMap_injO (this.trans (map_zero _).symm))`. Establish `hμO : InO μ`. Apply `mem_O_of_stable I hI0 hIfg μ` to reduce the goal to its premises. Introduce `c hc`. Take `⟨y, hyΛ, hyW, rfl⟩` from `(hmemI c).mp hc`.

Conclude with `(hmemI _).mpr ⟨γ y, hγΛ y hyΛ, (hγW y hyW).1, (hγW y hyW).2⟩`. Establish `hg0 : (g : E) ≠ 0` using `Nat.cast_ne_zero.mpr (by omega)`. Establish `hνO : InO ((μ - 1) / (g : E))`. Apply `mem_O_of_local` to reduce the goal to its premises. Introduce `P hPm`.

Distinguish the cases in `hgP : (g : 𝓞 E) ∈ P`. Set `P' : HeightOneSpectrum (𝓞 E)` to `⟨P, hPm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hPm (RingOfIntegers.not_isField E)⟩`. Establish `hloc : ∀ c ∈ I, ∃ s : 𝓞 E, s ∉ P ∧ algebraMap (𝓞 E) E s * ((μ - 1) / (g : E)) * c ∈ I`. Introduce `c hc`. Take `⟨y, hyΛ, hyW, rfl⟩` from `(hmemI c).mp hc`.

Take `⟨s, hs, hsm⟩` from `cong β₁ β₂ hU hFC hA' hA'' hP1 hP2 P' hgP y hyΛ (hWo hyW)`. Take `⟨z₁, hz₁, w, hw, hz⟩` from `Submodule.mem_sup.mp hsm`. Take `⟨l, hl, rfl⟩` from `mem_gΛ (Λ := Λ) g hz₁`. Rewrite `hz` using `[← hγ y]`. Use `⟨s, hs, (hmemI _).mpr ⟨l, hl, ?_, ?_⟩⟩` and prove the remaining obligations.

Establish `hgl : (g : 𝓞 E) • l ∈ W`. Establish `: (g : 𝓞 E) • l = s • (γ y - y) - w` using `by rw [← hz]; abel`. Rewrite using `[this]`. Conclude with `W.sub_mem (W.smul_of_tower_mem s (W.sub_mem (hγW y hyW).1 hyW)) (hXW hw.2)`. Establish `: l = (g : E)⁻¹ • ((g : 𝓞 E) • l)`.

Rewrite using `[smulO, map_natCast, smul_smul, inv_mul_cancel₀ hg0, one_smul]`. Rewrite using `[this]`. Conclude with `W.smul_mem _ hgl`. Establish `h1 : π ((g : 𝓞 E) • l) = π (s • (γ y - y))`. Rewrite using `[← hz, map_add, hπX w hw.2, add_zero]`.

Rewrite `h1` using `[smulO, smulO, map_smul, map_smul, map_sub, (hγW y hyW).2, map_natCast, smul_eq_mul, smul_eq_mul]`. Clear the denominators using the available nonvanishing facts. Take the linear combination `h1`. Take `⟨s, hs, hsI⟩` from `exists_common P I hIfg _ hloc`. Use `⟨s, hs, mem_O_of_stable I hI0 hIfg _ ?_⟩` and prove the remaining obligations.

Introduce `c hc`. Conclude with `hsI c hc`. Use `⟨(g : 𝓞 E), hgP, ?_⟩` and prove the remaining obligations. Take `⟨o, ho⟩` from `hμO`. Use `⟨o - 1, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_sub, map_one, ho, map_natCast]`. Clear the denominators using the available nonvanishing facts. Conclude with `eq_one_of_cong μ g hg hnorm hνO`.
-/
theorem eigenOne_gen (Λ : Submodule (𝓞 E) S.V) {g r : ℕ} {T T' : E} {F : LFlag S r T}
    {F' F'' : LFlag S r T'} (β₁ β₂ : S.V ≃ₗ[E] S.V) (hg : 3 ≤ g)
    (hCM : ∀ μ : E, star μ * μ = 1 → ∀ φ : E →+* ℂ, ‖φ μ‖ = 1)
    (hL : Submodule.IsLattice E Λ) (hU : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) (hFC : IsFixedConv Λ g F)
    (hA' : IsAdmissible Λ g F F') (hA'' : IsAdmissible Λ g F F'')
    (hP1 : IsPair Λ F F' F'' β₁ g) (hP2 : IsPair Λ F F' F'' β₂ g)
    (v : S.V) (hv : v ∈ orth S (Xplus F')) (hvX : v ∉ Xsp F') (hvv : S.hT v v ≠ 0)
    (μ : E) (hμ : β₁.symm (β₂ v) - μ • v ∈ Xsp F') : μ = 1 := by
  obtain ⟨ξ', hA'⟩ := hA'
  obtain ⟨ξ'', hA''⟩ := hA''
  set X' := Xsp F' with hX'
  let γ : S.V →ₗ[E] S.V := (β₁.symm : S.V →ₗ[E] S.V) ∘ₗ (β₂ : S.V →ₗ[E] S.V)
  have hγ : ∀ x, γ x = β₁.symm (β₂ x) := fun x => rfl
  have hγX : ∀ x ∈ X', γ x ∈ X' := by
    intro x hx
    rw [hγ]
    apply symm_mem_X hP1.2.1
    rw [← Xflag_r, ← hP2.2.1 r]
    exact Submodule.mem_map_of_mem (by rw [Xflag_r]; exact hx)
  have hγΛ : ∀ x ∈ Λ, γ x ∈ Λ := by
    intro x hx
    rw [hγ]
    apply symm_mem hP1.1
    have h2 := hP2.1.2
    unfold Formalism.HermitianLatticesTheory.gmap at h2
    rw [← h2]
    exact ⟨x, hx, rfl⟩
  have hiso2 : ∀ x y, S.hT (β₂ x) (β₂ y) = S.hT x y := hP2.1.1
  have hiso1 : ∀ x y, S.hT (β₁.symm x) (β₁.symm y) = S.hT x y := by
    intro x y
    have := hP1.1.1 (β₁.symm x) (β₁.symm y)
    simpa using this.symm
  have hγiso : ∀ x y, S.hT (γ x) (γ y) = S.hT x y := by
    intro x y; rw [hγ, hγ, hiso1, hiso2]
  have hXXplus : X' ≤ Xplus F' := le_sup_left
  have hvo : v ∈ orth S X' := by
    rw [mem_orth] at hv ⊢
    exact fun x hx => hv x (hXXplus hx)
  set x₀ := γ v - μ • v with hx₀
  have hx₀X : x₀ ∈ X' := hμ
  have hγv : γ v = μ • v + x₀ := by rw [hx₀]; abel

  have hstar : star μ * μ = 1 := by
    have h1 := hγiso v v
    rw [hγv] at h1
    have e1 : S.hT x₀ v = 0 := (mem_orth S).mp hvo x₀ hx₀X
    have e2 : S.hT v x₀ = 0 := by rw [hT_swap, e1, star_zero]
    have e3 : S.hT x₀ x₀ = 0 := hT_X F' hx₀X hx₀X
    simp only [map_add, LinearMap.add_apply, hT_smul_left, hT_smul_right, e1, e2, e3] at h1
    have h2 : (star μ * μ - 1) * S.hT v v = 0 := by linear_combination h1
    rcases mul_eq_zero.mp h2 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hvv
  have hnorm := hCM μ hstar

  have hqv : (X'.mkQ v) ≠ 0 := by
    rw [Submodule.mkQ_apply, Ne, Submodule.Quotient.mk_eq_zero]; exact hvX
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual E (S.V ⧸ X'), f (X'.mkQ v) ≠ 0 := by
    by_contra h
    push Not at h
    exact hqv ((Module.forall_dual_apply_eq_zero_iff E _).mp h)
  let π : S.V →ₗ[E] E := (f (X'.mkQ v))⁻¹ • (f ∘ₗ X'.mkQ)
  have hπv : π v = 1 := by
    simp only [π, LinearMap.smul_apply, LinearMap.comp_apply, smul_eq_mul]
    exact inv_mul_cancel₀ hf
  have hπX : ∀ x ∈ X', π x = 0 := by
    intro x hx
    simp only [π, LinearMap.smul_apply, LinearMap.comp_apply, smul_eq_mul,
      (Submodule.Quotient.mk_eq_zero X').mpr hx, Submodule.mkQ_apply, map_zero, mul_zero]
  set W : Submodule E S.V := Submodule.span E {v} ⊔ X' with hW
  have hdec : ∀ y ∈ W, y - π y • v ∈ X' := by
    intro y hy
    obtain ⟨a, ha, x, hx, rfl⟩ := Submodule.mem_sup.mp hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ha
    have : π (c • v + x) = c := by rw [map_add, map_smul, hπv, hπX x hx, smul_eq_mul]; ring
    rw [this]; simpa using hx
  have hWeq : ∀ y ∈ W, y = π y • v + (y - π y • v) := fun y _ => by abel
  have hvW : v ∈ W := Submodule.mem_sup_left (Submodule.mem_span_singleton_self v)
  have hXW : X' ≤ W := le_sup_right
  have hγW : ∀ y ∈ W, γ y ∈ W ∧ π (γ y) = μ * π y := by
    intro y hy
    have h1 := hWeq y hy
    have h2 : γ y = (π y * μ) • v + (π y • x₀ + γ (y - π y • v)) := by
      conv_lhs => rw [h1]
      rw [map_add, map_smul, hγv, smul_add, smul_smul]; abel
    constructor
    · rw [h2]
      exact W.add_mem (W.smul_mem _ hvW) (hXW (X'.add_mem (X'.smul_mem _ hx₀X) (hγX _ (hdec y hy))))
    · rw [h2, map_add, map_smul, hπv, map_add, map_smul, hπX _ hx₀X, hπX _ (hγX _ (hdec y hy))]
      simp only [smul_eq_mul]; ring
  have hWo : W ≤ orth S X' := by
    apply sup_le
    · rw [Submodule.span_le]; rintro _ rfl; exact hvo
    · intro x hx; rw [mem_orth]; intro y hy; exact hT_X F' hy hx

  let I : Submodule (𝓞 E) E := (Λ ⊓ toO S W).map (π.restrictScalars (𝓞 E))
  have hmemI : ∀ c, c ∈ I ↔ ∃ y ∈ Λ, y ∈ W ∧ π y = c := by
    intro c
    constructor
    · rintro ⟨y, ⟨hyΛ, hyW⟩, rfl⟩; exact ⟨y, hyΛ, hyW, rfl⟩
    · rintro ⟨y, hyΛ, hyW, rfl⟩; exact ⟨y, ⟨hyΛ, hyW⟩, rfl⟩
  have hIfg : I.FG := by
    have hN : IsNoetherian (𝓞 E) Λ := isNoetherian_of_fg_of_noetherian Λ hL.fg
    have h1 := (IsNoetherian.noetherian ((toO S W).comap Λ.subtype)).map Λ.subtype
    rw [Submodule.map_comap_subtype] at h1
    exact h1.map _
  have hI0 : I ≠ ⊥ := by
    obtain ⟨a, ha, haΛ⟩ := exists_smul_mem S Λ hL v
    intro hbot
    have : π (a • v) ∈ I := (hmemI _).mpr ⟨a • v, haΛ, W.smul_of_tower_mem a hvW, rfl⟩
    rw [hbot, Submodule.mem_bot, smulO, map_smul, hπv, smul_eq_mul, mul_one] at this
    exact ha (algebraMap_injO (this.trans (map_zero _).symm))
  have hμO : InO μ := by
    apply mem_O_of_stable I hI0 hIfg μ
    intro c hc
    obtain ⟨y, hyΛ, hyW, rfl⟩ := (hmemI c).mp hc
    exact (hmemI _).mpr ⟨γ y, hγΛ y hyΛ, (hγW y hyW).1, (hγW y hyW).2⟩
  have hg0 : (g : E) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hνO : InO ((μ - 1) / (g : E)) := by
    apply mem_O_of_local
    intro P hPm
    by_cases hgP : (g : 𝓞 E) ∈ P
    · let P' : HeightOneSpectrum (𝓞 E) :=
        ⟨P, hPm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hPm (RingOfIntegers.not_isField E)⟩
      have hloc : ∀ c ∈ I, ∃ s : 𝓞 E, s ∉ P ∧
          algebraMap (𝓞 E) E s * ((μ - 1) / (g : E)) * c ∈ I := by
        intro c hc
        obtain ⟨y, hyΛ, hyW, rfl⟩ := (hmemI c).mp hc
        obtain ⟨s, hs, hsm⟩ := cong β₁ β₂ hU hFC hA' hA'' hP1 hP2 P' hgP y hyΛ (hWo hyW)
        obtain ⟨z₁, hz₁, w, hw, hz⟩ := Submodule.mem_sup.mp hsm
        obtain ⟨l, hl, rfl⟩ := mem_gΛ (Λ := Λ) g hz₁
        rw [← hγ y] at hz
        refine ⟨s, hs, (hmemI _).mpr ⟨l, hl, ?_, ?_⟩⟩
        · have hgl : (g : 𝓞 E) • l ∈ W := by
            have : (g : 𝓞 E) • l = s • (γ y - y) - w := by rw [← hz]; abel
            rw [this]
            exact W.sub_mem (W.smul_of_tower_mem s (W.sub_mem (hγW y hyW).1 hyW)) (hXW hw.2)
          have : l = (g : E)⁻¹ • ((g : 𝓞 E) • l) := by
            rw [smulO, map_natCast, smul_smul, inv_mul_cancel₀ hg0, one_smul]
          rw [this]; exact W.smul_mem _ hgl
        · have h1 : π ((g : 𝓞 E) • l) = π (s • (γ y - y)) := by
            rw [← hz, map_add, hπX w hw.2, add_zero]
          rw [smulO, smulO, map_smul, map_smul, map_sub, (hγW y hyW).2, map_natCast,
            smul_eq_mul, smul_eq_mul] at h1
          field_simp
          linear_combination h1
      obtain ⟨s, hs, hsI⟩ := exists_common P I hIfg _ hloc
      refine ⟨s, hs, mem_O_of_stable I hI0 hIfg _ ?_⟩
      intro c hc; exact hsI c hc
    · refine ⟨(g : 𝓞 E), hgP, ?_⟩
      obtain ⟨o, ho⟩ := hμO
      refine ⟨o - 1, ?_⟩
      rw [map_sub, map_one, ho, map_natCast]
      field_simp
  exact eq_one_of_cong μ g hg hnorm hνO

end Gen

section D7

open PI.BetaLUniq

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Establish `h0` using `(D.host.g_prime 0).two_le`. Establish `h1` using `(D.host.g_prime 1).two_le`. Use `show 3 ≤ D.host.g 0 * D.host.g 1`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem gS_ge_three (D : D7) : 3 ≤ gS D := by
  have h0 := (D.host.g_prime 0).two_le
  have h1 := (D.host.g_prime 1).two_le
  show 3 ≤ D.host.g 0 * D.host.g 1
  nlinarith

/- English proof (translation)
Introduce `D u u' Λ F F' F'' β₁ β₂ hF hT' hT'' _ _ hP1 hP2 _ _ v hv hvX _ μ hμ`. Establish `hvv : (hS D).hT v v ≠ 0` using `fun h => hvX (hW D u' F' v hv h)`. Conclude with `eigenOne_gen Λ β₁ β₂ (gS_ge_three D) (fun μ h φ => cm_norm_eq_one D μ h φ) hF.1 hF.2.1 hF.2.2.2 hT'.2.1 hT''.2.1 hP1 hP2 v hv hvX hvv μ hμ`.
-/
theorem eigenvalue_one_of_anisotropic (hW : WAniso) : EigenvalueLastLineOne := by
  intro D u u' Λ F F' F'' β₁ β₂ hF hT' hT'' _ _ hP1 hP2 _ _ v hv hvX _ μ hμ
  have hvv : (hS D).hT v v ≠ 0 := fun h => hvX (hW D u' F' v hv h)
  exact eigenOne_gen Λ β₁ β₂ (gS_ge_three D) (fun μ h φ => cm_norm_eq_one D μ h φ) hF.1 hF.2.1
    hF.2.2.2 hT'.2.1 hT''.2.1 hP1 hP2 v hv hvX hvv μ hμ

/- English proof (translation)
The claim follows from `eigenvalue_one_of_anisotropic weight_space_anisotropic`.
-/
theorem eigenvalue_last_line_eq_one : EigenvalueLastLineOne := eigenvalue_one_of_anisotropic weight_space_anisotropic

end D7

end PI.UnitaryGroupMassFormula.BetaLUniq
