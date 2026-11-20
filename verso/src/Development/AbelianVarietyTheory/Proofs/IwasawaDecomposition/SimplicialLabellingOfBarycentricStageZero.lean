import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBaryStageStart

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan.BaryFin

variable {X : Type} [AddCommGroup X]

/- English proof (translation)
The claim follows from `LinearMap.ext₂ fun a b => by simp`.
-/
theorem toReal_zero' : toReal (0 : LinearMap.BilinForm ℤ X) = 0 := LinearMap.ext₂ fun a b => by simp

/- English proof (translation)
Unfold `genRank at h`. Use `haveI : Module.Finite ℤ (Submodule.span ℤ (Set.range γ)) := Module.Finite.span_of_finite ℤ (Set.finite_range γ)`. Take `⟨a, ha, e⟩` from `Module.finrank_eq_zero_iff.1 h ⟨γ i, Submodule.subset_span ⟨i, rfl⟩⟩`. Establish `e' : a • γ i = 0` using `congrArg Subtype.val e`. Use `LinearMap.ext₂ fun y z => ?_` and prove the remaining obligations.

Use `LinearMap.congr_fun₂ e' y z` as an intermediate fact. Simplify using `only [LinearMap.smul_apply, smul_eq_mul, LinearMap.zero_apply] at this ⊢`. Conclude with `(mul_eq_zero.1 this).resolve_left ha`.
-/
theorem eq_zero_of_genRank_eq_zero {m : ℕ} (γ : Fin m → LinearMap.BilinForm ℤ X) (h : genRank γ = 0) (i : Fin m) :
    γ i = 0 := by
  unfold genRank at h
  haveI : Module.Finite ℤ (Submodule.span ℤ (Set.range γ)) := Module.Finite.span_of_finite ℤ (Set.finite_range γ)
  obtain ⟨a, ha, e⟩ := Module.finrank_eq_zero_iff.1 h ⟨γ i, Submodule.subset_span ⟨i, rfl⟩⟩
  have e' : a • γ i = 0 := congrArg Subtype.val e
  refine LinearMap.ext₂ fun y z => ?_
  have := LinearMap.congr_fun₂ e' y z
  simp only [LinearMap.smul_apply, smul_eq_mul, LinearMap.zero_apply] at this ⊢
  exact (mul_eq_zero.1 this).resolve_left ha

/- English proof (translation)
Establish `hk' : (0 : ℝ) < k` using `by exact_mod_cast hk`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, hc, h⟩`. Use `⟨fun i => c i / k, fun i => div_nonneg (hc i) hk'.le, LinearMap.ext₂ fun a b => ?_⟩` and prove the remaining obligations. Use `LinearMap.congr_fun₂ h a b` as an intermediate fact.

Simplify using `only [toReal_apply, LinearMap.smul_apply, LinearMap.sum_apply, smul_eq_mul] at this ⊢`. Move the coercions through the operations in `at this`. Repeatedly rewrite using `[div_mul_eq_mul_div, ← Finset.sum_div, ← this]`. Clear the denominators using the available nonvanishing facts. Introduce and unpack `⟨c, hc, h⟩`.

Use `⟨fun i => k * c i, fun i => mul_nonneg hk'.le (hc i), LinearMap.ext₂ fun a b => ?_⟩` and prove the remaining obligations. Use `LinearMap.congr_fun₂ h a b` as an intermediate fact. Simplify using `only [toReal_apply, LinearMap.smul_apply, LinearMap.sum_apply, smul_eq_mul] at this ⊢`. Use `push_cast`. Rewrite using `[this, Finset.mul_sum]`.

Conclude with `Finset.sum_congr rfl fun i _ => by ring`.
-/
theorem inRCone_smul_iff {m : ℕ} (γ : Fin m → LinearMap.BilinForm ℤ X) (β : LinearMap.BilinForm ℤ X) {k : ℕ}
    (hk : 0 < k) : InRCone γ ((k : ℤ) • β) ↔ InRCone γ β := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  constructor
  · rintro ⟨c, hc, h⟩
    refine ⟨fun i => c i / k, fun i => div_nonneg (hc i) hk'.le, LinearMap.ext₂ fun a b => ?_⟩
    have := LinearMap.congr_fun₂ h a b
    simp only [toReal_apply, LinearMap.smul_apply, LinearMap.sum_apply, smul_eq_mul] at this ⊢
    push_cast at this
    simp_rw [div_mul_eq_mul_div, ← Finset.sum_div, ← this]
    field_simp
  · rintro ⟨c, hc, h⟩
    refine ⟨fun i => k * c i, fun i => mul_nonneg hk'.le (hc i), LinearMap.ext₂ fun a b => ?_⟩
    have := LinearMap.congr_fun₂ h a b
    simp only [toReal_apply, LinearMap.smul_apply, LinearMap.sum_apply, smul_eq_mul] at this ⊢
    push_cast
    rw [this, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

variable {O : Type} [CommRing O] {bar : O → O} {q : ℕ}

/- English proof (translation)
Establish `key` using `hlab X hX (v k) (hv.mem k) (hv.nonneg k)`. Rewrite `hk` using `[key]`. Establish `h0` using `Nat.cast_nonpos.1 hk`. Establish `hS : ({n : ℕ | ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ ∧ InRCone γ (v k) ∧ genRank γ = n}).Nonempty` using `⟨_, b, v, hv, inRCone_self v k, rfl⟩`. Take `⟨m, γ, -, ⟨c, -, hc⟩, hr⟩` from `Nat.sInf_mem hS`.

Rewrite `hr` using `[h0]`. Establish `hz` using `eq_zero_of_genRank_eq_zero γ hr`. Use `LinearMap.ext₂ fun y z => ?_` and prove the remaining obligations. Use `LinearMap.congr_fun₂ hc y z` as an intermediate fact. Simplify using `[hz, LinearMap.sum_apply] at this`.

Simplify using `using this`.
-/
theorem eq_zero_of_label_nonpos {ψ lab : InvFun O} (hlab : IsCarrierDim bar q ψ lab) {X : Type} [AddCommGroup X]
    [Module O X] [Module.Finite O X] [Module.Projective O X] (hX : Module.finrank O X ≤ q) {b : ℕ}
    {v : Fin b → LinearMap.BilinForm ℤ X} (hv : IsCell bar ψ v) (k : Fin b) (hk : lab.evalZ (v k) ≤ 0) : v k = 0 := by
  have key := hlab X hX (v k) (hv.mem k) (hv.nonneg k)
  rw [key] at hk
  have h0 := Nat.cast_nonpos.1 hk
  have hS : ({n : ℕ | ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ ∧ InRCone γ (v k) ∧
      genRank γ = n}).Nonempty := ⟨_, b, v, hv, inRCone_self v k, rfl⟩
  obtain ⟨m, γ, -, ⟨c, -, hc⟩, hr⟩ := Nat.sInf_mem hS
  rw [h0] at hr
  have hz := eq_zero_of_genRank_eq_zero γ hr
  refine LinearMap.ext₂ fun y z => ?_
  have := LinearMap.congr_fun₂ hc y z
  simp [hz, LinearMap.sum_apply] at this
  simpa using this

variable (O bar q) in

/- English proof (translation)
Use `⟨fun X _ _ _ _ hX β hβ hp k hk => ?_, fun X _ _ _ _ hX m γ hγ => ?_⟩` and prove the remaining obligations. Establish `hp' : ∀ y, 0 ≤ ((k : ℤ) • β) y y` using `fun y => by`. Simplify using `only [LinearMap.smul_apply, smul_eq_mul]`. Conclude with `mul_nonneg (by positivity) (hp y)`. Rewrite using `[hlab X hX _ (Submodule.smul_mem _ _ hβ) hp', hlab X hX β hβ hp]`.

Simplify using `only [inRCone_smul_iff _ _ hk]`. Take `⟨b, a, v, u, hc, hv, hin, hinj, -, hle, -, hli⟩` from `hφ.2.2 X hX m γ hγ`. Establish `hv0 : ∀ k, v k = 0` using `fun k => eq_zero_of_label_nonpos hlab hX hv k (by simpa using hle (v k) (hv.mem k) (hv.nonneg k) (inRCone_self v k))`. Establish `hu : IsCell bar φ u`. Use `⟨fun j => by simpa using hc.mem (Fin.natAdd b j), fun j => by simpa using hc.nonneg (Fin.natAdd b j), ?_, ?_⟩` and prove the remaining obligations.

Use `linearOn_comp hc.linear (⟨Fin.natAdd b, fun x y h => by simpa using h⟩ : Fin a ↪ Fin (b + a))` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Conclude with `(Fin.append_right v u i).symm`. Take `⟨N, ℓ, hN, h1, h2, h3⟩` from `hc.strict`.

Use `⟨N, ℓ, hN, fun i => by simpa using h1 (Fin.natAdd b i), h2, fun β hβ hp he => ?_⟩` and prove the remaining obligations. Take `⟨k, c, hk, hc'⟩` from `h3 β hβ hp he`. Use `⟨k, fun i => c (Fin.natAdd b i), hk, ?_⟩` and prove the remaining obligations. Rewrite using `[hc', Fin.sum_univ_add]`. Simplify using `[hv0]`.

Use `⟨a, u, hu, Fintype.linearIndependent_iff.2 fun c hc0 i => congrFun (hli 0 c (by rw [hc0]; simp)) i, hinj, fun j => ?_⟩` and prove the remaining obligations. Take `⟨c, hc0, h⟩` from `hin j`. Use `⟨fun i => c (Fin.natAdd b i), fun i => hc0 _, ?_⟩` and prove the remaining obligations. Rewrite using `[h, Fin.sum_univ_add]`. Simplify using `[hv0, toReal_zero']`.
-/
theorem simpLab_of_isBaryStage_zero (ψ lab φ : InvFun O) (hlab : IsCarrierDim bar q ψ lab)
    (hφ : IsBaryStage bar q ψ lab φ 0) : SimpLab bar q φ lab := by
  refine ⟨fun X _ _ _ _ hX β hβ hp k hk => ?_, fun X _ _ _ _ hX m γ hγ => ?_⟩
  · have hp' : ∀ y, 0 ≤ ((k : ℤ) • β) y y := fun y => by
      simp only [LinearMap.smul_apply, smul_eq_mul]
      exact mul_nonneg (by positivity) (hp y)
    rw [hlab X hX _ (Submodule.smul_mem _ _ hβ) hp', hlab X hX β hβ hp]
    simp only [inRCone_smul_iff _ _ hk]
  · obtain ⟨b, a, v, u, hc, hv, hin, hinj, -, hle, -, hli⟩ := hφ.2.2 X hX m γ hγ
    have hv0 : ∀ k, v k = 0 := fun k => eq_zero_of_label_nonpos hlab hX hv k
      (by simpa using hle (v k) (hv.mem k) (hv.nonneg k) (inRCone_self v k))
    have hu : IsCell bar φ u := by
      refine ⟨fun j => by simpa using hc.mem (Fin.natAdd b j), fun j => by simpa using hc.nonneg (Fin.natAdd b j),
        ?_, ?_⟩
      · have := linearOn_comp hc.linear (⟨Fin.natAdd b, fun x y h => by simpa using h⟩ : Fin a ↪ Fin (b + a))
        convert this using 1
        funext i
        exact (Fin.append_right v u i).symm
      · obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hc.strict
        refine ⟨N, ℓ, hN, fun i => by simpa using h1 (Fin.natAdd b i), h2, fun β hβ hp he => ?_⟩
        obtain ⟨k, c, hk, hc'⟩ := h3 β hβ hp he
        refine ⟨k, fun i => c (Fin.natAdd b i), hk, ?_⟩
        rw [hc', Fin.sum_univ_add]
        simp [hv0]
    refine ⟨a, u, hu, Fintype.linearIndependent_iff.2 fun c hc0 i => congrFun (hli 0 c (by rw [hc0]; simp)) i,
      hinj, fun j => ?_⟩
    obtain ⟨c, hc0, h⟩ := hin j
    refine ⟨fun i => c (Fin.natAdd b i), fun i => hc0 _, ?_⟩
    rw [h, Fin.sum_univ_add]
    simp [hv0, toReal_zero']

/- English proof (translation)
Introduce `O _ bar q` and use `simpLab_of_isBaryStage_zero O bar q`.
-/
example : ∀ (O : Type) [CommRing O] (bar : O → O) (q : ℕ) (ψ lab φ : InvFun O), IsCarrierDim bar q ψ lab →
    IsBaryStage bar q ψ lab φ 0 → SimpLab bar q φ lab := fun O _ bar q => simpLab_of_isBaryStage_zero O bar q

end GlobalTheory.PolFan.BaryFin
