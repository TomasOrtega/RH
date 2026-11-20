import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfIsOrbFormConst
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullAddInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCellQuotientByRadicalOfMemCone
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPrimitiveBalancedFormPrimitiveAmongIntForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvalPullSemilinearOfIsTwInv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingOfIntegersAutCommHostConjugationStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntBilinFormDescendAlongSurjectiveStatement

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.OrbMark

namespace GlobalTheory.PolFan.OrbMark

/- English proof (translation)
Introduce `E _ _ _ H X₀ _ _ _ m₀ δ₀ hm hpos hli hprim v t ht hv X _ _ _ β τ f hτ hf hsm hβ`. Generalize the expression as in `hK : (CarDim.orad v : Submodule (𝓞 E) X₀) = K at *`. Establish `hvan : ∀ i, 0 < t i → ∀ x ∈ K, ∀ y, δ₀ i x y = 0`. Introduce `i hi x hx y`. Establish `hxx : v x x = 0` using `by rw [← hK] at hx; simpa using (CarDim.mem_orad.1 hx) 1 x`.

Establish `hsum` using `LinearMap.congr_fun₂ hv x x`. Simplify using `only [toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hxx, Int.cast_zero] at hsum`. Establish `hall` using `(Finset.sum_eq_zero_iff_of_nonneg fun j _ => mul_nonneg (ht j) (Int.cast_nonneg (hpos j x))).1 hsum.symm i (Finset.mem_univ _)`. Establish `h0 : δ₀ i x x = 0`. Break down `mul_eq_zero.1 hall with h | h` into its components or cases.

Conclude with `absurd h hi.ne'`. Conclude with `h` after adjusting the coercions. Conclude with `ConeSub.eq_zero_of_self_eq_zero (δ₀ i) (hm i).1 (hpos i) h0 y`. Establish `hex : ∀ i, ∃ u : LinearMap.BilinForm ℤ (X₀ ⧸ K), 0 < t i → pull K.mkQ u = δ₀ i`. Introduce `i`.

Distinguish the cases in `hi : 0 < t i`. Take `⟨u, hu⟩` from `CarDim.exists_pull_mkQ_eq_of_vanish K (δ₀ i) (hvan i hi) (fun x y hy => by rw [(hm i).1]; exact hvan i hi y hy x)`. Conclude with `⟨u, fun _ => hu⟩`. Conclude with `⟨0, fun h => absurd h hi⟩`. Use `choose u hu using hex`.

Establish `hU : ∀ i, 0 < t i → ∀ y₀ z₀ : X₀, u i (Submodule.Quotient.mk y₀) (Submodule.Quotient.mk z₀) = δ₀ i y₀ z₀` using `fun i hi y₀ z₀ => LinearMap.congr_fun₂ (hu i hi) y₀ z₀`. Establish `hq : ∀ z : X₀ ⧸ K, ∃ z₀ : X₀, Submodule.Quotient.mk z₀ = z` using `Submodule.Quotient.mk_surjective K`. Set `P : LinearMap.BilinForm ℤ (X₀ ⧸ K) →ₗ[ℤ] LinearMap.BilinForm ℤ X₀` to `{ toFun := pull K.mkQ, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }`. Use `⟨u, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `LinearMap.ext₂ fun x y => ?_` and prove the remaining obligations.

Take `⟨x₀, hx₀⟩` from `hq (f x)`. Take `⟨y₀, hy₀⟩` from `hq (f y)`. Establish `h1` using `LinearMap.congr_fun₂ hv x₀ y₀`. Simplify using `only [toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, pullAdd_apply] at h1 ⊢`. Rewrite using `[hβ x y x₀ y₀ hx₀ hy₀, h1]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Break down `(ht i).lt_or_eq with hi | hi` into its components or cases. Rewrite using `[← hx₀, ← hy₀, hU i hi]`. Rewrite using `[← hi, zero_mul, zero_mul]`. Establish `hδ : LinearIndependent ℤ (fun i : {i // 0 < t i} => δ₀ i)` using `hli.comp _ Subtype.val_injective`.

Establish `hu' : LinearIndependent ℤ (fun i : {i // 0 < t i} => u i)`. Use `LinearIndependent.of_comp P ?_` and prove the remaining obligations. Use `hδ using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Conclude with `hu i i.2`.

Conclude with `hu'.map' (pullAddLin f) (LinearMap.ker_eq_bot.2 (pullAdd_injective hf))`. Introduce `i hi`. Use `⟨hu i hi, ⟨fun y z => ?_, fun a y z => ?_⟩, fun y => ?_, fun k β' hk => ?_, fun lab hlab => ?_⟩` and prove the remaining obligations. Take `⟨y₀, hy₀⟩` from `hq (f y)`. Take `⟨z₀, hz₀⟩` from `hq (f z)`.

Simplify using `only [pullAdd_apply, ← hy₀, ← hz₀, hU i hi]`. Conclude with `(hm i).1 y₀ z₀`. Take `⟨y₀, hy₀⟩` from `hq (f y)`. Take `⟨z₀, hz₀⟩` from `hq (f z)`. Simplify using `only [pullAdd_apply, hsm, ← hy₀, ← hz₀, ← Submodule.Quotient.mk_smul, hU i hi]`.

Rewrite using `[(hm i).2, GlobalTheory.T.ringOfIntegers_aut_comm_hostConjugation E H τ a]`. Take `⟨y₀, hy₀⟩` from `hq (f y)`. Simplify using `only [pullAdd_apply, ← hy₀, hU i hi]`. Conclude with `hpos i y₀`. Choose the witnesses or unpack the hypotheses as in `⟨ζ, hζ⟩ : ∃ ζ : LinearMap.BilinForm ℤ (X₀ ⧸ K), (k : ℤ) • ζ = u i := by`.

Break down `Nat.eq_zero_or_pos k with rfl | hk0` into its components or cases. Use `⟨0, ?_⟩` and prove the remaining obligations. Establish `: pullAdd f (u i) = pullAdd f 0`. Rewrite using `[← hk]`. Use `ext`.

Simplify using the standard rewrite rules. Rewrite using `[pullAdd_injective hf this]`. Simplify using the standard rewrite rules. Establish `hk0' : (k : ℤ) ≠ 0` using `by exact_mod_cast hk0.ne'`. Establish `hval : ∀ x y, (k : ℤ) * β' x y = u i (f x) (f y)` using `fun x y => by`.

Rewrite using `[← pullAdd_apply, ← hk]`. Simplify using the standard rewrite rules. Take `⟨ζ, hζ⟩` from `GlobalTheory.T.exists_intBilinForm_descend_along_surjective f hf β' (fun x hx y => by`. Use `hval x y` as an intermediate fact. Rewrite `this` using `[hx, map_zero, LinearMap.zero_apply]`.

Conclude with `(mul_eq_zero.1 this).resolve_left hk0')`. Use the proof step `(fun x hx y => by`. Use `hval y x` as an intermediate fact. Rewrite `this` using `[hx, map_zero]`. Conclude with `(mul_eq_zero.1 this).resolve_left hk0')`.

Use `⟨ζ, LinearMap.ext₂ fun a b => ?_⟩` and prove the remaining obligations. Take `⟨x, rfl⟩` from `hf a`. Take `⟨y, rfl⟩` from `hf b`. Simplify using `[hζ, hval]`. Use `isPrim_eq_one_of_smul_eq H.bar (δ₀ i) (hm i) (hprim i) k (pull K.mkQ ζ) ?_` and prove the remaining obligations.

Rewrite using `[← hu i hi, ← hζ]`. Use extensionality with `a b`. Simplify using the standard rewrite rules. Establish `h1` using `eval_pull_semilinear_of_isTwInv E H lab hlab τ hτ f hf hsm (fun a b => (u i a b : ℝ))`. Rewrite using `[← hu i hi, evalZ_pull lab K.mkQ_surjective]`.

Conclude with `h1`.
-/
theorem exists_desc_rays_pullAdd : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) {X₀ : Type} [AddCommGroup X₀] [Module (𝓞 E) X₀]
  [Module.Finite (𝓞 E) X₀] {m₀ : ℕ} (δ₀ : Fin m₀ → LinearMap.BilinForm ℤ X₀) (hm : ∀ i, δ₀ i ∈ balForms H.bar X₀),
  (∀ i y, 0 ≤ δ₀ i y y) → LinearIndependent ℤ δ₀ → (∀ i, IsPrim H.bar (⟨δ₀ i, hm i⟩ : balForms H.bar X₀)) →
  ∀ (v : LinearMap.BilinForm ℤ X₀) (t : Fin m₀ → ℝ), (∀ i, 0 ≤ t i) → toReal v = ∑ i, t i • toReal (δ₀ i) →
  ∀ {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (β : LinearMap.BilinForm ℤ X) (τ : 𝓞 E ≃+* 𝓞 E)
    (f : X →+ X₀ ⧸ (CarDim.orad v : Submodule (𝓞 E) X₀)), τ H.w0 = H.w0 → Function.Surjective f →
    (∀ (a : 𝓞 E) (x : X), f (a • x) = τ a • f x) →
    (∀ (x y : X) (x₀ y₀ : X₀), Submodule.Quotient.mk x₀ = f x → Submodule.Quotient.mk y₀ = f y → β x y = v x₀ y₀) →
  ∃ u : Fin m₀ → LinearMap.BilinForm ℤ (X₀ ⧸ (CarDim.orad v : Submodule (𝓞 E) X₀)),
    toReal β = ∑ i, t i • toReal (pullAdd f (u i)) ∧
    LinearIndependent ℤ (fun i : {i // 0 < t i} => pullAdd f (u i)) ∧
    ∀ i, 0 < t i → pull (CarDim.orad v : Submodule (𝓞 E) X₀).mkQ (u i) = δ₀ i ∧ pullAdd f (u i) ∈ balForms H.bar X ∧
      (∀ y, 0 ≤ pullAdd f (u i) y y) ∧ (∀ (k : ℕ) (β' : LinearMap.BilinForm ℤ X), (k : ℤ) • β' = pullAdd f (u i) → k = 1) ∧
      ∀ lab : InvFun (𝓞 E), IsTwInv H lab → lab.evalZ (pullAdd f (u i)) = lab.evalZ (δ₀ i) := by
  intro E _ _ _ H X₀ _ _ _ m₀ δ₀ hm hpos hli hprim v t ht hv X _ _ _ β τ f hτ hf hsm hβ
  classical
  generalize hK : (CarDim.orad v : Submodule (𝓞 E) X₀) = K at *
  have hvan : ∀ i, 0 < t i → ∀ x ∈ K, ∀ y, δ₀ i x y = 0 := by
    intro i hi x hx y
    have hxx : v x x = 0 := by rw [← hK] at hx; simpa using (CarDim.mem_orad.1 hx) 1 x
    have hsum := LinearMap.congr_fun₂ hv x x
    simp only [toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hxx, Int.cast_zero] at hsum
    have hall := (Finset.sum_eq_zero_iff_of_nonneg fun j _ =>
      mul_nonneg (ht j) (Int.cast_nonneg (hpos j x))).1 hsum.symm i (Finset.mem_univ _)
    have h0 : δ₀ i x x = 0 := by
      rcases mul_eq_zero.1 hall with h | h
      · exact absurd h hi.ne'
      · exact_mod_cast h
    exact ConeSub.eq_zero_of_self_eq_zero (δ₀ i) (hm i).1 (hpos i) h0 y
  have hex : ∀ i, ∃ u : LinearMap.BilinForm ℤ (X₀ ⧸ K), 0 < t i → pull K.mkQ u = δ₀ i := by
    intro i
    by_cases hi : 0 < t i
    · obtain ⟨u, hu⟩ := CarDim.exists_pull_mkQ_eq_of_vanish K (δ₀ i) (hvan i hi)
        (fun x y hy => by rw [(hm i).1]; exact hvan i hi y hy x)
      exact ⟨u, fun _ => hu⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose u hu using hex
  have hU : ∀ i, 0 < t i → ∀ y₀ z₀ : X₀, u i (Submodule.Quotient.mk y₀) (Submodule.Quotient.mk z₀) = δ₀ i y₀ z₀ :=
    fun i hi y₀ z₀ => LinearMap.congr_fun₂ (hu i hi) y₀ z₀
  have hq : ∀ z : X₀ ⧸ K, ∃ z₀ : X₀, Submodule.Quotient.mk z₀ = z := Submodule.Quotient.mk_surjective K
  let P : LinearMap.BilinForm ℤ (X₀ ⧸ K) →ₗ[ℤ] LinearMap.BilinForm ℤ X₀ :=
    { toFun := pull K.mkQ, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  refine ⟨u, ?_, ?_, ?_⟩
  · refine LinearMap.ext₂ fun x y => ?_
    obtain ⟨x₀, hx₀⟩ := hq (f x)
    obtain ⟨y₀, hy₀⟩ := hq (f y)
    have h1 := LinearMap.congr_fun₂ hv x₀ y₀
    simp only [toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, pullAdd_apply] at h1 ⊢
    rw [hβ x y x₀ y₀ hx₀ hy₀, h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases (ht i).lt_or_eq with hi | hi
    · rw [← hx₀, ← hy₀, hU i hi]
    · rw [← hi, zero_mul, zero_mul]
  · have hδ : LinearIndependent ℤ (fun i : {i // 0 < t i} => δ₀ i) := hli.comp _ Subtype.val_injective
    have hu' : LinearIndependent ℤ (fun i : {i // 0 < t i} => u i) := by
      refine LinearIndependent.of_comp P ?_
      convert hδ using 1
      funext i
      exact hu i i.2
    exact hu'.map' (pullAddLin f) (LinearMap.ker_eq_bot.2 (pullAdd_injective hf))
  · intro i hi
    refine ⟨hu i hi, ⟨fun y z => ?_, fun a y z => ?_⟩, fun y => ?_, fun k β' hk => ?_, fun lab hlab => ?_⟩
    · obtain ⟨y₀, hy₀⟩ := hq (f y)
      obtain ⟨z₀, hz₀⟩ := hq (f z)
      simp only [pullAdd_apply, ← hy₀, ← hz₀, hU i hi]
      exact (hm i).1 y₀ z₀
    · obtain ⟨y₀, hy₀⟩ := hq (f y)
      obtain ⟨z₀, hz₀⟩ := hq (f z)
      simp only [pullAdd_apply, hsm, ← hy₀, ← hz₀, ← Submodule.Quotient.mk_smul, hU i hi]
      rw [(hm i).2, GlobalTheory.T.ringOfIntegers_aut_comm_hostConjugation E H τ a]
    · obtain ⟨y₀, hy₀⟩ := hq (f y)
      simp only [pullAdd_apply, ← hy₀, hU i hi]
      exact hpos i y₀
    · obtain ⟨ζ, hζ⟩ : ∃ ζ : LinearMap.BilinForm ℤ (X₀ ⧸ K), (k : ℤ) • ζ = u i := by
        rcases Nat.eq_zero_or_pos k with rfl | hk0
        · refine ⟨0, ?_⟩
          have : pullAdd f (u i) = pullAdd f 0 := by
            rw [← hk]; ext; simp
          rw [pullAdd_injective hf this]; simp
        · have hk0' : (k : ℤ) ≠ 0 := by exact_mod_cast hk0.ne'
          have hval : ∀ x y, (k : ℤ) * β' x y = u i (f x) (f y) := fun x y => by
            rw [← pullAdd_apply, ← hk]; simp
          obtain ⟨ζ, hζ⟩ := GlobalTheory.T.exists_intBilinForm_descend_along_surjective f hf β'
            (fun x hx y => by
              have := hval x y
              rw [hx, map_zero, LinearMap.zero_apply] at this
              exact (mul_eq_zero.1 this).resolve_left hk0')
            (fun x hx y => by
              have := hval y x
              rw [hx, map_zero] at this
              exact (mul_eq_zero.1 this).resolve_left hk0')
          refine ⟨ζ, LinearMap.ext₂ fun a b => ?_⟩
          obtain ⟨x, rfl⟩ := hf a
          obtain ⟨y, rfl⟩ := hf b
          simp [hζ, hval]
      refine isPrim_eq_one_of_smul_eq H.bar (δ₀ i) (hm i) (hprim i) k (pull K.mkQ ζ) ?_
      rw [← hu i hi, ← hζ]
      ext a b
      simp
    · have h1 := eval_pull_semilinear_of_isTwInv E H lab hlab τ hτ f hf hsm (fun a b => (u i a b : ℝ))
      rw [← hu i hi, evalZ_pull lab K.mkQ_surjective]
      exact h1

end GlobalTheory.PolFan.OrbMark
