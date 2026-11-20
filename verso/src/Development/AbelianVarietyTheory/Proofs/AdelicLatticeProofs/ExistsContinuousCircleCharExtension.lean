import Mathlib

open scoped Topology

namespace GlobalTheory

/- English proof (translation)
Use `letI : DivisibleBy (Additive Circle) ℕ := divisibleByOfSMulRightSurj _ _ fun {n} hn u => by`. Take `⟨t, ht⟩` from `Circle.exp_surjective (Additive.toMul u)`. Use `⟨Additive.ofMul (Circle.exp (t / n)), ?_⟩` and prove the remaining obligations. Apply `Additive.toMul.injective` to reduce the goal to its premises. Establish `hn' : (n : ℝ) ≠ 0` using `by exact_mod_cast hn`.

Simplify using `only [toMul_nsmul, toMul_ofMul]`. Rewrite using `[← ht, ← Circle.exp_nsmul, nsmul_eq_mul, mul_div_cancel₀ _ hn']`. Use `letI : DivisibleBy (Additive Circle) ℤ := AddGroup.divisibleByIntOfDivisibleByNat _`. Take `⟨ρ, hρ⟩` from `(Module.Baer.of_divisible (Additive Circle)).extension_property_addMonoidHom (MonoidHom.toAdditive i) hi (MonoidHom.toAdditive ψ)`. Use `⟨MonoidHom.toAdditive.symm ρ, fun a => ?_⟩` and prove the remaining obligations.

Conclude with `congrArg Additive.toMul (DFunLike.congr_fun hρ (Additive.ofMul a))`.
-/
theorem circle_hom_extend_of_injective {A B : Type} [CommGroup A] [CommGroup B] (i : A →* B)
    (hi : Function.Injective i) (ψ : A →* Circle) : ∃ χ : B →* Circle, ∀ a, χ (i a) = ψ a := by
  letI : DivisibleBy (Additive Circle) ℕ := divisibleByOfSMulRightSurj _ _ fun {n} hn u => by
    obtain ⟨t, ht⟩ := Circle.exp_surjective (Additive.toMul u)
    refine ⟨Additive.ofMul (Circle.exp (t / n)), ?_⟩
    apply Additive.toMul.injective
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    simp only [toMul_nsmul, toMul_ofMul]
    rw [← ht, ← Circle.exp_nsmul, nsmul_eq_mul, mul_div_cancel₀ _ hn']
  letI : DivisibleBy (Additive Circle) ℤ := AddGroup.divisibleByIntOfDivisibleByNat _
  obtain ⟨ρ, hρ⟩ := (Module.Baer.of_divisible (Additive Circle)).extension_property_addMonoidHom
    (MonoidHom.toAdditive i) hi (MonoidHom.toAdditive ψ)
  refine ⟨MonoidHom.toAdditive.symm ρ, fun a => ?_⟩
  exact congrArg Additive.toMul (DFunLike.congr_fun hρ (Additive.ofMul a))

/- English proof (translation)
Introduce `G _ _ _ H N ψ hH hψ hN`. Set `f : H →* G ⧸ N` to `(QuotientGroup.mk' N).comp H.subtype`. Establish `hker : f.ker ≤ ψ.ker` using `fun x hx => by`. Rewrite `hx`, the goal using `[MonoidHom.mem_ker]`. Conclude with `hN x ((QuotientGroup.eq_one_iff _).1 hx)`.

Take `⟨χ₀, hχ₀⟩` from `circle_hom_extend_of_injective (QuotientGroup.kerLift f) (QuotientGroup.kerLift_injective f) (QuotientGroup.lift f.ker ψ hker)`. Establish `hx : ∀ x : H, (χ₀.comp (QuotientGroup.mk' N)) x = ψ x` using `fun x => hχ₀ (QuotientGroup.mk x)`. Use `⟨χ₀.comp (QuotientGroup.mk' N), ?_, fun x hxN => ?_, hx⟩` and prove the remaining obligations. Use `continuous_of_continuousAt_one _ ?_` and prove the remaining obligations. Establish `hc : ContinuousOn (χ₀.comp (QuotientGroup.mk' N)) (H : Set G)`.

Rewrite using `[continuousOn_iff_continuous_domRestrict]`. Conclude with `hψ.congr fun x => (hx x).symm`. Conclude with `hc.continuousAt (hH.mem_nhds H.one_mem)`. Establish `: QuotientGroup.mk' N x = 1` using `(QuotientGroup.eq_one_iff _).2 hxN`. Rewrite using `[MonoidHom.comp_apply, this, map_one]`.
-/
theorem exists_continuous_circle_char_extension :
    ∀ (G : Type) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] (H N : Subgroup G) (ψ : H →* Circle), IsOpen (H : Set G) → Continuous ψ → (∀ x : H, (x : G) ∈ N → ψ x = 1) → ∃ χ : G →* Circle, Continuous χ ∧ (∀ x ∈ N, χ x = 1) ∧ ∀ x : H, χ x = ψ x := by
  intro G _ _ _ H N ψ hH hψ hN
  let f : H →* G ⧸ N := (QuotientGroup.mk' N).comp H.subtype
  have hker : f.ker ≤ ψ.ker := fun x hx => by
    rw [MonoidHom.mem_ker] at hx ⊢
    exact hN x ((QuotientGroup.eq_one_iff _).1 hx)
  obtain ⟨χ₀, hχ₀⟩ := circle_hom_extend_of_injective (QuotientGroup.kerLift f)
    (QuotientGroup.kerLift_injective f) (QuotientGroup.lift f.ker ψ hker)
  have hx : ∀ x : H, (χ₀.comp (QuotientGroup.mk' N)) x = ψ x := fun x => hχ₀ (QuotientGroup.mk x)
  refine ⟨χ₀.comp (QuotientGroup.mk' N), ?_, fun x hxN => ?_, hx⟩
  · refine continuous_of_continuousAt_one _ ?_
    have hc : ContinuousOn (χ₀.comp (QuotientGroup.mk' N)) (H : Set G) := by
      rw [continuousOn_iff_continuous_domRestrict]
      exact hψ.congr fun x => (hx x).symm
    exact hc.continuousAt (hH.mem_nhds H.one_mem)
  · have : QuotientGroup.mk' N x = 1 := (QuotientGroup.eq_one_iff _).2 hxN
    rw [MonoidHom.comp_apply, this, map_one]

end GlobalTheory
