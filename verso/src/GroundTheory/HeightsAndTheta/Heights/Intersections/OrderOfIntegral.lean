import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsTerLast
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsTerTer
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsTerFurther
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField

noncomputable section

/- English proof (translation)
Establish `hmul : ∀ x : F, ∃ m : ℤ, m ≠ 0 ∧ (m : F) * x ∈ S`. Introduce `x`. Take `⟨c, hc, hc0, hxc⟩` from `hden x`. Establish `hci : IsIntegral ℤ (⟨c, hc⟩ : S)` using `(isIntegral_algHom_iff S.subtype.toIntAlgHom Subtype.val_injective).1 (hint c hc)`. Establish `hne` using `Ideal.comap_ne_bot_of_integral_mem (I := Ideal.span {(⟨c, hc⟩ : S)}) (fun h => hc0 (congrArg Subtype.val h)) (Ideal.mem_span_singleton_self _) hci`.

Take `⟨m, hm, hm0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hne`. Take `⟨d, hd⟩` from `Ideal.mem_span_singleton'.1 (Ideal.mem_comap.1 hm)`. Use `⟨m, hm0, ?_⟩` and prove the remaining obligations. Establish `hmdc : (m : F) = (d : F) * c`. Use `congrArg Subtype.val hd` as an intermediate fact.

Simplify using `using this.symm`. Rewrite using `[hmdc, mul_assoc, mul_comm c x]`. Conclude with `S.mul_mem d.2 hxc`. Set `φ : S →ₗ[ℤ] 𝓞 F` to `{ toFun := fun x => ⟨x, hint x x.2⟩ map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl }`. Establish `hφ : Function.Injective φ` using `fun x y h => Subtype.ext (congrArg (fun z : 𝓞 F => (z : F)) h)`.

Establish `: Module.Finite ℤ S` using `Module.Finite.of_injective φ hφ`. Establish `: Module.IsTorsionFree ℤ S` using `hφ.moduleIsTorsionFree φ (fun r x => φ.map_smul r x)`. Establish `: Module.Free ℤ S` using `Module.free_of_finite_type_torsion_free'`. Use `⟨inferInstance, inferInstance, le_antisymm ?_ ?_⟩` and prove the remaining obligations. Rewrite using `[← RingOfIntegers.rank]`.

Conclude with `LinearMap.finrank_le_finrank_of_injective hφ`. Rewrite using `[← RingOfIntegers.rank]`. Take `⟨n, s, hs⟩` from `Module.Finite.exists_fin (R := ℤ) (M := 𝓞 F)`. Use `choose m hm0 hmS using fun i => hmul (s i : F)`. Establish `hM0 : (∏ i, m i) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun i _ => hm0 i`.

Establish `hMS : ∀ y : 𝓞 F, ((∏ i, m i : ℤ) : F) * y ∈ S`. Introduce `y`. Establish `hy : y ∈ Submodule.span ℤ (Set.range s)` using `hs ▸ Submodule.mem_top`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy`.

Take `⟨i, rfl⟩` from `hy`. Take `⟨q, hq⟩ : m i ∣ ∏ j, m j` from `Finset.dvd_prod_of_mem m (Finset.mem_univ i)`. Rewrite using `[hq, Int.cast_mul, mul_comm (m i : F), mul_assoc]`. Conclude with `S.mul_mem (intCast_mem S q) (hmS i)`. Consider the case `zero => simp`.

Consider the case `add y z _ _ hy hz`. Use `S.add_mem hy hz using 1` and compare the differences between its conclusion and the goal. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Consider the case `smul r y _ hy`.

Use `S.zsmul_mem hy r using 1` and compare the differences between its conclusion and the goal. Simplify using `only [RingOfIntegers.coe_eq_algebraMap, zsmul_eq_mul, map_mul, map_intCast]`. Expand and normalize the polynomial expressions, which then agree. Set `ψ : 𝓞 F →ₗ[ℤ] S` to `{ toFun := fun y => ⟨((∏ i, m i : ℤ) : F) * y, hMS y⟩ map_add' := fun y z => Subtype.ext (by push_cast; ring) map_smul' := fun r y => Subtype.ext (by`. Simplify using `only [RingOfIntegers.coe_eq_algebraMap, zsmul_eq_mul, map_mul, map_intCast, Subring.coe_mul, SubringClass.coe_intCast, RingHom.id_apply]`.

Use the proof step `ring) }`. Establish `hψ : Function.Injective ψ`. Introduce `y z h`. Establish `h' : ((∏ i, m i : ℤ) : F) * y = ((∏ i, m i : ℤ) : F) * z` using `congrArg Subtype.val h`. Conclude with `RingOfIntegers.eq_iff.1 (mul_left_cancel₀ (Int.cast_ne_zero.2 hM0) h')`.

Conclude with `LinearMap.finrank_le_finrank_of_injective hψ`.
-/
theorem RegularityOrder.order_of_integral {F : Type*} [Field F] [NumberField F] (S : Subring F)
    (hint : ∀ x ∈ S, IsIntegral ℤ x) (hden : ∀ x : F, ∃ c ∈ S, c ≠ 0 ∧ x * c ∈ S) :
    Module.Finite ℤ S ∧ Module.Free ℤ S ∧ Module.finrank ℤ S = Module.finrank ℚ F := by

  have hmul : ∀ x : F, ∃ m : ℤ, m ≠ 0 ∧ (m : F) * x ∈ S := by
    intro x
    obtain ⟨c, hc, hc0, hxc⟩ := hden x
    have hci : IsIntegral ℤ (⟨c, hc⟩ : S) :=
      (isIntegral_algHom_iff S.subtype.toIntAlgHom Subtype.val_injective).1 (hint c hc)
    have hne := Ideal.comap_ne_bot_of_integral_mem (I := Ideal.span {(⟨c, hc⟩ : S)})
      (fun h => hc0 (congrArg Subtype.val h)) (Ideal.mem_span_singleton_self _) hci
    obtain ⟨m, hm, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 (Ideal.mem_comap.1 hm)
    refine ⟨m, hm0, ?_⟩
    have hmdc : (m : F) = (d : F) * c := by
      have := congrArg Subtype.val hd
      simpa using this.symm
    rw [hmdc, mul_assoc, mul_comm c x]
    exact S.mul_mem d.2 hxc

  let φ : S →ₗ[ℤ] 𝓞 F :=
    { toFun := fun x => ⟨x, hint x x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hφ : Function.Injective φ := fun x y h =>
    Subtype.ext (congrArg (fun z : 𝓞 F => (z : F)) h)
  have : Module.Finite ℤ S := Module.Finite.of_injective φ hφ
  have : Module.IsTorsionFree ℤ S := hφ.moduleIsTorsionFree φ (fun r x => φ.map_smul r x)
  have : Module.Free ℤ S := Module.free_of_finite_type_torsion_free'
  refine ⟨inferInstance, inferInstance, le_antisymm ?_ ?_⟩
  · rw [← RingOfIntegers.rank]
    exact LinearMap.finrank_le_finrank_of_injective hφ
  · rw [← RingOfIntegers.rank]
    obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := ℤ) (M := 𝓞 F)
    choose m hm0 hmS using fun i => hmul (s i : F)
    have hM0 : (∏ i, m i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hm0 i
    have hMS : ∀ y : 𝓞 F, ((∏ i, m i : ℤ) : F) * y ∈ S := by
      intro y
      have hy : y ∈ Submodule.span ℤ (Set.range s) := hs ▸ Submodule.mem_top
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨i, rfl⟩ := hy
        obtain ⟨q, hq⟩ : m i ∣ ∏ j, m j := Finset.dvd_prod_of_mem m (Finset.mem_univ i)
        rw [hq, Int.cast_mul, mul_comm (m i : F), mul_assoc]
        exact S.mul_mem (intCast_mem S q) (hmS i)
      | zero => simp
      | add y z _ _ hy hz =>
        convert S.add_mem hy hz using 1
        push_cast
        ring
      | smul r y _ hy =>
        convert S.zsmul_mem hy r using 1
        simp only [RingOfIntegers.coe_eq_algebraMap, zsmul_eq_mul, map_mul, map_intCast]
        ring
    let ψ : 𝓞 F →ₗ[ℤ] S :=
      { toFun := fun y => ⟨((∏ i, m i : ℤ) : F) * y, hMS y⟩
        map_add' := fun y z => Subtype.ext (by push_cast; ring)
        map_smul' := fun r y => Subtype.ext (by
          simp only [RingOfIntegers.coe_eq_algebraMap, zsmul_eq_mul, map_mul, map_intCast,
            Subring.coe_mul, SubringClass.coe_intCast, RingHom.id_apply]
          ring) }
    have hψ : Function.Injective ψ := by
      intro y z h
      have h' : ((∏ i, m i : ℤ) : F) * y = ((∏ i, m i : ℤ) : F) * z := congrArg Subtype.val h
      exact RingOfIntegers.eq_iff.1 (mul_left_cancel₀ (Int.cast_ne_zero.2 hM0) h')
    exact LinearMap.finrank_le_finrank_of_injective hψ

/- English proof (translation)
Introduce `K _ ι _ P hP`. Set `f : funField P →ₐ[ℤ] FractionRing (MRing ι ⧸ P)` to `{ (funField P).subtype with commutes' := fun r => by simp }`. Establish `hint₀ : ∀ x ∈ regRing P, IsIntegral ℤ x` using `fun x hx => (isIntegral_algHom_iff f Subtype.val_injective).1 (h₃ K ι P hP ⟨x, hx⟩)`. Take `⟨hF, hN⟩` from `h₁ K ι P hP`. Set `_ : Field (funField P)` to `hF.toField`.

Use `hN` as an intermediate fact. Establish `hint : ∀ x ∈ regRing P, IsIntegral ℤ x` using `hint₀`. Establish `hden : ∀ x : funField P, ∃ c ∈ regRing P, c ≠ 0 ∧ x * c ∈ regRing P`. Introduce `x`. Take `⟨c, hc0, hc⟩` from `h₂ K ι P x hP`.

Conclude with `⟨c, fun W h1 h2 => (hc W h1 h2).1, hc0, fun W h1 h2 => (hc W h1 h2).2⟩`. Take `⟨hfin, hfree, hrank⟩` from `RegularityOrder.order_of_integral (F := funField P) (regRing P) hint hden`. Conclude with `⟨hfree, hfin, fun _ _ => hrank⟩`.
-/
theorem RegularityOrder.proof (h₁ : RegularityFunctionFieldNumber.Statement) (h₂ : RegularityDenominator.Statement)
    (h₃ : RegularityIntegral.Statement) : RegularityOrder.Statement := by
  intro K _ ι _ P hP
  let f : funField P →ₐ[ℤ] FractionRing (MRing ι ⧸ P) :=
    { (funField P).subtype with commutes' := fun r => by simp }
  have hint₀ : ∀ x ∈ regRing P, IsIntegral ℤ x := fun x hx =>
    (isIntegral_algHom_iff f Subtype.val_injective).1 (h₃ K ι P hP ⟨x, hx⟩)
  obtain ⟨hF, hN⟩ := h₁ K ι P hP
  let _ : Field (funField P) := hF.toField
  have := hN
  have hint : ∀ x ∈ regRing P, IsIntegral ℤ x := hint₀
  have hden : ∀ x : funField P, ∃ c ∈ regRing P, c ≠ 0 ∧ x * c ∈ regRing P := by
    intro x
    obtain ⟨c, hc0, hc⟩ := h₂ K ι P x hP
    exact ⟨c, fun W h1 h2 => (hc W h1 h2).1, hc0, fun W h1 h2 => (hc W h1 h2).2⟩
  obtain ⟨hfin, hfree, hrank⟩ := RegularityOrder.order_of_integral (F := funField P) (regRing P) hint hden
  exact ⟨hfree, hfin, fun _ _ => hrank⟩

end

end GroundTheory.Heights₂.Heights.Inter
