import Mathlib
import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.Integral

open IsLocalRing

/- English proof (translation)
Introduce `L B _ _ _ _ N _ _ _ _ _`. Establish `hfin : Module.Finite B N` using `Module.Finite.of_restrictScalars_finite L B N`. Rewrite using `[Module.supportDim_eq_ringKrullDim_quotient_annihilator]`. Set `f : B →ₐ[L] Module.End L N` to `Algebra.lsmul L L N`. Establish `hf : ∀ b : B, b ∈ Module.annihilator B N → f b = 0`.

Introduce `b hb`. Use extensionality with `n`. Conclude with `Module.mem_annihilator.mp hb n`. Set `g : (B ⧸ Module.annihilator B N) →ₐ[L] Module.End L N` to `Ideal.Quotient.liftₐ (Module.annihilator B N) f hf`. Establish `hinj : Function.Injective g`.

Use `(injective_iff_map_eq_zero g).mpr ?_` and prove the remaining obligations. Introduce `q hq`. Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective q`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem]`. Use `Module.mem_annihilator.mpr (fun n => ?_)` and prove the remaining obligations.

Establish `h` using `LinearMap.congr_fun hq n`. Conclude with `h`. Use `haveI : Algebra.IsIntegral L (B ⧸ Module.annihilator B N) := ⟨fun q => (isIntegral_algHom_iff g hinj).mp (Algebra.IsIntegral.isIntegral _)⟩`. Conclude with `Order.krullDim_le_of_strictMono (fun P => (⟨Ideal.comap (algebraMap L (B ⧸ Module.annihilator B N)) P.asIdeal, inferInstance⟩ : PrimeSpectrum L)) (fun P Q h => Ideal.IsIntegral.comap_lt_comap h)`.
-/
theorem UpperTheory.V.AlgebraTools.supportDim_le_of_finite :
    ∀ (L B : Type) [CommRing L] [IsNoetherianRing L] [CommRing B] [Algebra L B] (N : Type) [AddCommGroup N] [Module B N]
      [Module L N] [IsScalarTower L B N] [Module.Finite L N], Module.supportDim B N ≤ ringKrullDim L := by
  intro L B _ _ _ _ N _ _ _ _ _
  have hfin : Module.Finite B N := Module.Finite.of_restrictScalars_finite L B N
  rw [Module.supportDim_eq_ringKrullDim_quotient_annihilator]
  let f : B →ₐ[L] Module.End L N := Algebra.lsmul L L N
  have hf : ∀ b : B, b ∈ Module.annihilator B N → f b = 0 := by
    intro b hb
    ext n
    exact Module.mem_annihilator.mp hb n
  let g : (B ⧸ Module.annihilator B N) →ₐ[L] Module.End L N :=
    Ideal.Quotient.liftₐ (Module.annihilator B N) f hf
  have hinj : Function.Injective g := by
    refine (injective_iff_map_eq_zero g).mpr ?_
    intro q hq
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
    rw [Ideal.Quotient.eq_zero_iff_mem]
    refine Module.mem_annihilator.mpr (fun n => ?_)
    have h := LinearMap.congr_fun hq n
    exact h
  haveI : Algebra.IsIntegral L (B ⧸ Module.annihilator B N) :=
    ⟨fun q => (isIntegral_algHom_iff g hinj).mp (Algebra.IsIntegral.isIntegral _)⟩
  exact Order.krullDim_le_of_strictMono
    (fun P => (⟨Ideal.comap (algebraMap L (B ⧸ Module.annihilator B N)) P.asIdeal, inferInstance⟩ :
      PrimeSpectrum L))
    (fun P Q h => Ideal.IsIntegral.comap_lt_comap h)
