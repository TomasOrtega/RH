import ReciprocityTheory.CommutativeAlgebra.ChainConnInDim

namespace ReciprocityTheory.CA

open Polynomial RingTheory.Sequence

/- English proof (translation)
Establish `hk : RingHom.ker (mapRingHom (Ideal.Quotient.mk J)) = J.map (C : S →+* S[X])`. Rewrite using `[Polynomial.ker_mapRingHom, Ideal.mk_ker]`. Rewrite `hgh`, the goal using `[← hk, RingHom.mem_ker]`. Simplify using `only [map_mul, coe_mapRingHom] at hgh`. Rewrite using `[coe_mapRingHom]`.

Conclude with `((hg.map (Ideal.Quotient.mk J)).mul_right_eq_zero_iff).mp hgh`.
-/
theorem pstep_monic_mem_of_mul {S : Type*} [CommRing S] (J : Ideal S) {g h : S[X]} (hg : g.Monic)
    (hgh : g * h ∈ J.map (C : S →+* S[X])) : h ∈ J.map (C : S →+* S[X]) := by

  have hk : RingHom.ker (mapRingHom (Ideal.Quotient.mk J)) = J.map (C : S →+* S[X]) := by
    rw [Polynomial.ker_mapRingHom, Ideal.mk_ker]
  rw [← hk, RingHom.mem_ker] at hgh ⊢
  simp only [map_mul, coe_mapRingHom] at hgh
  rw [coe_mapRingHom]
  exact ((hg.map (Ideal.Quotient.mk J)).mul_right_eq_zero_iff).mp hgh

/- English proof (translation)
Rewrite using `[isWeaklyRegular_append_iff]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `h` using `hrs.of_flat (S := S[X])`. Rewrite `h` using `[Polynomial.algebraMap_eq]`. Then use the resulting hypothesis. Rewrite using `[isWeaklyRegular_singleton_iff]`.

Establish `hI : (Ideal.ofList (rs.map C) • ⊤ : Submodule S[X] S[X]) = (Ideal.ofList rs).map (C : S →+* S[X])`. Rewrite using `[Ideal.smul_eq_mul, Ideal.mul_top, Ideal.map_ofList]`. Introduce `a b hab`. Take `⟨a, rfl⟩` from `Submodule.Quotient.mk_surjective _ a`. Take `⟨b, rfl⟩` from `Submodule.Quotient.mk_surjective _ b`.

Express the relevant statement in the definitionally equal form `g • Submodule.Quotient.mk a = g • Submodule.Quotient.mk b at hab`. Rewrite `hab` using `[← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, hI]`. Rewrite `hab` using `[smul_eq_mul, smul_eq_mul, ← mul_sub]`. Rewrite using `[Submodule.Quotient.eq, hI]`. Conclude with `pstep_monic_mem_of_mul _ hg hab`.
-/
theorem isWeaklyRegular_map_C_append_monic {S : Type*} [CommRing S] {rs : List S}
    (hrs : IsWeaklyRegular S rs) {g : S[X]} (hg : g.Monic) :
    IsWeaklyRegular S[X] (rs.map C ++ [g]) := by
  rw [isWeaklyRegular_append_iff]
  refine ⟨?_, ?_⟩
  · have h := hrs.of_flat (S := S[X])
    rwa [Polynomial.algebraMap_eq] at h
  · rw [isWeaklyRegular_singleton_iff]
    have hI : (Ideal.ofList (rs.map C) • ⊤ : Submodule S[X] S[X]) =
        (Ideal.ofList rs).map (C : S →+* S[X]) := by
      rw [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.map_ofList]
    intro a b hab
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    change g • Submodule.Quotient.mk a = g • Submodule.Quotient.mk b at hab
    rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, hI] at hab
    rw [smul_eq_mul, smul_eq_mul, ← mul_sub] at hab
    rw [Submodule.Quotient.eq, hI]
    exact pstep_monic_mem_of_mul _ hg hab

/- English proof (translation)
Use `letI : Algebra S T := e.toRingHom.toAlgebra`. Set `l : T ≃ₗ[S] S` to `{ e.symm.toAddEquiv with map_smul' := fun c t => by`. Express the relevant statement in the definitionally equal form `e.symm (algebraMap S T c * t) = c * e.symm t`. Rewrite using `[RingHom.algebraMap_toAlgebra, map_mul]`. Simplify using `}`.

Use `haveI : Module.Flat S T := Module.Flat.of_linearEquiv l`. Conclude with `hrs.of_flat`.
-/
theorem isWeaklyRegular_map_ringEquiv {S T : Type*} [CommRing S] [CommRing T] (e : S ≃+* T)
    {rs : List S} (hrs : IsWeaklyRegular S rs) : IsWeaklyRegular T (rs.map e) := by
  letI : Algebra S T := e.toRingHom.toAlgebra

  let l : T ≃ₗ[S] S :=
    { e.symm.toAddEquiv with
      map_smul' := fun c t => by
        change e.symm (algebraMap S T c * t) = c * e.symm t
        rw [RingHom.algebraMap_toAlgebra, map_mul]
        simp }
  haveI : Module.Flat S T := Module.Flat.of_linearEquiv l
  exact hrs.of_flat

end ReciprocityTheory.CA
