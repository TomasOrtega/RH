import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.EpC

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

/- English proof (translation)
Use `letI : Module O M := Module.compHom M φ`. Use `haveI hmax : (RingHom.ker f).IsMaximal := RingHom.ker_isMaximal_of_surjective f hf`. Establish `hker : RingHom.ker f = maximalIdeal O` using `IsLocalRing.eq_maximalIdeal hmax`. Establish `hT : Module.IsTorsionBySet O M (RingHom.ker f)`. Introduce and unpack `m ⟨o, ho⟩`.

Conclude with `hM o (hker ▸ ho) m`. Use `letI : Field (O ⧸ RingHom.ker f) := Ideal.Quotient.field _`. Use `letI : Module (O ⧸ RingHom.ker f) M := hT.module`. Use `haveI : Module.Free (O ⧸ RingHom.ker f) M := Module.Free.of_divisionRing _ _`. Use `haveI : Module.Projective (O ⧸ RingHom.ker f) M := Module.Projective.of_free`.

Take `⟨Ψ, hΨ⟩` from `Module.Projective.exists_dual_ne_zero (O ⧸ RingHom.ker f) hq`. Set `e` to `RingHom.quotientKerEquivOfSurjective hf`. Use `⟨(e : (O ⧸ RingHom.ker f) →+* F).toAddMonoidHom.comp Ψ.toAddMonoidHom, fun o m => ?_, ?_⟩` and prove the remaining obligations. Use `show e (Ψ (φ o • m)) = f o * e (Ψ m)`. Establish `hs : (φ o • m : M) = (Ideal.Quotient.mk (RingHom.ker f) o) • m` using `(hT.mk_smul o m).symm`.

Rewrite using `[hs, map_smul, smul_eq_mul, map_mul, RingHom.quotientKerEquivOfSurjective_apply_mk]`. Use `show e (Ψ q) ≠ 0`. Conclude with `fun h => hΨ (e.injective (h.trans (map_zero e).symm))`.
-/
private theorem exists_semilinear_functional_nonzero {O B F M : Type} [CommRing O] [IsLocalRing O] [CommRing B] [Field F] [AddCommGroup M]
    [Module B M] (φ : O →+* B) (f : O →+* F) (hf : Function.Surjective f)
    (hM : ∀ o ∈ maximalIdeal O, ∀ m : M, φ o • m = 0) (q : M) (hq : q ≠ 0) :
    ∃ Φ : M →+ F, (∀ o m, Φ (φ o • m) = f o * Φ m) ∧ Φ q ≠ 0 := by
  letI : Module O M := Module.compHom M φ
  haveI hmax : (RingHom.ker f).IsMaximal := RingHom.ker_isMaximal_of_surjective f hf
  have hker : RingHom.ker f = maximalIdeal O := IsLocalRing.eq_maximalIdeal hmax
  have hT : Module.IsTorsionBySet O M (RingHom.ker f) := by
    rintro m ⟨o, ho⟩
    exact hM o (hker ▸ ho) m
  letI : Field (O ⧸ RingHom.ker f) := Ideal.Quotient.field _
  letI : Module (O ⧸ RingHom.ker f) M := hT.module
  haveI : Module.Free (O ⧸ RingHom.ker f) M := Module.Free.of_divisionRing _ _
  haveI : Module.Projective (O ⧸ RingHom.ker f) M := Module.Projective.of_free
  obtain ⟨Ψ, hΨ⟩ := Module.Projective.exists_dual_ne_zero (O ⧸ RingHom.ker f) hq
  let e := RingHom.quotientKerEquivOfSurjective hf
  refine ⟨(e : (O ⧸ RingHom.ker f) →+* F).toAddMonoidHom.comp Ψ.toAddMonoidHom, fun o m => ?_, ?_⟩
  · show e (Ψ (φ o • m)) = f o * e (Ψ m)
    have hs : (φ o • m : M) = (Ideal.Quotient.mk (RingHom.ker f) o) • m := (hT.mk_smul o m).symm
    rw [hs, map_smul, smul_eq_mul, map_mul, RingHom.quotientKerEquivOfSurjective_apply_mk]
  · show e (Ψ q) ≠ 0
    exact fun h => hΨ (e.injective (h.trans (map_zero e).symm))

/- English proof (translation)
Introduce `l _ S y hy`. Assume the negation of the conclusion as `hne`. Set `P` to `S.J2 • (⊤ : Submodule S.Bh S.U.N)`. Establish `hq : (Submodule.Quotient.mk y : S.U.N ⧸ P) ≠ 0`. Rewrite using `[Ne, Submodule.Quotient.mk_eq_zero]`.

Conclude with `hne`. Establish `hJ : ∀ b ∈ S.J2, ∀ z : S.U.N, b • z ∈ P` using `fun b hb z => Submodule.smul_mem_smul hb trivial`. Establish `hM : ∀ o ∈ maximalIdeal S.OO, ∀ m : S.U.N ⧸ P, algebraMap S.OO S.Bh o • m = 0`. Introduce `o ho m`. Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective P m`.

Rewrite using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Conclude with `hJ _ (Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ ho))) z`. Take `⟨Φ0, hΦ0, hne0⟩` from `exists_semilinear_functional_nonzero (algebraMap S.OO S.Bh) (S.rF.comp (algebraMap S.OO S.Bh)) S.oo_surj hM _ hq`. Set `Φ : S.U.N →+ S.F` to `Φ0.comp P.mkQ.toAddMonoidHom`. Establish `hmem : Φ ∈ S.Ph`.

Use `⟨fun o z => ?_, fun b hb z => ?_⟩` and prove the remaining obligations. Use `show Φ0 (P.mkQ (algebraMap S.OO S.Bh o • z)) = S.rF (algebraMap S.OO S.Bh o) * Φ0 (P.mkQ z)`. Rewrite using `[map_smul]`. Conclude with `hΦ0 o _`. Use `show Φ0 (P.mkQ (b • z)) = 0`.

Rewrite using `[Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero P).mpr (hJ b hb z), map_zero]`. Conclude with `hne0 (hy Φ hmem)`.
-/
theorem UpperTheory.V.Pa.phSep :
    ∀ (l : ℕ) [Fact l.Prime] (S : Ctx l), ∀ y : S.U.N, (∀ Φ ∈ S.Ph, Φ y = 0) → y ∈ S.J2 • (⊤ : Submodule S.Bh S.U.N) := by
  intro l _ S y hy
  by_contra hne
  let P := S.J2 • (⊤ : Submodule S.Bh S.U.N)
  have hq : (Submodule.Quotient.mk y : S.U.N ⧸ P) ≠ 0 := by
    rw [Ne, Submodule.Quotient.mk_eq_zero]
    exact hne
  have hJ : ∀ b ∈ S.J2, ∀ z : S.U.N, b • z ∈ P := fun b hb z => Submodule.smul_mem_smul hb trivial
  have hM : ∀ o ∈ maximalIdeal S.OO, ∀ m : S.U.N ⧸ P, algebraMap S.OO S.Bh o • m = 0 := by
    intro o ho m
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective P m
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact hJ _ (Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ ho))) z
  obtain ⟨Φ0, hΦ0, hne0⟩ :=
    exists_semilinear_functional_nonzero (algebraMap S.OO S.Bh) (S.rF.comp (algebraMap S.OO S.Bh)) S.oo_surj hM _ hq
  let Φ : S.U.N →+ S.F := Φ0.comp P.mkQ.toAddMonoidHom
  have hmem : Φ ∈ S.Ph := by
    refine ⟨fun o z => ?_, fun b hb z => ?_⟩
    · show Φ0 (P.mkQ (algebraMap S.OO S.Bh o • z)) = S.rF (algebraMap S.OO S.Bh o) * Φ0 (P.mkQ z)
      rw [map_smul]
      exact hΦ0 o _
    · show Φ0 (P.mkQ (b • z)) = 0
      rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero P).mpr (hJ b hb z), map_zero]
  exact hne0 (hy Φ hmem)
