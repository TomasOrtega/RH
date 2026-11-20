import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MSpBasis
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.LocFactor
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoEvLow
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.SpFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpRoots

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

/- English proof (translation)
Establish `hC : ∀ r : R, F (MvPowerSeries.C r) = algebraMap R L r`. Introduce `r`. Establish `: (MvPowerSeries.C r : MvPowerSeries (Fin q × Fin n) R) = algebraMap R _ r`. Rewrite using `[MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]`. Rewrite using `[this, F.commutes]`.

Establish `hle : spIdeal P ut ≤ RingHom.ker F`. Use `Ideal.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨j, k, rfl⟩`. Rewrite using `[SetLike.mem_coe, RingHom.mem_ker]`. Establish `h1 : ∀ i, F (MvPowerSeries.C (ut j i) + MvPowerSeries.X (j, i)) = a j i`.

Introduce `i`. Rewrite using `[map_add, hC, hX]`. Conclude with `add_sub_cancel _ _`. Establish `h2 : (F : MvPowerSeries (Fin q × Fin n) R →+* L).comp MvPowerSeries.C = algebraMap R L` using `RingHom.ext hC`. Rewrite using `[← RingHom.coe_coe F, ← Polynomial.coeff_map]`.

Rewrite using `[Polynomial.map_sub, Polynomial.map_prod, Polynomial.map_map, h2, ← ha j]`. Simplify using `only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, RingHom.coe_coe, h1, sub_self, Polynomial.coeff_zero]`. Conclude with `⟨Ideal.Quotient.liftₐ _ F fun z hz => hle hz, fun z => rfl⟩`.
-/
private theorem spCo_desc {R L : Type} [CommRing R] [CommRing L] [Algebra R L] {q n : ℕ}
    (P : Fin q → Polynomial R) (ut : Fin q → Fin n → R) (a : Fin q → Fin n → L)
    (ha : ∀ j, ∏ i, (Polynomial.X - Polynomial.C (a j i)) = (P j).map (algebraMap R L))
    (F : MvPowerSeries (Fin q × Fin n) R →ₐ[R] L)
    (hX : ∀ p, F (MvPowerSeries.X p) = a p.1 p.2 - algebraMap R L (ut p.1 p.2)) :
    ∃ F' : Sp P ut →ₐ[R] L, ∀ z, F' (Sp.mk P ut z) = F z := by
  classical
  have hC : ∀ r : R, F (MvPowerSeries.C r) = algebraMap R L r := by
    intro r
    have : (MvPowerSeries.C r : MvPowerSeries (Fin q × Fin n) R) = algebraMap R _ r := by
      rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    rw [this, F.commutes]
  have hle : spIdeal P ut ≤ RingHom.ker F := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨j, k, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker]
    have h1 : ∀ i, F (MvPowerSeries.C (ut j i) + MvPowerSeries.X (j, i)) = a j i := by
      intro i
      rw [map_add, hC, hX]
      exact add_sub_cancel _ _
    have h2 : (F : MvPowerSeries (Fin q × Fin n) R →+* L).comp MvPowerSeries.C = algebraMap R L :=
      RingHom.ext hC
    rw [← RingHom.coe_coe F, ← Polynomial.coeff_map]
    rw [Polynomial.map_sub, Polynomial.map_prod, Polynomial.map_map, h2, ← ha j]
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, RingHom.coe_coe, h1, sub_self,
      Polynomial.coeff_zero]
  exact ⟨Ideal.Quotient.liftₐ _ F fun z hz => hle hz, fun z => rfl⟩

/- English proof (translation)
Take `⟨bas, -⟩` from `mSplitAlg_basis (Fin q) n R P (fun j => (h j).1) (fun j => (h j).2.1)`. Use `haveI : Module.Free R (MSplitAlg P n) := Module.Free.of_basis bas`. Use `haveI : Module.Finite R (MSplitAlg P n) := Module.Finite.of_basis bas`. Establish `hχ : ∀ j, ∏ i, (Polynomial.X - Polynomial.C (residue R (ut j i))) = (P j).map (algebraMap R (ResidueField R))`. Introduce `j`.

Rewrite using `[ResidueField.algebraMap_eq, (h j).2.2]`. Take `⟨χ, hχr⟩ : ∃ χ : (MSplitAlg P n) →ₐ[R] ResidueField R, ∀ j i, χ (MSplitAlg.root P n j i) = residue R (ut j i)` from `⟨MSplitAlg.lift P n _ hχ, MSplitAlg.lift_root P n _ hχ⟩`. Establish `hχalg : ∀ r : R, χ (algebraMap R (MSplitAlg P n) r) = residue R r`. Introduce `r`. Rewrite using `[χ.commutes, ResidueField.algebraMap_eq]`.

Establish `hχs : Function.Surjective χ`. Introduce `y`. Take `⟨r, rfl⟩` from `residue_surjective y`. Conclude with `⟨_, hχalg r⟩`. Take `⟨n0, hn0⟩ : ∃ n0 : Ideal (MSplitAlg P n), n0 = RingHom.ker χ` from `⟨_, rfl⟩`.

Use `haveI : n0.IsMaximal := hn0 ▸ RingHom.ker_isMaximal_of_surjective χ hχs`. Take `⟨hBs, hBfin, hBloc, hBcpl, hBfree, -, hBuniv⟩` from `local_factor R (MSplitAlg P n) n0`. Use `haveI := hBfin`. Use `haveI := hBloc`. Use `haveI : Module.Free R (Localization.AtPrime n0) := hBfree inferInstance`.

Use `haveI : IsNoetherianRing (Localization.AtPrime n0) := isNoetherian_of_tower R (inferInstance : IsNoetherian R (Localization.AtPrime n0))`. Establish `hmem0 : ∀ y, y ∈ n0 ↔ χ y = 0` using `fun y => by rw [hn0, RingHom.mem_ker]`. Establish `hinB : ∀ y ∈ n0, algebraMap (MSplitAlg P n) (Localization.AtPrime n0) y ∈ maximalIdeal (Localization.AtPrime n0)` using `fun y hy => (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime n0) n0 y).2 hy`. Establish `hroot : ∀ j i, MSplitAlg.root P n j i - algebraMap R (MSplitAlg P n) (ut j i) ∈ n0`. Introduce `j i`.

Rewrite using `[hmem0, map_sub, hχalg, hχr, sub_self]`. Use `haveI hRR : IsCO R R := @IsCO.mk R R _ _ _ _ _ _ inferInstance ⟨fun a ha => ha⟩ (fun x => ⟨x, by rw [Algebra.algebraMap_self, RingHom.id_apply, sub_self]; exact zero_mem _⟩)`. Use `haveI hRB : IsCO R (Localization.AtPrime n0) := @IsCO.mk R (Localization.AtPrime n0) _ _ _ _ _ _ hBcpl hBloc (fun x => by`. Take `⟨y, rfl⟩` from `hBs x`. Take `⟨r, hr⟩` from `residue_surjective (χ y)`.

Use `⟨r, ?_⟩` and prove the remaining obligations. Rewrite using `[IsScalarTower.algebraMap_apply R (MSplitAlg P n) (Localization.AtPrime n0), ← map_sub]`. Apply `hinB` to reduce the goal to its premises. Rewrite using `[hmem0, map_sub, hχalg, hr, sub_self])`. Establish `hmemB : ∀ p : Fin q × Fin n, algebraMap (MSplitAlg P n) (Localization.AtPrime n0) (MSplitAlg.root P n p.1 p.2) - algebraMap R (Localization.AtPrime n0) (ut p.1 p.2) ∈ maximalIdeal (Localization.AtPrime n0)`.

Introduce `p`. Rewrite using `[IsScalarTower.algebraMap_apply R (MSplitAlg P n) (Localization.AtPrime n0), ← map_sub]`. Conclude with `hinB _ (hroot p.1 p.2)`. Take `⟨F, ⟨hFC, hFX⟩, -⟩` from `co_ev R R (Localization.AtPrime n0) (Fin q × Fin n) (Algebra.ofId R (Localization.AtPrime n0)) (fun p => algebraMap (MSplitAlg P n) (Localization.AtPrime n0) (MSplitAlg.root P n p.1 p.2) - algebraMap R (Localization.AtPrime n0) (ut p.1 p.2)) hmemB`. Establish `hFX' : ∀ p : Fin q × Fin n, F (MvPowerSeries.X p) = algebraMap (MSplitAlg P n) (Localization.AtPrime n0) (MSplitAlg.root P n p.1 p.2) - algebraMap R (Localization.AtPrime n0) (ut p.1 p.2)` using `hFX`.

Establish `hFC' : ∀ x : R, F (MvPowerSeries.C x) = algebraMap R (Localization.AtPrime n0) x` using `fun x => hFC x`. Establish `hrootB : ∀ j, ∏ i, (Polynomial.X - Polynomial.C (algebraMap (MSplitAlg P n) (Localization.AtPrime n0) (MSplitAlg.root P n j i))) = (P j).map (algebraMap R (Localization.AtPrime n0))`. Introduce `j`. Use `congrArg (Polynomial.map (algebraMap (MSplitAlg P n) (Localization.AtPrime n0))) (MSplitAlg.prod_root P n j)` as an intermediate fact. Rewrite `this` using `[Polynomial.map_map, ← IsScalarTower.algebraMap_eq]`.

Rewrite using `[← this, Polynomial.map_prod]`. Simplify using `only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]`. Take `⟨Φ, hΦ⟩` from `spCo_desc P ut (fun j i => algebraMap (MSplitAlg P n) (Localization.AtPrime n0) (MSplitAlg.root P n j i)) hrootB F hFX`. Use `haveI : Nontrivial (Sp P ut) := Φ.toRingHom.domain_nontrivial`. Use `haveI : IsLocalRing (Sp P ut) := IsLocalRing.of_surjective' (Sp.mk P ut).toRingHom (fun z => Ideal.Quotient.mk_surjective z)`.

Take `⟨Ψ, hΨ⟩ : ∃ Ψ : (MSplitAlg P n) →ₐ[R] Sp P ut, ∀ j i, Ψ (MSplitAlg.root P n j i) = Sp.u P ut j i` from `⟨MSplitAlg.lift P n _ (fun j => (spRoots R q n P ut j).1), MSplitAlg.lift_root P n _ _⟩`. Take `⟨F0, hF0X, hF0C⟩ : ∃ F0 : MvPowerSeries (Fin q × Fin n) R →ₐ[R] ResidueField R, (∀ p, F0 (MvPowerSeries.X p) = 0) ∧ ∀ r, F0 (MvPowerSeries.C r) = residue R r` from `⟨{ toRingHom := (residue R).comp MvPowerSeries.constantCoeff commutes' := fun r => by show residue R (MvPowerSeries.constantCoeff (algebraMap R (MvPowerSeries (Fin q × Fin n) R) r)) = _`. Rewrite using `[MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, MvPowerSeries.constantCoeff_C, ResidueField.algebraMap_eq] },`. Use `fun p => by show residue R (MvPowerSeries.constantCoeff (MvPowerSeries.X p)) = 0`. Rewrite using `[MvPowerSeries.constantCoeff_X, map_zero],`.

Use `fun r => by show residue R (MvPowerSeries.constantCoeff (MvPowerSeries.C r)) = _`. Rewrite using `[MvPowerSeries.constantCoeff_C]⟩`. Establish `hF0X' : ∀ p : Fin q × Fin n, F0 (MvPowerSeries.X p) = residue R (ut p.1 p.2) - algebraMap R (ResidueField R) (ut p.1 p.2)`. Introduce `p`. Rewrite using `[hF0X, ResidueField.algebraMap_eq, sub_self]`.

Take `⟨χ', hχ'⟩` from `spCo_desc P ut (fun j i => residue R (ut j i)) hχ F0 hF0X'`. Establish `hχ'alg : ∀ r : R, χ' (algebraMap R (Sp P ut) r) = residue R r`. Introduce `r`. Rewrite using `[χ'.commutes, ResidueField.algebraMap_eq]`. Establish `hχ's : Function.Surjective χ'`.

Introduce `y`. Take `⟨r, rfl⟩` from `residue_surjective y`. Conclude with `⟨_, hχ'alg r⟩`. Establish `hkerχ' : RingHom.ker χ' = maximalIdeal (Sp P ut)` using `IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective χ' hχ's)`. Establish `hχΨ : χ'.comp Ψ = χ`.

Apply `MSplitAlg.hom_ext` to reduce the goal to its premises. Introduce `j i`. Rewrite using `[AlgHom.comp_apply, hΨ, hχr]`. Use `show χ' (Sp.mk P ut _) = _`. Rewrite using `[hχ', map_add, hF0C, hF0X, add_zero]`.

Establish `hcomap : Ideal.comap Ψ.toRingHom (maximalIdeal (Sp P ut)) = n0`. Use `Ideal.ext fun y => ?_` and prove the remaining obligations. Rewrite using `[Ideal.mem_comap, ← hkerχ', hmem0, RingHom.mem_ker]`. Use `show χ' (Ψ y) = 0 ↔ χ y = 0`. Rewrite using `[← AlgHom.comp_apply, hχΨ]`.

Take `⟨g0, hg0⟩` from `hBuniv (Sp P ut) Ψ.toRingHom hcomap`. Establish `hg0' : ∀ y, g0 (algebraMap (MSplitAlg P n) (Localization.AtPrime n0) y) = Ψ y` using `fun y => RingHom.congr_fun hg0 y`. Take `⟨g, hg⟩ : ∃ g : (Localization.AtPrime n0) →ₐ[R] Sp P ut, ∀ y, g (algebraMap (MSplitAlg P n) (Localization.AtPrime n0) y) = Ψ y` from `⟨{ g0 with commutes' := fun r => by show g0 (algebraMap R (Localization.AtPrime n0) r) = _`. Rewrite using `[IsScalarTower.algebraMap_apply R (MSplitAlg P n) (Localization.AtPrime n0), hg0', Ψ.commutes] }, hg0'⟩`. Establish `hΦu : ∀ j i, Φ (Sp.u P ut j i) = algebraMap (MSplitAlg P n) (Localization.AtPrime n0) (MSplitAlg.root P n j i)`.

Introduce `j i`. Use `show Φ (Sp.mk P ut _) = _`. Rewrite using `[hΦ, map_add, hFC', hFX']`. Conclude with `add_sub_cancel _ _`. Establish `hΦg : Φ.comp g = AlgHom.id R (Localization.AtPrime n0)`.

Establish `h1 : (Φ.comp g).comp (IsScalarTower.toAlgHom R (MSplitAlg P n) (Localization.AtPrime n0)) = IsScalarTower.toAlgHom R (MSplitAlg P n) (Localization.AtPrime n0)`. Apply `MSplitAlg.hom_ext` to reduce the goal to its premises. Introduce `j i`. Rewrite using `[AlgHom.comp_apply, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', hg, hΨ, hΦu]`. Use `AlgHom.ext fun x => ?_` and prove the remaining obligations.

Take `⟨y, rfl⟩` from `hBs x`. Conclude with `AlgHom.congr_fun h1 y`. Use `haveI : IsCO R (MvPowerSeries (Fin q × Fin n) R) := co_mvps R R (Fin q × Fin n)`. Use `haveI : IsCO R (Sp P ut) := co_quot R (MvPowerSeries (Fin q × Fin n) R) (Sp P ut) (Sp.mk P ut) (fun z => Ideal.Quotient.mk_surjective z)`. Establish `hmemSp : ∀ p : Fin q × Fin n, Sp.mk P ut (MvPowerSeries.X p) ∈ maximalIdeal (Sp P ut)`.

Introduce `p`. Rewrite using `[← hkerχ', RingHom.mem_ker, hχ', hF0X]`. Take `⟨F1, -, huniq⟩` from `co_ev R R (Sp P ut) (Fin q × Fin n) (Algebra.ofId R (Sp P ut)) (fun p => Sp.mk P ut (MvPowerSeries.X p)) hmemSp`. Establish `hCalg : ∀ (f : MvPowerSeries (Fin q × Fin n) R →ₐ[R] Sp P ut) (x : R), f (MvPowerSeries.C x) = Algebra.ofId R (Sp P ut) x`. Introduce `f x`.

Establish `: (MvPowerSeries.C x : MvPowerSeries (Fin q × Fin n) R) = algebraMap R _ x`. Rewrite using `[MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]`. Rewrite using `[this, f.commutes, Algebra.ofId_apply]`. Establish `hX1 : ∀ p : Fin q × Fin n, ((g.comp Φ).comp (Sp.mk P ut)) (MvPowerSeries.X p) = Sp.mk P ut (MvPowerSeries.X p)`. Introduce `p`.

Rewrite using `[AlgHom.comp_apply, AlgHom.comp_apply, hΦ, hFX', map_sub, AlgHom.commutes, hg, hΨ]`. Conclude with `(spRoots R q n P ut p.1).2 p.2`. Establish `hgΦ : g.comp Φ = AlgHom.id R (Sp P ut)`. Apply `Ideal.Quotient.algHom_ext` to reduce the goal to its premises. Conclude with `(huniq _ ⟨hCalg _, hX1⟩).trans (huniq _ ⟨hCalg _, fun p => rfl⟩).symm`.

Set `e : Sp P ut ≃ₐ[R] (Localization.AtPrime n0)` to `AlgEquiv.ofAlgHom Φ g hΦg hgΦ`. Use `⟨inferInstance, Module.Free.of_equiv e.symm.toLinearEquiv, ?_⟩` and prove the remaining obligations. Rewrite using `[eq_top_iff]`. Introduce and unpack `z -`. Take `⟨y, hy⟩` from `hBs (Φ z)`.

Establish `hz : Ψ y = z`. Rewrite using `[← hg y, hy]`. Conclude with `AlgHom.congr_fun hgΦ z`. Rewrite using `[← hz]`. Use `clear hz hy`.

Take `⟨p, rfl⟩` from `Ideal.Quotient.mk_surjective y`. Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C r => show Ψ (algebraMap R (MSplitAlg P n) r) ∈ _`. Rewrite using `[Ψ.commutes]`. Conclude with `Subalgebra.algebraMap_mem _ r`.

Consider the case `add p1 p2 h1 h2`. Rewrite using `[map_add, map_add]`. Conclude with `add_mem h1 h2`. Consider the case `mul_X p s hp`. Rewrite using `[map_mul, map_mul]`.

Use `mul_mem hp (Algebra.subset_adjoin ⟨s, ?_⟩)` and prove the remaining obligations. Conclude with `(hΨ s.1 s.2).symm`.
-/
private theorem splitting_algebra_nontrivial_free_generated (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] (q n : ℕ) (P : Fin q → Polynomial R) (ut : Fin q → Fin n → R)
    (h : ∀ j, (P j).Monic ∧ (P j).natDegree = n ∧
      (P j).map (residue R) = ∏ i, (Polynomial.X - Polynomial.C (residue R (ut j i)))) :
    Nontrivial (Sp P ut) ∧ Module.Free R (Sp P ut) ∧
      Algebra.adjoin R (Set.range fun p : Fin q × Fin n => Sp.u P ut p.1 p.2) = ⊤ := by
  classical
  obtain ⟨bas, -⟩ := mSplitAlg_basis (Fin q) n R P (fun j => (h j).1) (fun j => (h j).2.1)
  haveI : Module.Free R (MSplitAlg P n) := Module.Free.of_basis bas
  haveI : Module.Finite R (MSplitAlg P n) := Module.Finite.of_basis bas
  have hχ : ∀ j, ∏ i, (Polynomial.X - Polynomial.C (residue R (ut j i))) =
      (P j).map (algebraMap R (ResidueField R)) := by
    intro j
    rw [ResidueField.algebraMap_eq, (h j).2.2]
  obtain ⟨χ, hχr⟩ : ∃ χ : (MSplitAlg P n) →ₐ[R] ResidueField R,
      ∀ j i, χ (MSplitAlg.root P n j i) = residue R (ut j i) :=
    ⟨MSplitAlg.lift P n _ hχ, MSplitAlg.lift_root P n _ hχ⟩
  have hχalg : ∀ r : R, χ (algebraMap R (MSplitAlg P n) r) = residue R r := by
    intro r
    rw [χ.commutes, ResidueField.algebraMap_eq]
  have hχs : Function.Surjective χ := by
    intro y
    obtain ⟨r, rfl⟩ := residue_surjective y
    exact ⟨_, hχalg r⟩
  obtain ⟨n0, hn0⟩ : ∃ n0 : Ideal (MSplitAlg P n), n0 = RingHom.ker χ := ⟨_, rfl⟩
  haveI : n0.IsMaximal := hn0 ▸ RingHom.ker_isMaximal_of_surjective χ hχs
  obtain ⟨hBs, hBfin, hBloc, hBcpl, hBfree, -, hBuniv⟩ := local_factor R (MSplitAlg P n) n0
  haveI := hBfin
  haveI := hBloc
  haveI : Module.Free R (Localization.AtPrime n0) := hBfree inferInstance
  haveI : IsNoetherianRing (Localization.AtPrime n0) := isNoetherian_of_tower R (inferInstance : IsNoetherian R (Localization.AtPrime n0))
  have hmem0 : ∀ y, y ∈ n0 ↔ χ y = 0 := fun y => by rw [hn0, RingHom.mem_ker]
  have hinB : ∀ y ∈ n0, algebraMap (MSplitAlg P n) (Localization.AtPrime n0) y ∈ maximalIdeal (Localization.AtPrime n0) := fun y hy =>
    (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime n0) n0 y).2 hy
  have hroot : ∀ j i, MSplitAlg.root P n j i - algebraMap R (MSplitAlg P n) (ut j i) ∈ n0 := by
    intro j i
    rw [hmem0, map_sub, hχalg, hχr, sub_self]
  haveI hRR : IsCO R R := @IsCO.mk R R _ _ _ _ _ _ inferInstance ⟨fun a ha => ha⟩
    (fun x => ⟨x, by rw [Algebra.algebraMap_self, RingHom.id_apply, sub_self]; exact zero_mem _⟩)
  haveI hRB : IsCO R (Localization.AtPrime n0) := @IsCO.mk R (Localization.AtPrime n0) _ _ _ _ _ _ hBcpl hBloc (fun x => by
    obtain ⟨y, rfl⟩ := hBs x
    obtain ⟨r, hr⟩ := residue_surjective (χ y)
    refine ⟨r, ?_⟩
    rw [IsScalarTower.algebraMap_apply R (MSplitAlg P n) (Localization.AtPrime n0), ← map_sub]
    apply hinB
    rw [hmem0, map_sub, hχalg, hr, sub_self])
  have hmemB : ∀ p : Fin q × Fin n, algebraMap (MSplitAlg P n) (Localization.AtPrime n0) (MSplitAlg.root P n p.1 p.2) -
      algebraMap R (Localization.AtPrime n0) (ut p.1 p.2) ∈ maximalIdeal (Localization.AtPrime n0) := by
    intro p
    rw [IsScalarTower.algebraMap_apply R (MSplitAlg P n) (Localization.AtPrime n0), ← map_sub]
    exact hinB _ (hroot p.1 p.2)
  obtain ⟨F, ⟨hFC, hFX⟩, -⟩ := co_ev R R (Localization.AtPrime n0) (Fin q × Fin n) (Algebra.ofId R (Localization.AtPrime n0))
    (fun p => algebraMap (MSplitAlg P n) (Localization.AtPrime n0) (MSplitAlg.root P n p.1 p.2) - algebraMap R (Localization.AtPrime n0) (ut p.1 p.2)) hmemB
  have hFX' : ∀ p : Fin q × Fin n, F (MvPowerSeries.X p) =
      algebraMap (MSplitAlg P n) (Localization.AtPrime n0) (MSplitAlg.root P n p.1 p.2) - algebraMap R (Localization.AtPrime n0) (ut p.1 p.2) := hFX
  have hFC' : ∀ x : R, F (MvPowerSeries.C x) = algebraMap R (Localization.AtPrime n0) x := fun x => hFC x
  have hrootB : ∀ j, ∏ i, (Polynomial.X - Polynomial.C (algebraMap (MSplitAlg P n) (Localization.AtPrime n0) (MSplitAlg.root P n j i))) =
      (P j).map (algebraMap R (Localization.AtPrime n0)) := by
    intro j
    have := congrArg (Polynomial.map (algebraMap (MSplitAlg P n) (Localization.AtPrime n0))) (MSplitAlg.prod_root P n j)
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq] at this
    rw [← this, Polynomial.map_prod]
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  obtain ⟨Φ, hΦ⟩ := spCo_desc P ut (fun j i => algebraMap (MSplitAlg P n) (Localization.AtPrime n0) (MSplitAlg.root P n j i)) hrootB F hFX
  haveI : Nontrivial (Sp P ut) := Φ.toRingHom.domain_nontrivial
  haveI : IsLocalRing (Sp P ut) := IsLocalRing.of_surjective' (Sp.mk P ut).toRingHom
    (fun z => Ideal.Quotient.mk_surjective z)
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : (MSplitAlg P n) →ₐ[R] Sp P ut, ∀ j i, Ψ (MSplitAlg.root P n j i) = Sp.u P ut j i :=
    ⟨MSplitAlg.lift P n _ (fun j => (spRoots R q n P ut j).1), MSplitAlg.lift_root P n _ _⟩
  obtain ⟨F0, hF0X, hF0C⟩ : ∃ F0 : MvPowerSeries (Fin q × Fin n) R →ₐ[R] ResidueField R,
      (∀ p, F0 (MvPowerSeries.X p) = 0) ∧ ∀ r, F0 (MvPowerSeries.C r) = residue R r :=
    ⟨{ toRingHom := (residue R).comp MvPowerSeries.constantCoeff
       commutes' := fun r => by
         show residue R (MvPowerSeries.constantCoeff (algebraMap R (MvPowerSeries (Fin q × Fin n) R) r)) = _
         rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
           MvPowerSeries.constantCoeff_C, ResidueField.algebraMap_eq] },
     fun p => by
       show residue R (MvPowerSeries.constantCoeff (MvPowerSeries.X p)) = 0
       rw [MvPowerSeries.constantCoeff_X, map_zero],
     fun r => by
       show residue R (MvPowerSeries.constantCoeff (MvPowerSeries.C r)) = _
       rw [MvPowerSeries.constantCoeff_C]⟩
  have hF0X' : ∀ p : Fin q × Fin n, F0 (MvPowerSeries.X p) =
      residue R (ut p.1 p.2) - algebraMap R (ResidueField R) (ut p.1 p.2) := by
    intro p
    rw [hF0X, ResidueField.algebraMap_eq, sub_self]
  obtain ⟨χ', hχ'⟩ := spCo_desc P ut (fun j i => residue R (ut j i)) hχ F0 hF0X'
  have hχ'alg : ∀ r : R, χ' (algebraMap R (Sp P ut) r) = residue R r := by
    intro r
    rw [χ'.commutes, ResidueField.algebraMap_eq]
  have hχ's : Function.Surjective χ' := by
    intro y
    obtain ⟨r, rfl⟩ := residue_surjective y
    exact ⟨_, hχ'alg r⟩
  have hkerχ' : RingHom.ker χ' = maximalIdeal (Sp P ut) :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective χ' hχ's)
  have hχΨ : χ'.comp Ψ = χ := by
    apply MSplitAlg.hom_ext
    intro j i
    rw [AlgHom.comp_apply, hΨ, hχr]
    show χ' (Sp.mk P ut _) = _
    rw [hχ', map_add, hF0C, hF0X, add_zero]
  have hcomap : Ideal.comap Ψ.toRingHom (maximalIdeal (Sp P ut)) = n0 := by
    refine Ideal.ext fun y => ?_
    rw [Ideal.mem_comap, ← hkerχ', hmem0, RingHom.mem_ker]
    show χ' (Ψ y) = 0 ↔ χ y = 0
    rw [← AlgHom.comp_apply, hχΨ]
  obtain ⟨g0, hg0⟩ := hBuniv (Sp P ut) Ψ.toRingHom hcomap
  have hg0' : ∀ y, g0 (algebraMap (MSplitAlg P n) (Localization.AtPrime n0) y) = Ψ y := fun y => RingHom.congr_fun hg0 y
  obtain ⟨g, hg⟩ : ∃ g : (Localization.AtPrime n0) →ₐ[R] Sp P ut, ∀ y, g (algebraMap (MSplitAlg P n) (Localization.AtPrime n0) y) = Ψ y :=
    ⟨{ g0 with
        commutes' := fun r => by
          show g0 (algebraMap R (Localization.AtPrime n0) r) = _
          rw [IsScalarTower.algebraMap_apply R (MSplitAlg P n) (Localization.AtPrime n0), hg0', Ψ.commutes] }, hg0'⟩
  have hΦu : ∀ j i, Φ (Sp.u P ut j i) = algebraMap (MSplitAlg P n) (Localization.AtPrime n0) (MSplitAlg.root P n j i) := by
    intro j i
    show Φ (Sp.mk P ut _) = _
    rw [hΦ, map_add, hFC', hFX']
    exact add_sub_cancel _ _
  have hΦg : Φ.comp g = AlgHom.id R (Localization.AtPrime n0) := by
    have h1 : (Φ.comp g).comp (IsScalarTower.toAlgHom R (MSplitAlg P n) (Localization.AtPrime n0)) = IsScalarTower.toAlgHom R (MSplitAlg P n) (Localization.AtPrime n0) := by
      apply MSplitAlg.hom_ext
      intro j i
      rw [AlgHom.comp_apply, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', hg, hΨ, hΦu]
    refine AlgHom.ext fun x => ?_
    obtain ⟨y, rfl⟩ := hBs x
    exact AlgHom.congr_fun h1 y
  haveI : IsCO R (MvPowerSeries (Fin q × Fin n) R) := co_mvps R R (Fin q × Fin n)
  haveI : IsCO R (Sp P ut) := co_quot R (MvPowerSeries (Fin q × Fin n) R) (Sp P ut) (Sp.mk P ut)
    (fun z => Ideal.Quotient.mk_surjective z)
  have hmemSp : ∀ p : Fin q × Fin n, Sp.mk P ut (MvPowerSeries.X p) ∈ maximalIdeal (Sp P ut) := by
    intro p
    rw [← hkerχ', RingHom.mem_ker, hχ', hF0X]
  obtain ⟨F1, -, huniq⟩ := co_ev R R (Sp P ut) (Fin q × Fin n) (Algebra.ofId R (Sp P ut))
    (fun p => Sp.mk P ut (MvPowerSeries.X p)) hmemSp
  have hCalg : ∀ (f : MvPowerSeries (Fin q × Fin n) R →ₐ[R] Sp P ut) (x : R),
      f (MvPowerSeries.C x) = Algebra.ofId R (Sp P ut) x := by
    intro f x
    have : (MvPowerSeries.C x : MvPowerSeries (Fin q × Fin n) R) = algebraMap R _ x := by
      rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    rw [this, f.commutes, Algebra.ofId_apply]
  have hX1 : ∀ p : Fin q × Fin n, ((g.comp Φ).comp (Sp.mk P ut)) (MvPowerSeries.X p) =
      Sp.mk P ut (MvPowerSeries.X p) := by
    intro p
    rw [AlgHom.comp_apply, AlgHom.comp_apply, hΦ, hFX', map_sub, AlgHom.commutes, hg, hΨ]
    exact (spRoots R q n P ut p.1).2 p.2
  have hgΦ : g.comp Φ = AlgHom.id R (Sp P ut) := by
    apply Ideal.Quotient.algHom_ext
    exact (huniq _ ⟨hCalg _, hX1⟩).trans (huniq _ ⟨hCalg _, fun p => rfl⟩).symm
  let e : Sp P ut ≃ₐ[R] (Localization.AtPrime n0) := AlgEquiv.ofAlgHom Φ g hΦg hgΦ
  refine ⟨inferInstance, Module.Free.of_equiv e.symm.toLinearEquiv, ?_⟩
  rw [eq_top_iff]
  rintro z -
  obtain ⟨y, hy⟩ := hBs (Φ z)
  have hz : Ψ y = z := by
    rw [← hg y, hy]
    exact AlgHom.congr_fun hgΦ z
  rw [← hz]
  clear hz hy
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
  induction p using MvPolynomial.induction_on with
  | C r =>
    show Ψ (algebraMap R (MSplitAlg P n) r) ∈ _
    rw [Ψ.commutes]
    exact Subalgebra.algebraMap_mem _ r
  | add p1 p2 h1 h2 =>
    rw [map_add, map_add]
    exact add_mem h1 h2
  | mul_X p s hp =>
    rw [map_mul, map_mul]
    refine mul_mem hp (Algebra.subset_adjoin ⟨s, ?_⟩)
    exact (hΨ s.1 s.2).symm

/- English proof (translation)
Introduce `O R _ _ _ _ _ q n P ut h`. Use `haveI : IsNoetherianRing R := IsCO.toIsNoetherian (O := O)`. Use `haveI : IsAdicComplete (maximalIdeal R) R := IsCO.complete (O := O)`. Take `⟨hnt, hfree, hadj⟩` from `splitting_algebra_nontrivial_free_generated R q n P ut h`. Take `⟨hfin, -⟩` from `BC.sp_fin R q n P ut`.

Use `haveI := hnt`. Use `haveI := co_mvps O R (Fin q × Fin n)`. Use `⟨?_, hfree, hfin, hadj⟩` and prove the remaining obligations. Conclude with `co_quot O (MvPowerSeries (Fin q × Fin n) R) (Sp P ut) ((Sp.mk P ut).restrictScalars O) (fun z => Ideal.Quotient.mk_surjective z)`.
-/
theorem UpperTheory.V.Pa.Core.spCo :
    ∀ (O R : Type) [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R] (q n : ℕ) (P : Fin q → Polynomial R) (ut : Fin q → Fin n → R), (∀ j, (P j).Monic ∧ (P j).natDegree = n ∧ (P j).map (residue R) = ∏ i, (Polynomial.X - Polynomial.C (residue R (ut j i)))) → IsCO O (Sp P ut) ∧ Module.Free R (Sp P ut) ∧ Module.Finite R (Sp P ut) ∧ Algebra.adjoin R (Set.range fun p : Fin q × Fin n => Sp.u P ut p.1 p.2) = ⊤ := by
  intro O R _ _ _ _ _ q n P ut h
  haveI : IsNoetherianRing R := IsCO.toIsNoetherian (O := O)
  haveI : IsAdicComplete (maximalIdeal R) R := IsCO.complete (O := O)
  obtain ⟨hnt, hfree, hadj⟩ := splitting_algebra_nontrivial_free_generated R q n P ut h
  obtain ⟨hfin, -⟩ := BC.sp_fin R q n P ut
  haveI := hnt
  haveI := co_mvps O R (Fin q × Fin n)
  refine ⟨?_, hfree, hfin, hadj⟩
  exact co_quot O (MvPowerSeries (Fin q × Fin n) R) (Sp P ut) ((Sp.mk P ut).restrictScalars O)
    (fun z => Ideal.Quotient.mk_surjective z)
