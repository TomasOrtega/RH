import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UnitThetaConstantsGenerateIntegralTorsionImports
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnivBasis
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsTwistBasisOffPrime
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaFibre

open TwistLoc VVRank

/- English proof (translation)
Take `rfl : (fun k => h ≫ φ k) = φ'` from `funext e`. Take `⟨t, ht, s, hs⟩` from `exists_clear_denominator M H hL φ ε s'`. Use `⟨t, ht, s, fun Z r z J hJ => ?_⟩` and prove the remaining obligations. Rewrite using `[sval_of s (r ≫ h) z J (fun k => J (r ≫ h ≫ φ k)) (fun k => by rw [Category.assoc])]`. Conclude with `hs Z r z _ (hJ.mem (fun k => h ≫ φ k) r)`.
-/
theorem exists_clear_sval {R Rm : Type} [CommRing R] [CommRing Rm] [Algebra R Rm] (M : Submonoid R)
    [IsLocalization M Rm] {X Y Y' : Scheme.{0}} {π : Y ⟶ Spec (CommRingCat.of R)}
    {π' : Y' ⟶ Spec (CommRingCat.of Rm)} {h : Y' ⟶ Y}
    (H : IsPullback h π' π (Spec.map (CommRingCat.ofHom (algebraMap R Rm))))
    [CompactSpace Y] [QuasiSeparatedSpace Y] {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (φ' : K → (Y' ⟶ X)) (e : ∀ k, h ≫ φ k = φ' k) (ε : K → ℤ)
    (s' : LB.Sec (LB.LinComb L φ' ε)) :
    ∃ t ∈ M, ∃ s : LB.Sec (LB.LinComb L φ ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J), Good L z J →
      sval s (r ≫ h) z J = gc (r ≫ h ≫ π) z t * sval s' r z J := by
  obtain rfl : (fun k => h ≫ φ k) = φ' := funext e
  obtain ⟨t, ht, s, hs⟩ := exists_clear_denominator M H hL φ ε s'
  refine ⟨t, ht, s, fun Z r z J hJ => ?_⟩
  rw [sval_of s (r ≫ h) z J (fun k => J (r ≫ h ≫ φ k)) (fun k => by rw [Category.assoc])]
  exact hs Z r z _ (hJ.mem (fun k => h ≫ φ k) r)

/- English proof (translation)
Introduce `hS R _ P th hth s`. Take `⟨V, hV, b, hb⟩` from `ThetaReal.exists_univBasis hS P 1 le_rfl s`. Establish `hp : s.asIdeal.IsPrime` using `s.isPrime`. Set `Rp` to `Localization.AtPrime s.asIdeal`. Set `k` to `IsLocalRing.ResidueField Rp`.

Set `Tp : Over (Sp R)` to `Over.mk (spMap (algebraMap R Rp))`. Set `Tk : Over (Sp R)` to `Over.mk (spMap (IsLocalRing.residue Rp) ≫ spMap (algebraMap R Rp))`. Set `hk : Tk ⟶ Tp` to `Over.homMk (spMap (IsLocalRing.residue Rp)) rfl`. Set `u : Tp ⟶ baseOver (Sp R)` to `Over.homMk Tp.hom (Category.comp_id _)`. Establish `hr : Set.range (spMap (algebraMap R Rp)) ⊆ Set.range V.ι`.

Introduce and unpack `_ ⟨q, rfl⟩`. Use `(Scheme.Opens.range_ι V).ge ?_` and prove the remaining obligations. Use `Specializes.mem_open ?_ V.isOpen hV` and prove the remaining obligations. Use `(PrimeSpectrum.le_iff_specializes _ _).1 fun x hx => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hx'`.

Conclude with `q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hx (IsLocalization.map_units Rp (⟨x, hx'⟩ : s.asIdeal.primeCompl)))`. Set `v : Tp ⟶ overRes (T` to `baseOver (Sp R)) V := Over.homMk (IsOpenImmersion.lift V.ι _ hr) (by show IsOpenImmersion.lift V.ι _ hr ≫ V.ι ≫ 𝟙 _ = spMap (algebraMap R Rp)`. Rewrite using `[Category.comp_id, IsOpenImmersion.lift_fac])`. Set `i₀ : Fin (1 ^ P.g)` to `⟨0, by simp⟩`. Set `bp : LB.Sec (LPow P.A P.L 1 Tp)` to `pullS P.A _ v (SecM.toSec P.A (b i₀))`.

Establish `haff : IsAffine Tk.left` using `inferInstanceAs (IsAffine (Spec _))`. Establish `hnt : Nontrivial Γ(Tk.left, ⊤)` using `(Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom.domain_nontrivial`. Take `⟨c, hc⟩` from `hb Tk (hk ≫ v)`. Establish `hne : (SecM.ofSec P.A (pullS P.A 1 hk bp) : SecM P.A P.L 1 Tk) ≠ 0` using `fun h0 => c.ne_zero i₀ ((hc i₀).trans ((pullM_comp P.A P.isLB _ hk v _).symm.trans h0))`. Establish `hsm` using `P.isAb.smooth`.

Establish `hpr` using `P.isAb.proper`. Establish `hred : IsReduced (Tk ⊗ P.A).left`. Establish `: IsReduced Tk.left` using `inferInstanceAs (IsReduced (Spec (CommRingCat.of k)))`. Establish `: Smooth (fst Tk P.A).left` using `inferInstanceAs (Smooth (pullback.fst Tk.hom P.A.hom))`. Use the proof step `GlobalTheory.isReduced_of_smooth_of_isReduced (fst Tk P.A).left`.

Choose the witnesses or unpack the hypotheses as in `⟨z, hz⟩ : ∃ z, z ∈ nonzeroLocus (pullS P.A 1 hk bp) := by`. Assume the negation of the conclusion as `hn`. Conclude with `hne (Subtype.ext (funext fun j => eq_zero_of_basicOpen_eq_bot ((pullS P.A 1 hk bp).f j) (eq_bot_iff.2 fun y hy => (hn ⟨y, TopologicalSpace.Opens.mem_iSup.2 ⟨j, hy⟩⟩).elim)))`. Establish `: CompactSpace P.A.left` using `QuasiCompact.compactSpace_of_compactSpace P.A.hom`. Establish `: QuasiSeparatedSpace P.A.left` using `(quasiSeparated_iff_quasiSeparatedSpace P.A.hom).mp inferInstance`.

Establish `H : IsPullback (snd Tp P.A).left (fst Tp P.A).left P.A.hom (spMap (algebraMap R Rp))` using `(IsPullback.of_hasPullback Tp.hom P.A.hom).flip`. Take `⟨t, ht, σ, hσ⟩` from `exists_clear_sval s.asIdeal.primeCompl H P.isLB (fun _ : Fin 1 => 𝟙 P.A.left) (fun _ => (snd Tp P.A).left) (fun _ => Category.comp_id _) (fun _ => 1) bp`. Take `⟨a, ha, -⟩` from `hth (pullTo (φ' := fun _ : Fin 1 => (snd (baseOver (Sp R)) P.A).left) σ (snd (baseOver (Sp R)) P.A).left (fun _ => Category.comp_id _))`. Use `choose J hJ using fun χ : (Tk ⊗ P.A).left ⟶ P.A.left => exists_chart P.isLB (χ z)`. Establish `hJ' : Good P.L z J` using `hJ`.

Set `r : (Tk ⊗ P.A).left ⟶ (Tp ⊗ P.A).left` to `𝟙 _ ≫ (hk ▷ P.A).left`. Set `ρ : (Tk ⊗ P.A).left ⟶ (baseOver (Sp R) ⊗ P.A).left` to `r ≫ (u ▷ P.A).left`. Establish `e₁ : ρ ≫ (snd (baseOver (Sp R)) P.A).left = r ≫ (snd Tp P.A).left`. Rewrite using `[Category.assoc, whisker_snd_left]`. Establish `e₂ : r ≫ (snd Tp P.A).left ≫ P.A.hom = (fst Tk P.A).left ≫ Tk.hom`.

Rewrite using `[Category.assoc, Category.id_comp, ← Category.assoc, whisker_snd_left, Over.w, Over.w]`. Establish `hs : ((fst Tk P.A).left ≫ Tk.hom) z = s` using `by show spMap (algebraMap R Rp) (spMap (IsLocalRing.residue Rp) ((fst Tk P.A).left z)) = s`. Generalize the expression as in `(fst Tk P.A).left z = w`. Take `rfl : w = (IsLocalRing.closedPoint k : PrimeSpectrum k)` from `Subsingleton.elim (α := PrimeSpectrum k) _ _`. Establish `: spMap (IsLocalRing.residue Rp) (IsLocalRing.closedPoint k : PrimeSpectrum k) = (IsLocalRing.closedPoint Rp : PrimeSpectrum Rp)` using `IsLocalRing.comap_closedPoint (IsLocalRing.residue Rp)`.

Rewrite using `[this]`. Conclude with `PrimeSpectrum.ext (Localization.AtPrime.comap_maximalIdeal (I := s.asIdeal))`. Establish `u₁ : IsUnit (sv P.A bp r z J)`. Rewrite using `[← sv_pullS P.A 1 hk bp (𝟙 _) z hJ']`. Conclude with `(AmpleSpan.mem_nonzeroLocus_iff_gs _ (𝟙 _) z (hJ'.mem (fun _ : Fin 1 => (snd Tk P.A).left) _)).1 hz`.

Establish `u₂ : IsUnit (gc (r ≫ (snd Tp P.A).left ≫ P.A.hom) z t)`. Rewrite using `[gc, AmpleSpan.isUnit_gs_iff _ z ⊤ trivial, e₂, hs]`. Conclude with `(basicOpen_eq_of_affine (R := CommRingCat.of R) t).ge ht`. Establish `u₃` using `u₂.mul u₁`. Establish `hm` using `hJ'.mem (fun _ : Fin 1 => (snd (baseOver (Sp R)) P.A).left) ρ`.

Establish `e₃` using `IsComb.gs (π := (fst (baseOver (Sp R)) P.A).left) ha ρ z _ hm`. Rewrite `e₃` using `[Fin.sum_univ_one]`. Establish `e₄` using `sval_pullTo (φ' := fun _ : Fin 1 => (snd (baseOver (Sp R)) P.A).left) σ (snd (baseOver (Sp R)) P.A).left (fun _ => Category.comp_id _) ρ z hJ'`. Rewrite `e₄` using `[e₁, hσ _ r z J hJ']`. Use `⟨ρ z, (AmpleSpan.mem_nonzeroLocus_iff_gs th ρ z hm).2 (isUnit_of_mul_isUnit_right ((congrArg IsUnit (e₃.symm.trans e₄)).mpr u₃)), ?_⟩` and prove the remaining obligations.

Use `show ((ρ ≫ (snd (baseOver (Sp R)) P.A).left) ≫ P.A.hom) z = s`. Rewrite using `[e₁, Category.assoc, e₂, hs]`.
-/
theorem exists_mem_nonzeroLocus_fibre : SecBaseChangeAnySt → ∀ (R : Type) [CommRing R] (P : PolAV (Sp R)) (th : LB.Sec (LPow P.A P.L 1 (baseOver (Sp R)))), IsSecBasis _ (fun _ : Fin 1 => th) → ∀ s : Sp R, ∃ y ∈ nonzeroLocus th, P.A.hom ((snd (baseOver (Sp R)) P.A).left y) = s := by
  intro hS R _ P th hth s
  obtain ⟨V, hV, b, hb⟩ := ThetaReal.exists_univBasis hS P 1 le_rfl s
  have hp : s.asIdeal.IsPrime := s.isPrime
  let Rp := Localization.AtPrime s.asIdeal
  let k := IsLocalRing.ResidueField Rp
  let Tp : Over (Sp R) := Over.mk (spMap (algebraMap R Rp))
  let Tk : Over (Sp R) := Over.mk (spMap (IsLocalRing.residue Rp) ≫ spMap (algebraMap R Rp))
  let hk : Tk ⟶ Tp := Over.homMk (spMap (IsLocalRing.residue Rp)) rfl
  let u : Tp ⟶ baseOver (Sp R) := Over.homMk Tp.hom (Category.comp_id _)
  have hr : Set.range (spMap (algebraMap R Rp)) ⊆ Set.range V.ι := by
    rintro _ ⟨q, rfl⟩
    refine (Scheme.Opens.range_ι V).ge ?_
    refine Specializes.mem_open ?_ V.isOpen hV
    refine (PrimeSpectrum.le_iff_specializes _ _).1 fun x hx => ?_
    by_contra hx'
    exact q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hx
      (IsLocalization.map_units Rp (⟨x, hx'⟩ : s.asIdeal.primeCompl)))
  let v : Tp ⟶ overRes (T := baseOver (Sp R)) V := Over.homMk (IsOpenImmersion.lift V.ι _ hr) (by
    show IsOpenImmersion.lift V.ι _ hr ≫ V.ι ≫ 𝟙 _ = spMap (algebraMap R Rp)
    rw [Category.comp_id, IsOpenImmersion.lift_fac])
  let i₀ : Fin (1 ^ P.g) := ⟨0, by simp⟩
  let bp : LB.Sec (LPow P.A P.L 1 Tp) := pullS P.A _ v (SecM.toSec P.A (b i₀))
  have haff : IsAffine Tk.left := inferInstanceAs (IsAffine (Spec _))
  have hnt : Nontrivial Γ(Tk.left, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom.domain_nontrivial
  obtain ⟨c, hc⟩ := hb Tk (hk ≫ v)
  have hne : (SecM.ofSec P.A (pullS P.A 1 hk bp) : SecM P.A P.L 1 Tk) ≠ 0 := fun h0 =>
    c.ne_zero i₀ ((hc i₀).trans ((pullM_comp P.A P.isLB _ hk v _).symm.trans h0))
  have hsm := P.isAb.smooth
  have hpr := P.isAb.proper
  have hred : IsReduced (Tk ⊗ P.A).left :=
    have : IsReduced Tk.left := inferInstanceAs (IsReduced (Spec (CommRingCat.of k)))
    have : Smooth (fst Tk P.A).left := inferInstanceAs (Smooth (pullback.fst Tk.hom P.A.hom))
    GlobalTheory.isReduced_of_smooth_of_isReduced (fst Tk P.A).left
  obtain ⟨z, hz⟩ : ∃ z, z ∈ nonzeroLocus (pullS P.A 1 hk bp) := by
    by_contra hn
    exact hne (Subtype.ext (funext fun j => eq_zero_of_basicOpen_eq_bot ((pullS P.A 1 hk bp).f j)
      (eq_bot_iff.2 fun y hy => (hn ⟨y, TopologicalSpace.Opens.mem_iSup.2 ⟨j, hy⟩⟩).elim)))
  have : CompactSpace P.A.left := QuasiCompact.compactSpace_of_compactSpace P.A.hom
  have : QuasiSeparatedSpace P.A.left := (quasiSeparated_iff_quasiSeparatedSpace P.A.hom).mp inferInstance
  have H : IsPullback (snd Tp P.A).left (fst Tp P.A).left P.A.hom (spMap (algebraMap R Rp)) :=
    (IsPullback.of_hasPullback Tp.hom P.A.hom).flip
  obtain ⟨t, ht, σ, hσ⟩ := exists_clear_sval s.asIdeal.primeCompl H P.isLB (fun _ : Fin 1 => 𝟙 P.A.left)
    (fun _ => (snd Tp P.A).left) (fun _ => Category.comp_id _) (fun _ => 1) bp
  obtain ⟨a, ha, -⟩ := hth (pullTo (φ' := fun _ : Fin 1 => (snd (baseOver (Sp R)) P.A).left) σ
    (snd (baseOver (Sp R)) P.A).left (fun _ => Category.comp_id _))
  choose J hJ using fun χ : (Tk ⊗ P.A).left ⟶ P.A.left => exists_chart P.isLB (χ z)
  have hJ' : Good P.L z J := hJ
  let r : (Tk ⊗ P.A).left ⟶ (Tp ⊗ P.A).left := 𝟙 _ ≫ (hk ▷ P.A).left
  let ρ : (Tk ⊗ P.A).left ⟶ (baseOver (Sp R) ⊗ P.A).left := r ≫ (u ▷ P.A).left
  have e₁ : ρ ≫ (snd (baseOver (Sp R)) P.A).left = r ≫ (snd Tp P.A).left := by
    rw [Category.assoc, whisker_snd_left]
  have e₂ : r ≫ (snd Tp P.A).left ≫ P.A.hom = (fst Tk P.A).left ≫ Tk.hom := by
    rw [Category.assoc, Category.id_comp, ← Category.assoc, whisker_snd_left, Over.w, Over.w]
  have hs : ((fst Tk P.A).left ≫ Tk.hom) z = s := by
    show spMap (algebraMap R Rp) (spMap (IsLocalRing.residue Rp) ((fst Tk P.A).left z)) = s
    generalize (fst Tk P.A).left z = w
    obtain rfl : w = (IsLocalRing.closedPoint k : PrimeSpectrum k) :=
      Subsingleton.elim (α := PrimeSpectrum k) _ _
    have : spMap (IsLocalRing.residue Rp) (IsLocalRing.closedPoint k : PrimeSpectrum k) =
        (IsLocalRing.closedPoint Rp : PrimeSpectrum Rp) := IsLocalRing.comap_closedPoint (IsLocalRing.residue Rp)
    rw [this]
    exact PrimeSpectrum.ext (Localization.AtPrime.comap_maximalIdeal (I := s.asIdeal))
  have u₁ : IsUnit (sv P.A bp r z J) := by
    rw [← sv_pullS P.A 1 hk bp (𝟙 _) z hJ']
    exact (AmpleSpan.mem_nonzeroLocus_iff_gs _ (𝟙 _) z (hJ'.mem (fun _ : Fin 1 => (snd Tk P.A).left) _)).1 hz
  have u₂ : IsUnit (gc (r ≫ (snd Tp P.A).left ≫ P.A.hom) z t) := by
    rw [gc, AmpleSpan.isUnit_gs_iff _ z ⊤ trivial, e₂, hs]
    exact (basicOpen_eq_of_affine (R := CommRingCat.of R) t).ge ht
  have u₃ := u₂.mul u₁
  have hm := hJ'.mem (fun _ : Fin 1 => (snd (baseOver (Sp R)) P.A).left) ρ
  have e₃ := IsComb.gs (π := (fst (baseOver (Sp R)) P.A).left) ha ρ z _ hm
  rw [Fin.sum_univ_one] at e₃
  have e₄ := sval_pullTo (φ' := fun _ : Fin 1 => (snd (baseOver (Sp R)) P.A).left) σ
    (snd (baseOver (Sp R)) P.A).left (fun _ => Category.comp_id _) ρ z hJ'
  rw [e₁, hσ _ r z J hJ'] at e₄
  refine ⟨ρ z, (AmpleSpan.mem_nonzeroLocus_iff_gs th ρ z hm).2
    (isUnit_of_mul_isUnit_right ((congrArg IsUnit (e₃.symm.trans e₄)).mpr u₃)), ?_⟩
  show ((ρ ≫ (snd (baseOver (Sp R)) P.A).left) ≫ P.A.hom) z = s
  rw [e₁, Category.assoc, e₂, hs]

end GlobalTheory.ThetaFibre
