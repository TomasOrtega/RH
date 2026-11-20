import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardEtaleLocalSection

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.EtaleSections

/- English proof (translation)
Take `⟨g, hg, hstd⟩` from `Algebra.IsEtaleAt.exists_isStandardEtale (R := S) Q`. Set `Bg` to `Localization.Away g`. Establish `hdisj : Disjoint (Submonoid.powers g : Set B) (Q : Set B)`. Rewrite using `[Set.disjoint_left]`. Introduce and unpack `_ ⟨n, rfl⟩ hn`.

Conclude with `hg (hQ.mem_of_pow_mem n hn)`. Establish `hQ' : (Q.map (algebraMap B Bg)).IsPrime` using `IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers g) Bg Q hQ hdisj`. Establish `hcomap : (Q.map (algebraMap B Bg)).comap (algebraMap B Bg) = Q` using `IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers g) Bg hQ hdisj`. Establish `hc : (Q.map (algebraMap B Bg)).comap (algebraMap S Bg) = Q.comap (algebraMap S B)`. Rewrite using `[IsScalarTower.algebraMap_eq S B Bg, ← Ideal.comap_comap, hcomap]`.

Take `⟨e, he, hem, ⟨ψ⟩⟩` from `GlobalTheory.CompanionTheory.EtaleSection.exists_section_standardEtale hA hL Bg (Q.map (algebraMap B Bg)) hQ' (hc ▸ hm)`. Conclude with `⟨e, he, hc ▸ hem, ⟨ψ.comp (IsScalarTower.toAlgHom S B Bg)⟩⟩`.
-/
theorem exists_algHom_away_of_etale {S : Type} [CommRing S] (hA : Aic S) (hL : Loc S)
    (B : Type) [CommRing B] [Algebra S B] [Algebra.Etale S B] (Q : Ideal B) [hQ : Q.IsPrime]
    (hm : (Q.comap (algebraMap S B)).IsMaximal) :
    ∃ e : S, IsIdempotentElem e ∧ e ∉ Q.comap (algebraMap S B) ∧
      Nonempty (B →ₐ[S] Localization.Away e) := by
  obtain ⟨g, hg, hstd⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := S) Q
  let Bg := Localization.Away g
  have hdisj : Disjoint (Submonoid.powers g : Set B) (Q : Set B) := by
    rw [Set.disjoint_left]
    rintro _ ⟨n, rfl⟩ hn
    exact hg (hQ.mem_of_pow_mem n hn)
  have hQ' : (Q.map (algebraMap B Bg)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers g) Bg Q hQ hdisj
  have hcomap : (Q.map (algebraMap B Bg)).comap (algebraMap B Bg) = Q :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers g) Bg hQ hdisj
  have hc : (Q.map (algebraMap B Bg)).comap (algebraMap S Bg) = Q.comap (algebraMap S B) := by
    rw [IsScalarTower.algebraMap_eq S B Bg, ← Ideal.comap_comap, hcomap]
  obtain ⟨e, he, hem, ⟨ψ⟩⟩ := GlobalTheory.CompanionTheory.EtaleSection.exists_section_standardEtale hA hL Bg (Q.map (algebraMap B Bg)) hQ' (hc ▸ hm)
  exact ⟨e, he, hc ▸ hem, ⟨ψ.comp (IsScalarTower.toAlgHom S B Bg)⟩⟩

/- English proof (translation)
Introduce `S _ hA hL Y f hE hS m hm`. Set `x : Spec (CommRingCat.of S)` to `⟨m, hm.isPrime⟩`. Take `⟨y, hy⟩` from `hS.surj x`. Take `⟨V, hV, hyV, -⟩` from `exists_isAffineOpen_mem_and_subset (U := ⊤) (x := y) trivial`. Take `⟨φ, hφ⟩` from `Spec.map_surjective (hV.fromSpec ≫ f)`.

Establish `hEt : Etale (Spec.map φ)` using `by rw [hφ]; infer_instance`. Establish `hφe : φ.hom.Etale` using `(HasRingHomProperty.Spec_iff (P := @Etale)).1 hEt`. Set `_ : Algebra S Γ(Y, V)` to `φ.hom.toAlgebra`. Establish `: Algebra.Etale S Γ(Y, V)` using `RingHom.etale_algebraMap.1 hφe`. Establish `hyr : y ∈ Set.range hV.fromSpec` using `by rw [hV.range_fromSpec]; exact hyV`.

Take `⟨z, hz⟩` from `hyr`. Establish `hcm : z.asIdeal.comap (algebraMap S Γ(Y, V)) = m`. Establish `h1 : (Spec.map φ) z = x`. Rewrite using `[hφ, Scheme.Hom.comp_apply, hz, hy]`. Conclude with `congrArg PrimeSpectrum.asIdeal h1`.

Establish `: z.asIdeal.IsPrime` using `z.2`. Take `⟨e, he, hem, ⟨ψ⟩⟩` from `exists_algHom_away_of_etale hA hL Γ(Y, V) z.asIdeal (by rw [hcm]; exact hm)`. Use `⟨e, he, hcm ▸ hem, Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ hV.fromSpec, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, ← hφ, ← Spec.map_comp]`. Use `congr 1`.

Use extensionality with `a`. Conclude with `ψ.commutes a`.
-/
theorem exists_secOn_of_etale_surjective : ∀ {S : Type} [CommRing S] , Aic S → Loc S →
    ∀ (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of S)), Etale f → Surjective f →
    ∀ m : Ideal S, m.IsMaximal → ∃ e : S, IsIdempotentElem e ∧ e ∉ m ∧ SecOn f e := by
  intro S _ hA hL Y f hE hS m hm
  let x : Spec (CommRingCat.of S) := ⟨m, hm.isPrime⟩
  obtain ⟨y, hy⟩ := hS.surj x
  obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := y) trivial
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (hV.fromSpec ≫ f)
  have hEt : Etale (Spec.map φ) := by rw [hφ]; infer_instance
  have hφe : φ.hom.Etale := (HasRingHomProperty.Spec_iff (P := @Etale)).1 hEt
  let _ : Algebra S Γ(Y, V) := φ.hom.toAlgebra
  have : Algebra.Etale S Γ(Y, V) := RingHom.etale_algebraMap.1 hφe
  have hyr : y ∈ Set.range hV.fromSpec := by rw [hV.range_fromSpec]; exact hyV
  obtain ⟨z, hz⟩ := hyr
  have hcm : z.asIdeal.comap (algebraMap S Γ(Y, V)) = m := by
    have h1 : (Spec.map φ) z = x := by
      rw [hφ, Scheme.Hom.comp_apply, hz, hy]
    exact congrArg PrimeSpectrum.asIdeal h1
  have : z.asIdeal.IsPrime := z.2
  obtain ⟨e, he, hem, ⟨ψ⟩⟩ := exists_algHom_away_of_etale hA hL Γ(Y, V) z.asIdeal (by rw [hcm]; exact hm)
  refine ⟨e, he, hcm ▸ hem, Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ hV.fromSpec, ?_⟩
  rw [Category.assoc, ← hφ, ← Spec.map_comp]
  congr 1
  ext a
  exact ψ.commutes a

end GlobalTheory.CompanionTheory.EtaleSections
