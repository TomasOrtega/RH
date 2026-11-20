import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasic

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

/- English proof (translation)
Apply `HasRingHomProperty.Spec_iff.mpr` to reduce the goal to its premises. Conclude with `RingHom.etale_algebraMap.mpr ‹_›`.
-/
private lemma etale_specMap (D E : Type) [CommRing D] [CommRing E] [Algebra D E] [Algebra.Etale D E] :
    Etale (Spec.map (CommRingCat.ofHom (algebraMap D E))) := by
  apply HasRingHomProperty.Spec_iff.mpr
  exact RingHom.etale_algebraMap.mpr ‹_›

/- English proof (translation)
Introduce `hI D E _ _ _ _ hpts`. Set `φ : CommRingCat.of D ⟶ CommRingCat.of E` to `CommRingCat.ofHom (algebraMap D E)`. Establish `: Etale (Spec.map φ)` using `etale_specMap D E`. Establish `hiso : IsIso (Spec.map φ)`. Use `hI (Spec.map φ) ?_` and prove the remaining obligations.

Introduce `Ω _ _ z`. Take `⟨y, hy, hyu⟩` from `hpts Ω (Spec.preimage z).hom`. Use `⟨Spec.map (CommRingCat.ofHom y), ?_, ?_⟩` and prove the remaining obligations. Use `show Spec.map (CommRingCat.ofHom y) ≫ Spec.map φ = z`. Rewrite using `[← Spec.map_comp]`.

Use `conv_rhs => rw [← Spec.map_preimage z]`. Use `congr 1`. Use extensionality with `d`. Conclude with `congrArg (fun f : D →+* Ω => f d) hy`. Introduce `w hw`.

Rewrite using `[← Spec.map_preimage w]`. Use `congr 1`. Use extensionality with `e`. Establish `hx : (Spec.preimage w).hom.comp (algebraMap D E) = (Spec.preimage z).hom`. Establish `h2 : Spec.map (φ ≫ Spec.preimage w) = Spec.map (Spec.preimage z)`.

Rewrite using `[Spec.map_comp, Spec.map_preimage, Spec.map_preimage]`. Conclude with `hw`. Establish `h3` using `Spec.map_injective h2`. Use extensionality with `d`. Conclude with `congrArg (fun f => (CommRingCat.Hom.hom f) d) h3`.

Conclude with `congrArg (fun f : E →+* Ω => f e) (hyu _ hx)`. Establish `hφ : IsIso φ`. Use `⟨⟨Spec.preimage (inv (Spec.map φ)), ?_, ?_⟩⟩` and prove the remaining obligations. Apply `Spec.map_injective` to reduce the goal to its premises. Rewrite using `[Spec.map_comp, Spec.map_preimage, Spec.map_id, IsIso.inv_hom_id]`.

Apply `Spec.map_injective` to reduce the goal to its premises. Rewrite using `[Spec.map_comp, Spec.map_preimage, Spec.map_id, IsIso.hom_inv_id]`. Conclude with `ConcreteCategory.bijective_of_isIso φ`.
-/
theorem UpperTheory.Gal.G3.pAlgIsoPts :
    IsoPts → AlgIsoPts := by
  intro hI D E _ _ _ _ hpts
  let φ : CommRingCat.of D ⟶ CommRingCat.of E := CommRingCat.ofHom (algebraMap D E)
  have : Etale (Spec.map φ) := etale_specMap D E
  have hiso : IsIso (Spec.map φ) := by
    refine hI (Spec.map φ) ?_
    intro Ω _ _ z
    obtain ⟨y, hy, hyu⟩ := hpts Ω (Spec.preimage z).hom
    refine ⟨Spec.map (CommRingCat.ofHom y), ?_, ?_⟩
    · show Spec.map (CommRingCat.ofHom y) ≫ Spec.map φ = z
      rw [← Spec.map_comp]
      conv_rhs => rw [← Spec.map_preimage z]
      congr 1
      ext d
      exact congrArg (fun f : D →+* Ω => f d) hy
    · intro w hw
      rw [← Spec.map_preimage w]
      congr 1
      ext e
      have hx : (Spec.preimage w).hom.comp (algebraMap D E) = (Spec.preimage z).hom := by
        have h2 : Spec.map (φ ≫ Spec.preimage w) = Spec.map (Spec.preimage z) := by
          rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage]
          exact hw
        have h3 := Spec.map_injective h2
        ext d
        exact congrArg (fun f => (CommRingCat.Hom.hom f) d) h3
      exact congrArg (fun f : E →+* Ω => f e) (hyu _ hx)
  have hφ : IsIso φ := by
    refine ⟨⟨Spec.preimage (inv (Spec.map φ)), ?_, ?_⟩⟩
    · apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_preimage, Spec.map_id, IsIso.inv_hom_id]
    · apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_preimage, Spec.map_id, IsIso.hom_inv_id]
  exact ConcreteCategory.bijective_of_isIso φ
