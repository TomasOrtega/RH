import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SiegelOneDescent.Descend2
open PositivityTheory.RgEis PositivityTheory.RgEis.So
open NumberField Matrix
open scoped NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.EisSo

/- English proof (translation)
Introduce `F E R _ _ _ _ _ _ _ _ _ _ A ε ν _ δ _ _ ι _ _ _ j hA hB _ hJ`. Establish `hcv : Continuous ν` using `hB.cont`. Establish `hval : Continuous fun x : cover A ν ι => (((j x).1 : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R)`. Establish `e : (fun x : cover A ν ι => (((j x).1 : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R)) = fun x => (x.1.1 : R) • ((((dg ι (Units.map A.i.toMonoidHom δ))⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * ((x.1.2 : Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[F]).map ν) * ((dg ι (Units.map A.i.toMonoidHom δ) …`. Use function extensionality and compare the values at `x`.

Rewrite using `[hJ x]`. Both sides reduce to the same expression. Rewrite using `[e]`. Establish `h1 : Continuous fun x : cover A ν ι => (x.1.1 : R)` using `Units.continuous_val.comp (continuous_fst.comp continuous_subtype_val)`. Establish `h2 : Continuous fun x : cover A ν ι => (x.1.2 : Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[F])` using `Units.continuous_val.comp (continuous_snd.comp continuous_subtype_val)`.

Conclude with `h1.smul ((continuous_const.matrix_mul (h2.matrix_map hcv)).matrix_mul continuous_const)`. Establish `hjGL : Continuous fun x : cover A ν ι => ((j x).1 : GL (ι ⊕ ι) R)`. Use `Units.continuous_iff.2 ⟨hval, ?_⟩` and prove the remaining obligations. Establish `e : (fun x : cover A ν ι => (((((j x).1 : GL (ι ⊕ ι) R))⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R)) = (fun x : cover A ν ι => (((j x).1 : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R)) ∘ fun x => x⁻¹`. Use function extensionality and compare the values at `x`.

Simplify using `[map_inv]`. Rewrite using `[e]`. Conclude with `hval.comp continuous_inv`. Establish `hum : ∀ {S T : Type} [CommRing S] [CommRing T] [TopologicalSpace S] [TopologicalSpace T] [IsTopologicalRing S] (φ : S →+* T), Continuous φ → Continuous (Units.map φ.toMonoidHom)`. Introduce `S T _ _ _ _ _ φ hφ`.

Conclude with `Units.continuous_iff.2 ⟨hφ.comp Units.continuous_val, hφ.comp (Units.continuous_val.comp continuous_inv)⟩`. Establish `hdet : Continuous (Matrix.GeneralLinearGroup.det : GL (ι ⊕ ι) 𝔸[F] → 𝔸[F]ˣ)` using `Units.continuous_iff.2 ⟨Units.continuous_val.matrix_det, (Units.continuous_val.comp continuous_inv).matrix_det⟩`. Use `haveI : SecondCountableTopology Rᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology`. Use `haveI : SecondCountableTopology (Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[F]) := inferInstanceAs (SecondCountableTopology (ι ⊕ ι → ι ⊕ ι → 𝔸[F]))`. Use `haveI : SecondCountableTopology (Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[F])ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology`.

Use `haveI : SecondCountableTopology Rˣ := Units.isEmbedding_embedProduct.secondCountableTopology`. Use `haveI : SecondCountableTopology (GL (ι ⊕ ι) 𝔸[F]) := Units.isEmbedding_embedProduct.secondCountableTopology`. Use `haveI : LocallyCompactSpace Rˣ := Units.isClosedEmbedding_embedProduct.locallyCompactSpace`. Use `haveI : LocallyCompactSpace (GL (ι ⊕ ι) 𝔸[F]) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace`. Establish `hf : Continuous fun x : Rˣ × GL (ι ⊕ ι) 𝔸[F] => x.1 * Units.map A.σ.toMonoidHom x.1 * Units.map ν.toMonoidHom (Matrix.GeneralLinearGroup.det x.2)` using `(continuous_fst.mul ((hum A.σ hA.σcont).comp continuous_fst)).mul ((hum ν hcv).comp (hdet.comp continuous_snd))`.

Establish `hcl : IsClosed (cover A ν ι : Set (Rˣ × GL (ι ⊕ ι) 𝔸[F]))`. Establish `e : (cover A ν ι : Set (Rˣ × GL (ι ⊕ ι) 𝔸[F])) = (fun x : Rˣ × GL (ι ⊕ ι) 𝔸[F] => x.1 * Units.map A.σ.toMonoidHom x.1 * Units.map ν.toMonoidHom (Matrix.GeneralLinearGroup.det x.2)) ⁻¹' {1}` using `Set.ext fun x => Iff.rfl`. Rewrite using `[e]`. Conclude with `isClosed_singleton.preimage hf`. Use `haveI : SecondCountableTopology (Rˣ × GL (ι ⊕ ι) 𝔸[F]) := inferInstance`.

Conclude with `⟨hjGL.subtype_mk _, inferInstance, hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace, Topology.IsEmbedding.subtypeVal.secondCountableTopology⟩`.
-/
theorem jtop : JTop := by
  intro F E R _ _ _ _ _ _ _ _ _ _ A ε ν _ δ _ _ ι _ _ _ j hA hB _ hJ
  have hcv : Continuous ν := hB.cont

  have hval : Continuous fun x : cover A ν ι => (((j x).1 : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) := by
    have e : (fun x : cover A ν ι => (((j x).1 : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R)) = fun x =>
        (x.1.1 : R) • ((((dg ι (Units.map A.i.toMonoidHom δ))⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) *
          ((x.1.2 : Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[F]).map ν) *
          ((dg ι (Units.map A.i.toMonoidHom δ) : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R)) := by
      funext x; rw [hJ x]; rfl
    rw [e]
    have h1 : Continuous fun x : cover A ν ι => (x.1.1 : R) :=
      Units.continuous_val.comp (continuous_fst.comp continuous_subtype_val)
    have h2 : Continuous fun x : cover A ν ι => (x.1.2 : Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[F]) :=
      Units.continuous_val.comp (continuous_snd.comp continuous_subtype_val)
    exact h1.smul ((continuous_const.matrix_mul (h2.matrix_map hcv)).matrix_mul continuous_const)
  have hjGL : Continuous fun x : cover A ν ι => ((j x).1 : GL (ι ⊕ ι) R) := by
    refine Units.continuous_iff.2 ⟨hval, ?_⟩
    have e : (fun x : cover A ν ι => (((((j x).1 : GL (ι ⊕ ι) R))⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R)) =
        (fun x : cover A ν ι => (((j x).1 : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R)) ∘ fun x => x⁻¹ := by
      funext x; simp [map_inv]
    rw [e]; exact hval.comp continuous_inv
  have hum : ∀ {S T : Type} [CommRing S] [CommRing T] [TopologicalSpace S] [TopologicalSpace T]
      [IsTopologicalRing S] (φ : S →+* T), Continuous φ → Continuous (Units.map φ.toMonoidHom) := by
    intro S T _ _ _ _ _ φ hφ
    exact Units.continuous_iff.2 ⟨hφ.comp Units.continuous_val, hφ.comp (Units.continuous_val.comp continuous_inv)⟩
  have hdet : Continuous (Matrix.GeneralLinearGroup.det : GL (ι ⊕ ι) 𝔸[F] → 𝔸[F]ˣ) :=
    Units.continuous_iff.2 ⟨Units.continuous_val.matrix_det, (Units.continuous_val.comp continuous_inv).matrix_det⟩
  haveI : SecondCountableTopology Rᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  haveI : SecondCountableTopology (Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[F]) := inferInstanceAs (SecondCountableTopology (ι ⊕ ι → ι ⊕ ι → 𝔸[F]))
  haveI : SecondCountableTopology (Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[F])ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  haveI : SecondCountableTopology Rˣ := Units.isEmbedding_embedProduct.secondCountableTopology
  haveI : SecondCountableTopology (GL (ι ⊕ ι) 𝔸[F]) := Units.isEmbedding_embedProduct.secondCountableTopology
  haveI : LocallyCompactSpace Rˣ := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : LocallyCompactSpace (GL (ι ⊕ ι) 𝔸[F]) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  have hf : Continuous fun x : Rˣ × GL (ι ⊕ ι) 𝔸[F] =>
      x.1 * Units.map A.σ.toMonoidHom x.1 * Units.map ν.toMonoidHom (Matrix.GeneralLinearGroup.det x.2) :=
    (continuous_fst.mul ((hum A.σ hA.σcont).comp continuous_fst)).mul ((hum ν hcv).comp (hdet.comp continuous_snd))
  have hcl : IsClosed (cover A ν ι : Set (Rˣ × GL (ι ⊕ ι) 𝔸[F])) := by
    have e : (cover A ν ι : Set (Rˣ × GL (ι ⊕ ι) 𝔸[F])) = (fun x : Rˣ × GL (ι ⊕ ι) 𝔸[F] =>
        x.1 * Units.map A.σ.toMonoidHom x.1 * Units.map ν.toMonoidHom (Matrix.GeneralLinearGroup.det x.2)) ⁻¹' {1} :=
      Set.ext fun x => Iff.rfl
    rw [e]; exact isClosed_singleton.preimage hf
  haveI : SecondCountableTopology (Rˣ × GL (ι ⊕ ι) 𝔸[F]) := inferInstance
  exact ⟨hjGL.subtype_mk _, inferInstance, hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace,
    Topology.IsEmbedding.subtypeVal.secondCountableTopology⟩

end GlobalTheory.CompanionTheory.EisSo
