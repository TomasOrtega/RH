import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.SelmerRankBoundLaurent
open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open NumberField IsDedekindDomain GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange
open scoped TensorProduct

/- English proof (translation)
By extensionality, compare the relevant components. Establish an intermediate fact. Apply the first step, then apply the next step to every resulting obligation. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
private theorem galOf_one' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {A B : Type*} [CommRing A] [Algebra F A] [CommRing B] [Algebra E B] (e : E ⊗[F] A ≃ₐ[E] B) :
    galOf e (1 : E ≃ₐ[F] E) = RingHom.id _ := by
  ext x
  have h : Algebra.TensorProduct.map (((1 : E ≃ₐ[F] E) : E →ₐ[F] E)) (AlgHom.id F A) = AlgHom.id F _ := by
    ext <;> simp
  simp only [galOf, RingHom.comp_apply, h]
  simp

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
private theorem infMap_self (F : Type) [Field F] [NumberField F] : infMap F F = RingHom.id _ := by
  have hd := InfiniteAdeleRing.denseRange_algebraMap F
  have h1 : Continuous (infMap F F) := InfinitePlace.continuous_infiniteAdeleRingMap
  have := hd.equalizer h1 continuous_id (funext fun k => by
    simpa using InfinitePlace.infiniteAdeleRingMap_algebraMap (K := F) (L := F) k)
  exact RingHom.ext fun x => congrFun this x

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem incFin_bij (F : Type) [Field F] [NumberField F] (v : Pl F) : Function.Bijective (incFin F v) := by
  have h : ∀ x, incFin F v x = tensorEquiv' F v ((1 : F) ⊗ₜ[F] x) := by
    intro x
    rw [tensorEquiv'_tmul, map_one, one_mul]
    rfl
  have hb : Function.Bijective (fun x : v.adicCompletion F => (1 : F) ⊗ₜ[F] x) :=
    (TensorProduct.lid F (v.adicCompletion F)).symm.bijective
  have : (incFin F v : _ → _) = tensorEquiv' F v ∘ (fun x : v.adicCompletion F => (1 : F) ⊗ₜ[F] x) := funext h
  rw [this]
  exact (tensorEquiv' F v).bijective.comp hb

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations.
-/
theorem UpperTheory.baseChange_trivial_extension :
    Triv := by
  intro F _ _
  refine ⟨galOf_one' _, infMap_self F, fun v => ⟨galOf_one' _, incFin_bij F v⟩⟩
