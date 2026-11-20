import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ImportsRest
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletedLatticeStabilizerCompactOpenStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpqLocallyCompactGroup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Imports
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmDataIsCMExtAndGramIsHermND
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueInfEmb
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryGroupRealPointsEquivPiIndefiniteUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatCFullLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicSplit
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.VolExists

/- English proof (translation)
Set `j : H →* G` to `(e.symm.toMulEquiv.toMonoidHom).comp (MonoidHom.inr _ _)`. Establish `hj : Topology.IsEmbedding j` using `e.symm.toHomeomorph.isEmbedding.comp (isEmbedding_prodMkRight (1 : ∀ i, U i))`. Use `haveI : IsTopologicalGroup H := hj.isInducing.topologicalGroup j`. Use `haveI : SecondCountableTopology H := hj.secondCountableTopology`. Use `haveI : T2Space H := hj.t2Space`.

Use `haveI : LocallyCompactSpace H := hKc.locallyCompactSpace_of_mem_nhds_of_group (hKo.mem_nhds K.one_mem)`. Use `letI : MeasurableSpace H := borel H`. Use `haveI : BorelSpace H := ⟨rfl⟩`. Set `K0 : TopologicalSpace.PositiveCompacts H` to `⟨⟨K, hKc⟩, by show (interior (K : Set H)).Nonempty`. Rewrite using `[hKo.interior_eq]`.

Conclude with `⟨1, K.one_mem⟩⟩`. Set `m : Measure ((∀ i, U i) × H)` to `(Measure.pi ν).prod (Measure.haarMeasure K0)`. Use `haveI : m.IsHaarMeasure := inferInstanceAs (((Measure.pi ν).prod (Measure.haarMeasure K0)).IsHaarMeasure)`. Use `⟨m.map e.symm, e.symm.isHaarMeasure_map m, fun B hB => ?_⟩` and prove the remaining obligations. Establish `hme : MeasurableEmbedding e.symm` using `e.symm.toHomeomorph.measurableEmbedding`.

Rewrite using `[hme.map_apply]`. Establish `: e.symm ⁻¹' {h | (e h).2 ∈ K ∧ ∀ i, (e h).1 i ∈ B i} = (Set.univ.pi B) ×ˢ (K : Set H)`. Use extensionality with `x`. Simplify using `[and_comm]`. Rewrite using `[this, Measure.prod_prod, Measure.pi_pi]`.

Establish `h1 : Measure.haarMeasure K0 (K : Set H) = 1` using `Measure.haarMeasure_self`. Rewrite using `[h1, mul_one]`.
-/
theorem exists_haar_prod {G H I : Type} [Fintype I] {U : I → Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] [T2Space G]
    [Group H] [TopologicalSpace H] [∀ i, Group (U i)] [∀ i, TopologicalSpace (U i)]
    [∀ i, IsTopologicalGroup (U i)] [∀ i, MeasurableSpace (U i)] [∀ i, BorelSpace (U i)]
    [∀ i, SecondCountableTopology (U i)] [∀ i, LocallyCompactSpace (U i)]
    (ν : ∀ i, Measure (U i)) [∀ i, (ν i).IsHaarMeasure] (e : G ≃ₜ* (∀ i, U i) × H) (K : Subgroup H)
    (hKo : IsOpen (K : Set H)) (hKc : IsCompact (K : Set H)) :
    ∃ μ : Measure G, μ.IsHaarMeasure ∧ ∀ B : ∀ i, Set (U i), (∀ i, MeasurableSet (B i)) →
      μ {h | (e h).2 ∈ K ∧ ∀ i, (e h).1 i ∈ B i} = ∏ i, ν i (B i) := by
  let j : H →* G := (e.symm.toMulEquiv.toMonoidHom).comp (MonoidHom.inr _ _)
  have hj : Topology.IsEmbedding j :=
    e.symm.toHomeomorph.isEmbedding.comp (isEmbedding_prodMkRight (1 : ∀ i, U i))
  haveI : IsTopologicalGroup H := hj.isInducing.topologicalGroup j
  haveI : SecondCountableTopology H := hj.secondCountableTopology
  haveI : T2Space H := hj.t2Space
  haveI : LocallyCompactSpace H :=
    hKc.locallyCompactSpace_of_mem_nhds_of_group (hKo.mem_nhds K.one_mem)
  letI : MeasurableSpace H := borel H
  haveI : BorelSpace H := ⟨rfl⟩
  let K0 : TopologicalSpace.PositiveCompacts H :=
    ⟨⟨K, hKc⟩, by
      show (interior (K : Set H)).Nonempty
      rw [hKo.interior_eq]; exact ⟨1, K.one_mem⟩⟩
  let m : Measure ((∀ i, U i) × H) := (Measure.pi ν).prod (Measure.haarMeasure K0)
  haveI : m.IsHaarMeasure := inferInstanceAs (((Measure.pi ν).prod (Measure.haarMeasure K0)).IsHaarMeasure)
  refine ⟨m.map e.symm, e.symm.isHaarMeasure_map m, fun B hB => ?_⟩
  have hme : MeasurableEmbedding e.symm := e.symm.toHomeomorph.measurableEmbedding
  rw [hme.map_apply]
  have : e.symm ⁻¹' {h | (e h).2 ∈ K ∧ ∀ i, (e h).1 i ∈ B i} = (Set.univ.pi B) ×ˢ (K : Set H) := by
    ext x
    simp [and_comm]
  rw [this, Measure.prod_prod, Measure.pi_pi]
  have h1 : Measure.haarMeasure K0 (K : Set H) = 1 := Measure.haarMeasure_self
  rw [h1, mul_one]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mat_mul {P Q : ℕ} (a b : UpqT P Q) : UpqT.mat (a * b) = UpqT.mat a * UpqT.mat b := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mat_one {P Q : ℕ} : UpqT.mat (1 : UpqT P Q) = 1 := rfl

/- English proof (translation)
Set `g : GL (Fin P ⊕ Fin Q) ℂ` to `⟨A' * B, A * B', by rw [Matrix.mul_assoc, ← Matrix.mul_assoc B, h2, Matrix.one_mul, h3], by rw [Matrix.mul_assoc, ← Matrix.mul_assoc B', h4, Matrix.one_mul, h1]⟩`. Establish `hg : g ∈ Formalism.UG.Upq P Q` using `by show (A' * B)ᴴ * Formalism.UG.Jpq P Q * (A' * B) = Formalism.UG.Jpq P Q`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = (A * B)ᴴ * Formalism.UG.Jpq P Q * (A * B) := by`.

Rewrite using `[← h]`. Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = Formalism.UG.Jpq P Q := by rw [h1]; simp`. Use `⟨(⟨g, hg⟩ : Formalism.UG.Upq P Q), ?_⟩` and prove the remaining obligations. Use `show A' * B * A = A'`.

Rewrite using `[Matrix.mul_assoc, h2, Matrix.mul_one]`.
-/
theorem exists_upq_mul {P Q M : ℕ} (A A' : Matrix (Fin P ⊕ Fin Q) (Fin M) ℂ)
    (B B' : Matrix (Fin M) (Fin P ⊕ Fin Q) ℂ) (h1 : A * B = 1) (h2 : B * A = 1) (h3 : A' * B' = 1)
    (h4 : B' * A' = 1) (h : Aᴴ * Formalism.UG.Jpq P Q * A = A'ᴴ * Formalism.UG.Jpq P Q * A') :
    ∃ u : UpqT P Q, UpqT.mat u * A = A' := by
  let g : GL (Fin P ⊕ Fin Q) ℂ := ⟨A' * B, A * B',
    by rw [Matrix.mul_assoc, ← Matrix.mul_assoc B, h2, Matrix.one_mul, h3],
    by rw [Matrix.mul_assoc, ← Matrix.mul_assoc B', h4, Matrix.one_mul, h1]⟩
  have hg : g ∈ Formalism.UG.Upq P Q := by
    show (A' * B)ᴴ * Formalism.UG.Jpq P Q * (A' * B) = Formalism.UG.Jpq P Q
    calc (A' * B)ᴴ * Formalism.UG.Jpq P Q * (A' * B) = Bᴴ * (A'ᴴ * Formalism.UG.Jpq P Q * A') * B := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (A * B)ᴴ * Formalism.UG.Jpq P Q * (A * B) := by
          rw [← h]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Formalism.UG.Jpq P Q := by rw [h1]; simp
  refine ⟨(⟨g, hg⟩ : Formalism.UG.Upq P Q), ?_⟩
  show A' * B * A = A'
  rw [Matrix.mul_assoc, h2, Matrix.mul_one]

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ cm I _ τ cd W hτ hW`. Take `⟨hcm, -⟩` from `GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND F E cm`. Establish `hθ` using `GlobalTheory.Mem.VolEmb.existsUnique_infEmb F E cm.sig hcm`. Use `choose θ hθ1 hθ2 using fun i => hθ (τ i)`. Establish `hA` using `fun i => GlobalTheory.Mem.SignatureFactor.exists_factor _ _ _ _ (hW (τ i))`.

Use `choose A hA1 using fun i => (hA i).2.1`. Take `⟨e1, he1⟩` from `GlobalTheory.T.unitaryGroup_realPoints_equiv_pi_indefiniteUnitary F E cm.sig W.rank W.gram I τ θ (fun ρ => (W.sig (τ ρ)).1) (fun ρ => (W.sig (τ ρ)).2) A hcm hτ hθ1 (fun i => hW (τ i)) hA1`. Take `⟨e0, he0⟩` from `GlobalTheory.Mem.VolSplit.exists_adelic_split F E cm.sig W.rank W.gram`. Take `⟨L, hL, hLfg, hLsp⟩` from `GlobalTheory.Mem.Vol.latC_full_lattice E W`. Take `⟨K, hK, hKo, hKc⟩` from `GlobalTheory.T.completedLattice_stabilizer_compact_open F E cm.sig W.rank W.gram L hLfg hLsp`.

Take `⟨-, hsc, ht2⟩` from `GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary F E cm.sig W.rank W.gram`. Use `haveI : IsTopologicalGroup (HA (AF F) cm.sig W.gram) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _`. Use `haveI : BorelSpace (HA (AF F) cm.sig W.gram) := ⟨rfl⟩`. Use `haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).1`. Use `haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.1`.

Use `haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.1`. Use `haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.2.1`. Establish `hinj` using `fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.2.2.injective`. Use `haveI := cd.haar`. Set `e : HA (AF F) cm.sig W.gram ≃ₜ* (∀ i, UpqT (W.sig (τ i)).1 (W.sig (τ i)).2) × HA (Af F) cm.sig W.gram` to `e0.trans { e1.toMulEquiv.prodCongr (MulEquiv.refl _) with continuous_toFun := e1.continuous_toFun.prodMap continuous_id continuous_invFun := e1.continuous_invFun.prodMap continuous_id }`.

Establish `hee : ∀ h, e h = (e1 (e0 h).1, (e0 h).2)` using `fun h => rfl`. Take `⟨μ, hμ, hμB⟩` from `exists_haar_prod (fun i => cd.cd (W.sig (τ i)).1 (W.sig (τ i)).2) e K hKo hKc`. Use `⟨μ, hμ, ⟨θ, hθ1⟩, fun θ' hθ' => ?_⟩` and prove the remaining obligations. Take `rfl : θ' = θ` from `funext fun i => hθ2 i _ (hθ' i)`. Use `⟨⟨A, hA1⟩, fun A' hA' B hB => ?_⟩` and prove the remaining obligations.

Establish `hu : ∀ i, ∃ u : UpqT (W.sig (τ i)).1 (W.sig (τ i)).2, UpqT.mat u * A i = A' i`. Introduce `i`. Take `⟨C, h1, h2⟩` from `(hA i).2.2 _ (hA1 i)`. Take `⟨C', h3, h4⟩` from `(hA i).2.2 _ (hA' i)`. Conclude with `exists_upq_mul _ _ C C' h1 h2 h3 h4 ((hA1 i).trans (hA' i).symm)`.

Use `choose u hu using hu`. Establish `key` using `hμB (fun i => (fun g => u i * g) ⁻¹' ((fun g => g * (u i)⁻¹) ⁻¹' B i)) (fun i => measurable_const_mul _ (measurable_mul_const _ (hB i)))`. Establish `hcj : ∀ i, cd.cd (W.sig (τ i)).1 (W.sig (τ i)).2 ((fun g => u i * g) ⁻¹' ((fun g => g * (u i)⁻¹) ⁻¹' B i)) = cd.cd (W.sig (τ i)).1 (W.sig (τ i)).2 (B i)`. Introduce `i`. Use `haveI := GlobalTheory.UpqHaarRight.isMulRightInvariant _ _ _ (cd.haar (W.sig (τ i)).1 (W.sig (τ i)).2)`.

Rewrite using `[measure_preimage_mul, measure_preimage_mul_right]`. Rewrite `key` using `[Finset.prod_congr rfl (fun i _ => hcj i)]`. Rewrite using `[← key]`. Use `congr 1`. Use extensionality with `h`.

Simplify using `only [Set.mem_setOf_eq, hee, Set.mem_preimage]`. Rewrite using `[hK, (he0 h).1, hL]`. Use `and_congr_right fun _ => forall_congr' fun i => ?_` and prove the remaining obligations. Establish `h1 : UpqT.mat (e1 (e0 h).1 i) * A i = A i * infMat cm.sig W.gram (θ' i) h`. Rewrite using `[he1, (he0 h).2]`.

Both sides reduce to the same expression. Establish `h2 : UpqT.mat (u i * e1 (e0 h).1 i * (u i)⁻¹) * A' i = A' i * infMat cm.sig W.gram (θ' i) h`. Establish `h3 : UpqT.mat (u i)⁻¹ * A' i = A i`. Rewrite using `[← hu i, ← Matrix.mul_assoc, ← mat_mul, inv_mul_cancel, mat_one, Matrix.one_mul]`. Rewrite using `[mat_mul, mat_mul, Matrix.mul_assoc, h3, Matrix.mul_assoc, h1, ← Matrix.mul_assoc, hu i]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨b, hb, hbe⟩`. Take `⟨C', h3, -⟩` from `(hA i).2.2 _ (hA' i)`. Establish `: b = u i * e1 (e0 h).1 i * (u i)⁻¹`. Apply `hinj` to reduce the goal to its premises.

Establish `h5` using `congrArg (· * C') (hbe.trans h2.symm)`. Simplify `h5` using `only [Matrix.mul_assoc, h3, Matrix.mul_one]`. Conclude with `this ▸ hb`. Introduce `hb`. Conclude with `⟨_, hb, h2⟩`.
-/
theorem exists_isVolMeasF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (I : Type) [Fintype I] (τ : I → (E →+* ℂ)) (cd : CDHaar) (W : HSpace E), IsCMFam τ → W.SigOK → ∃ μ, IsVolMeasF cm τ cd W (fun ρ => (W.sig (τ ρ)).1) (fun ρ => (W.sig (τ ρ)).2) μ := by
  intro F E _ _ _ _ _ _ cm I _ τ cd W hτ hW
  obtain ⟨hcm, -⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND F E cm
  have hθ := GlobalTheory.Mem.VolEmb.existsUnique_infEmb F E cm.sig hcm
  choose θ hθ1 hθ2 using fun i => hθ (τ i)
  have hA := fun i => GlobalTheory.Mem.SignatureFactor.exists_factor _ _ _ _ (hW (τ i))
  choose A hA1 using fun i => (hA i).2.1
  obtain ⟨e1, he1⟩ := GlobalTheory.T.unitaryGroup_realPoints_equiv_pi_indefiniteUnitary F E cm.sig W.rank W.gram I τ θ (fun ρ => (W.sig (τ ρ)).1)
    (fun ρ => (W.sig (τ ρ)).2) A hcm hτ hθ1 (fun i => hW (τ i)) hA1
  obtain ⟨e0, he0⟩ := GlobalTheory.Mem.VolSplit.exists_adelic_split F E cm.sig W.rank W.gram
  obtain ⟨L, hL, hLfg, hLsp⟩ := GlobalTheory.Mem.Vol.latC_full_lattice E W
  obtain ⟨K, hK, hKo, hKc⟩ := GlobalTheory.T.completedLattice_stabilizer_compact_open F E cm.sig W.rank W.gram L hLfg hLsp
  obtain ⟨-, hsc, ht2⟩ := GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary F E cm.sig W.rank W.gram
  haveI : IsTopologicalGroup (HA (AF F) cm.sig W.gram) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : BorelSpace (HA (AF F) cm.sig W.gram) := ⟨rfl⟩
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.2.1
  have hinj := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.2.2.injective
  haveI := cd.haar
  let e : HA (AF F) cm.sig W.gram ≃ₜ*
      (∀ i, UpqT (W.sig (τ i)).1 (W.sig (τ i)).2) × HA (Af F) cm.sig W.gram :=
    e0.trans
      { e1.toMulEquiv.prodCongr (MulEquiv.refl _) with
        continuous_toFun := e1.continuous_toFun.prodMap continuous_id
        continuous_invFun := e1.continuous_invFun.prodMap continuous_id }
  have hee : ∀ h, e h = (e1 (e0 h).1, (e0 h).2) := fun h => rfl
  obtain ⟨μ, hμ, hμB⟩ := exists_haar_prod (fun i => cd.cd (W.sig (τ i)).1 (W.sig (τ i)).2) e K hKo hKc
  refine ⟨μ, hμ, ⟨θ, hθ1⟩, fun θ' hθ' => ?_⟩
  obtain rfl : θ' = θ := funext fun i => hθ2 i _ (hθ' i)
  refine ⟨⟨A, hA1⟩, fun A' hA' B hB => ?_⟩
  have hu : ∀ i, ∃ u : UpqT (W.sig (τ i)).1 (W.sig (τ i)).2, UpqT.mat u * A i = A' i := by
    intro i
    obtain ⟨C, h1, h2⟩ := (hA i).2.2 _ (hA1 i)
    obtain ⟨C', h3, h4⟩ := (hA i).2.2 _ (hA' i)
    exact exists_upq_mul _ _ C C' h1 h2 h3 h4 ((hA1 i).trans (hA' i).symm)
  choose u hu using hu
  have key := hμB (fun i => (fun g => u i * g) ⁻¹' ((fun g => g * (u i)⁻¹) ⁻¹' B i))
    (fun i => measurable_const_mul _ (measurable_mul_const _ (hB i)))
  have hcj : ∀ i, cd.cd (W.sig (τ i)).1 (W.sig (τ i)).2
      ((fun g => u i * g) ⁻¹' ((fun g => g * (u i)⁻¹) ⁻¹' B i)) =
      cd.cd (W.sig (τ i)).1 (W.sig (τ i)).2 (B i) := by
    intro i
    haveI := GlobalTheory.UpqHaarRight.isMulRightInvariant _ _ _ (cd.haar (W.sig (τ i)).1 (W.sig (τ i)).2)
    rw [measure_preimage_mul, measure_preimage_mul_right]
  rw [Finset.prod_congr rfl (fun i _ => hcj i)] at key
  rw [← key]
  congr 1
  ext h
  simp only [Set.mem_setOf_eq, hee, Set.mem_preimage]
  rw [hK, (he0 h).1, hL]
  refine and_congr_right fun _ => forall_congr' fun i => ?_
  have h1 : UpqT.mat (e1 (e0 h).1 i) * A i = A i * infMat cm.sig W.gram (θ' i) h := by
    rw [he1, (he0 h).2]; rfl
  have h2 : UpqT.mat (u i * e1 (e0 h).1 i * (u i)⁻¹) * A' i = A' i * infMat cm.sig W.gram (θ' i) h := by
    have h3 : UpqT.mat (u i)⁻¹ * A' i = A i := by
      rw [← hu i, ← Matrix.mul_assoc, ← mat_mul, inv_mul_cancel, mat_one, Matrix.one_mul]
    rw [mat_mul, mat_mul, Matrix.mul_assoc, h3, Matrix.mul_assoc, h1, ← Matrix.mul_assoc, hu i]
  constructor
  · rintro ⟨b, hb, hbe⟩
    obtain ⟨C', h3, -⟩ := (hA i).2.2 _ (hA' i)
    have : b = u i * e1 (e0 h).1 i * (u i)⁻¹ := by
      apply hinj
      have h5 := congrArg (· * C') (hbe.trans h2.symm)
      simpa only [Matrix.mul_assoc, h3, Matrix.mul_one] using h5
    exact this ▸ hb
  · intro hb
    exact ⟨_, hb, h2⟩

end GlobalTheory.Mem.VolExists
