import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PseudoCoefficientUpqTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAuxiliarySplitPlaceNotMemFinsetStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenCompactLevelSphericalOffTypesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRestrictedProductHaarGivenFiniteFactorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TestFunctionsTransportLocalLatticeIsometriesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportPureTensorsProductMeasureFiniteAdelicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdmissibleRepHasTraceFiniteAdelicPureTensorFunctStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RepresentationTransportTopGroupEquivStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInequivalentRepresentativesThroughMemberStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TrMultEnd

structure RepB (G : Type) [Group G] where

  X : Type
  [acg : AddCommGroup X]
  [mod : Module ℂ X]

  ρ : Representation ℂ G X

attribute [instance] RepB.acg RepB.mod

def RepB.triv (G : Type) [Group G] : RepB G := ⟨ℂ, 1⟩

/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
theorem RepB.transport {G : Type} [Group G] {B : RepB G} {X : Type} [AddCommGroup X] [Module ℂ X]
    {ρ : Representation ℂ G X} (h : B = ⟨X, ρ⟩)
    (P : ∀ (X : Type) [AddCommGroup X] [Module ℂ X], Representation ℂ G X → Prop) : P B.X B.ρ ↔ P X ρ := by
  subst h; rfl

/- English proof (translation)
Set `b : Fin (n₁ + n₂ + 1) → RepB G` to `Fin.append (Fin.append (fun i => (⟨W₁ i, A i⟩ : RepB G)) fun i => ⟨W₂ i, B i⟩) fun _ : Fin 1 => ⟨W, σ⟩`. Establish `hbA : ∀ i, b (Fin.castAdd 1 (Fin.castAdd n₂ i)) = ⟨W₁ i, A i⟩` using `fun i => by simp [b]`. Establish `hbB : ∀ i, b (Fin.castAdd 1 (Fin.natAdd n₁ i)) = ⟨W₂ i, B i⟩` using `fun i => by simp [b]`. Establish `hbσ : b (Fin.natAdd (n₁ + n₂) 0) = ⟨W, σ⟩` using `by simp [b]`. Establish `hb : ∀ k, (∃ i, b k = ⟨W₁ i, A i⟩) ∨ (∃ i, b k = ⟨W₂ i, B i⟩) ∨ b k = ⟨W, σ⟩`.

Introduce `k`. Use `Fin.addCases (fun k' => ?_) (fun k' => ?_) k` and prove the remaining obligations. Use `Fin.addCases (fun i => ?_) (fun i => ?_) k'` and prove the remaining obligations. Conclude with `Or.inl ⟨i, hbA i⟩`. Conclude with `Or.inr (Or.inl ⟨i, hbB i⟩)`.

Conclude with `Or.inr (Or.inr (by rw [Subsingleton.elim k' 0]; exact hbσ))`. Take `⟨n, s, hne, ⟨j₀, hj₀⟩, hcov⟩` from `GlobalTheory.T.exists_inequivalentRepresentatives_through_member G (n₁ + n₂ + 1) (fun k => (b k).X) (fun k => (b k).ρ) (Fin.natAdd (n₁ + n₂) 0)`. Use `⟨n, fun j => (b (s j)).X, fun j => inferInstance, fun j => inferInstance, fun j => (b (s j)).ρ, hne, fun i => ?_, fun i => ?_, fun P hA hB hσ k => ?_, j₀, fun P hP => ?_⟩` and prove the remaining obligations. Take `⟨j, hj⟩` from `hcov (Fin.castAdd 1 (Fin.castAdd n₂ i))`. Conclude with `⟨j, (RepB.transport (hbA i) (fun X _ _ ρ => Nonempty (ρ.Equiv ((b (s j)).ρ)))).1 hj⟩`.

Take `⟨j, hj⟩` from `hcov (Fin.castAdd 1 (Fin.natAdd n₁ i))`. Conclude with `⟨j, (RepB.transport (hbB i) (fun X _ _ ρ => Nonempty (ρ.Equiv ((b (s j)).ρ)))).1 hj⟩`. Break down `hb (s k) with ⟨i, h⟩ | ⟨i, h⟩ | h` into its components or cases. Conclude with `(RepB.transport h P).2 (hA i)`. Conclude with `(RepB.transport h P).2 (hB i)`.

Conclude with `(RepB.transport h P).2 hσ`. Conclude with `(RepB.transport ((congrArg b hj₀).trans hbσ) P).2 hP`.
-/
theorem exists_family {G : Type} [Group G] [TopologicalSpace G]
    {n₁ : ℕ} {W₁ : Fin n₁ → Type} [∀ i, AddCommGroup (W₁ i)] [∀ i, Module ℂ (W₁ i)] (A : ∀ i, Representation ℂ G (W₁ i))
    {n₂ : ℕ} {W₂ : Fin n₂ → Type} [∀ i, AddCommGroup (W₂ i)] [∀ i, Module ℂ (W₂ i)] (B : ∀ i, Representation ℂ G (W₂ i))
    {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G W) :
    ∃ (m : ℕ) (Ws : Fin m → Type) (_ : ∀ i, AddCommGroup (Ws i)) (_ : ∀ i, Module ℂ (Ws i))
      (τ : ∀ i, Representation ℂ G (Ws i)),
      (∀ i j, i ≠ j → IsEmpty ((τ i).Equiv (τ j))) ∧
      (∀ i, ∃ j, Nonempty ((A i).Equiv (τ j))) ∧ (∀ i, ∃ j, Nonempty ((B i).Equiv (τ j))) ∧
      (∀ P : ∀ (X : Type) [AddCommGroup X] [Module ℂ X], Representation ℂ G X → Prop,
        (∀ i, P _ (A i)) → (∀ i, P _ (B i)) → P W σ → ∀ j, P _ (τ j)) ∧
      ∃ j₀, ∀ P : ∀ (X : Type) [AddCommGroup X] [Module ℂ X], Representation ℂ G X → Prop, P W σ → P _ (τ j₀) := by
  let b : Fin (n₁ + n₂ + 1) → RepB G :=
    Fin.append (Fin.append (fun i => (⟨W₁ i, A i⟩ : RepB G)) fun i => ⟨W₂ i, B i⟩) fun _ : Fin 1 => ⟨W, σ⟩
  have hbA : ∀ i, b (Fin.castAdd 1 (Fin.castAdd n₂ i)) = ⟨W₁ i, A i⟩ := fun i => by simp [b]
  have hbB : ∀ i, b (Fin.castAdd 1 (Fin.natAdd n₁ i)) = ⟨W₂ i, B i⟩ := fun i => by simp [b]
  have hbσ : b (Fin.natAdd (n₁ + n₂) 0) = ⟨W, σ⟩ := by simp [b]
  have hb : ∀ k, (∃ i, b k = ⟨W₁ i, A i⟩) ∨ (∃ i, b k = ⟨W₂ i, B i⟩) ∨ b k = ⟨W, σ⟩ := by
    intro k
    refine Fin.addCases (fun k' => ?_) (fun k' => ?_) k
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) k'
      · exact Or.inl ⟨i, hbA i⟩
      · exact Or.inr (Or.inl ⟨i, hbB i⟩)
    · exact Or.inr (Or.inr (by rw [Subsingleton.elim k' 0]; exact hbσ))
  obtain ⟨n, s, hne, ⟨j₀, hj₀⟩, hcov⟩ :=
    GlobalTheory.T.exists_inequivalentRepresentatives_through_member G (n₁ + n₂ + 1) (fun k => (b k).X) (fun k => (b k).ρ) (Fin.natAdd (n₁ + n₂) 0)
  refine ⟨n, fun j => (b (s j)).X, fun j => inferInstance, fun j => inferInstance, fun j => (b (s j)).ρ, hne,
    fun i => ?_, fun i => ?_, fun P hA hB hσ k => ?_, j₀, fun P hP => ?_⟩
  · obtain ⟨j, hj⟩ := hcov (Fin.castAdd 1 (Fin.castAdd n₂ i))
    exact ⟨j, (RepB.transport (hbA i) (fun X _ _ ρ => Nonempty (ρ.Equiv ((b (s j)).ρ)))).1 hj⟩
  · obtain ⟨j, hj⟩ := hcov (Fin.castAdd 1 (Fin.natAdd n₁ i))
    exact ⟨j, (RepB.transport (hbB i) (fun X _ _ ρ => Nonempty (ρ.Equiv ((b (s j)).ρ)))).1 hj⟩
  · rcases hb (s k) with ⟨i, h⟩ | ⟨i, h⟩ | h
    · exact (RepB.transport h P).2 (hA i)
    · exact (RepB.transport h P).2 (hB i)
    · exact (RepB.transport h P).2 hσ
  · exact (RepB.transport ((congrArg b hj₀).trans hbσ) P).2 hP

def equivComp {G H : Type} [Group G] [Group H] {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    {ρ : Representation ℂ G X} {ρ' : Representation ℂ G Y} (e : ρ.Equiv ρ') (f : H →* G) :
    Representation.Equiv (ρ.comp f : Representation ℂ H X) (ρ'.comp f) :=
  Representation.Equiv.mk e.toLinearEquiv fun h => by
    ext x; exact congrArg (fun l : X →ₗ[ℂ] Y => l x) (e.isIntertwining' (f h))

def equivCompSymm {G H : Type} [Group G] [Group H] {X : Type} [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ G X) (Φ : G ≃* H) :
    Representation.Equiv ρ (((ρ.comp Φ.symm.toMonoidHom : Representation ℂ H X).comp Φ.toMonoidHom : Representation ℂ G X)) :=
  Representation.Equiv.mk (LinearEquiv.refl ℂ X) fun g => by ext x; simp

def equivCompSymm' {G H : Type} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H] {X : Type} [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ H X) (Φ : G ≃ₜ* H) :
    Representation.Equiv ρ (((ρ.comp Φ.symm.symm.toMulEquiv.toMonoidHom : Representation ℂ G X).comp Φ.symm.toMulEquiv.toMonoidHom : Representation ℂ H X)) :=
  Representation.Equiv.mk (LinearEquiv.refl ℂ X) fun g => by
    ext x
    change ρ g x = ρ (Φ (Φ.symm g)) x
    rw [Φ.apply_symm_apply]

end GlobalTheory.TrMultEnd

namespace GlobalTheory.TrMultEnd

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `D V lam S M T hodd hgap hlam hnf V' hr S' M' hlam' j hj Φ hΦ μ _ _ μ' _ _ W _ _ σ hirr hadm htv`. Take `⟨U, hU⟩` from `GlobalTheory.T.exists_splitPlaceHermitianSpace_notMem_finset D V T.S`. Set `μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)` to `fun v => haarLoc D.sp.cm.sig V.gram (frameLat V) v`. Establish `hμf : ∀ v, (μf v).IsHaarMeasure` using `fun v => inferInstance`. Establish `h1 : ∀ᶠ v in cofinite, μf v (Kv V v) = 1` using `Eventually.of_forall fun v => haarLoc_stabLoc _ _ _ v`.

Establish `h1K : ∀ v, μf v (Kv V v) = 1` using `fun v => haarLoc_stabLoc _ _ _ v`. Use `clear_value μf`. Take `⟨⟨μa, hμa⟩, ν, hν⟩` from `GlobalTheory.T.exists_restrictedProduct_haar_given_finiteFactors D V μ μf hμf h1`. Take `⟨hjK, hTU⟩` from `GlobalTheory.T.testFunctions_transport_localLatticeIsometries D V V' hr j hj`. Take `⟨T', U', hNF', hTF'⟩` from `hTU T U`.

Set `μf' : ∀ v, Measure (GLoc D.sp.cm.sig V'.gram v)` to `fun v => (μf v).map (j v)`. Establish `hμf' : ∀ v, (μf' v).IsHaarMeasure` using `fun v => (j v).isHaarMeasure_map (μf v)`. Establish `h1' : ∀ᶠ v in cofinite, μf' v (Kv V' v) = 1` using `Eventually.of_forall fun v => by`. Establish `hm : MeasurableSet (Kv V' v : Set (GLoc D.sp.cm.sig V'.gram v))` using `(isOpen_stabLoc _ _ _ v).measurableSet`. Rewrite using `[show μf' v (Kv V' v) = μf v ((j v) ⁻¹' (Kv V' v)) from Measure.map_apply (j v).continuous.measurable hm, show (j v) ⁻¹' (Kv V' v : Set _) = Kv V v from Set.ext fun g => hjK v g]`.

Conclude with `h1K v`. Take `⟨⟨μa', hμa'⟩, -⟩` from `GlobalTheory.T.exists_restrictedProduct_haar_given_finiteFactors D V' μ' μf' hμf' h1'`. Use `clear hμf'`. Take `⟨hfinFn, hνmap⟩` from `GlobalTheory.T.transport_pureTensors_productMeasure_finiteAdelic D V V' j hjK Φ hΦ`. Establish `hν'` using `hνmap μf ν hν`.

Take `⟨fa, hfa⟩` from `haveI := (isRestrictedProd_iff.1 hμa).1`. Use the proof step `hP.exists_isTestArchG M μa`. Take `⟨fa', hfa'⟩` from `haveI := (isRestrictedProd_iff.1 hμa').1`. Use the proof step `hP.exists_isTestArchG M' μa'`. Take `⟨K, hKo, hKc, hK⟩` from `GlobalTheory.T.exists_openCompact_level_sphericalOffTypes D V T U`.

Take `⟨hfin, hfam⟩` from `hF D V S M μ`. Take `⟨hfin', hfam'⟩` from `hF D V' S' M' μ'`. Take `⟨n₁, W₁, _, _, σ₁, hσ₁, hcov₁⟩` from `hfam K hKo`. Set `K' : Subgroup (GfC V')` to `K.map Φ.toMulEquiv.toMonoidHom`. Establish `hK'coe : (K' : Set (GfC V')) = Φ '' K` using `Subgroup.coe_map _ _`.

Establish `hK'o : IsOpen (K' : Set (GfC V'))` using `hK'coe ▸ Φ.toHomeomorph.isOpenMap _ hKo`. Establish `hK'c : IsCompact (K' : Set (GfC V'))` using `hK'coe ▸ hKc.image Φ.continuous`. Take `⟨n₂, W₂, _, _, σ₂, hσ₂, hcov₂⟩` from `hfam' K' hK'o`. Set `B : ∀ i, Representation ℂ (GfC V) (W₂ i)` to `fun i => (σ₂ i).comp Φ.symm.symm.toMulEquiv.toMonoidHom`. Take `⟨m, Ws, _, _, τ, hne, hA, hB, hmem, j₀, hj₀⟩` from `exists_family σ₁ B σ`.

Establish `hBi : ∀ i, (B i).IsIrreducible ∧ IsAdmissible (B i)` using `fun i =>`. Establish `h` using `GlobalTheory.T.representation_transport_topGroupEquiv _ _ Φ.symm (ν.map Φ) (W₂ i) (σ₂ i)`. Use the proof step `⟨h.1 (hσ₂.1 i), h.2.1 (hσ₂.2.1 i)⟩`. Establish `hτ : ∀ i, (τ i).IsIrreducible ∧ IsAdmissible (τ i)` using `hmem (fun X _ _ ρ => ρ.IsIrreducible ∧ IsAdmissible ρ) (fun i => ⟨hσ₁.1 i, hσ₁.2.1 i⟩) hBi ⟨hirr, hadm⟩`. Set `τ' : ∀ i, Representation ℂ (GfC V') (Ws i)` to `fun i => (τ i).comp Φ.symm.toMulEquiv.toMonoidHom`.

Establish `hfamτ : IsIrrFam τ` using `⟨fun i => (hτ i).1, fun i => (hτ i).2, hne⟩`. Establish `hfamτ' : IsIrrFam τ'`. Use `⟨fun i => (GlobalTheory.T.representation_transport_topGroupEquiv _ _ Φ ν _ (τ i)).1 (hτ i).1, fun i => (GlobalTheory.T.representation_transport_topGroupEquiv _ _ Φ ν _ (τ i)).2.1 (hτ i).2, fun i k hik => ⟨fun e => (hne i k hik).false ?_⟩⟩` and prove the remaining obligations. Conclude with `(equivCompSymm (τ i) Φ.toMulEquiv).trans ((equivComp e Φ.toMulEquiv.toMonoidHom).trans (equivCompSymm (τ k) Φ.toMulEquiv).symm)`. Establish `cov : ∀ ff, IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff → (∀ k ∈ K, ∀ g, finFn V ff (k * g) = finFn V ff g) → ∀ (X : Type) [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (GfC V) X), ρ.IsIrreducible → IsAdmissible ρ → mCuspDS μ ρ M ≠ 0 → ¬ GlobalTheory.IndefiniteRowSideFul …`.

Introduce `ff hffin hKinv X _ _ ρ hi ha hm hz`. Use `haveI := hν.1`. Take `⟨x, hx0, hx⟩` from `(GlobalTheory.T.admissibleRep_hasTrace_finiteAdelicPureTensorFunction D V ν ff hffin X ρ ha).2 K hKo hKc hKinv hz`. Take `⟨i, ⟨e⟩⟩` from `hcov₁ X ρ hi ha hm ⟨x, hx0, hx⟩`. Take `⟨k, ⟨e'⟩⟩` from `hA i`.

Conclude with `⟨k, ⟨e.trans e'⟩⟩`. Establish `cov' : ∀ ff, IsFinFamily D.sp.cm.sig V'.gram (frameLat V') (transfer j ff) → (∀ k ∈ K, ∀ g, finFn V ff (k * g) = finFn V ff g) → ∀ (X : Type) [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (GfC V') X), ρ.IsIrreducible → IsAdmissible ρ → mCuspDS μ' ρ M' ≠ 0 → ¬ GlobalTheory.I …`. Introduce `ff hffin hKinv X _ _ ρ hi ha hm hz`. Use `haveI := hν'.1`. Establish `hKinv' : ∀ k ∈ K', ∀ g, finFn V' (transfer j ff) (k * g) = finFn V' (transfer j ff) g`.

Introduce `k hk g`. Take `⟨k₀, hk₀, rfl⟩` from `Subgroup.mem_map.1 hk`. Take `⟨g₀, rfl⟩` from `Φ.surjective g`. Express the relevant statement in the definitionally equal form `finFn V' (transfer j ff) (Φ k₀ * Φ g₀) = _`. Rewrite using `[← map_mul, hfinFn, hfinFn, hKinv k₀ hk₀]`.

Take `⟨x, hx0, hx⟩` from `(GlobalTheory.T.admissibleRep_hasTrace_finiteAdelicPureTensorFunction D V' (ν.map Φ) (transfer j ff) hffin X ρ ha).2 K' hK'o hK'c hKinv' hz`. Take `⟨i, ⟨e⟩⟩` from `hcov₂ X ρ hi ha hm ⟨x, hx0, hx⟩`. Take `⟨k, ⟨e'⟩⟩` from `hB i`. Conclude with `⟨k, ⟨e.trans ((equivCompSymm' (σ₂ i) Φ).trans (equivComp e' Φ.symm.toMulEquiv.toMonoidHom))⟩⟩`. Set `a : Fin m → ℂ` to `fun i => ((mCuspDS μ (τ i) M).toNat : ℂ) - ((mCuspDS μ' (τ' i) M').toNat : ℂ)`.

Set `lam' : D.what₂.Tau → Fin V'.rank → ℤ` to `fun ρ i => lam ρ (i.cast hr)`. Establish `hgap' : ∀ ρ, Gap (lam' ρ)` using `fun ρ i k hik => by`. Use `hgap ρ (i.cast hr) (k.cast hr) (by simpa using hik)` as an intermediate fact. Rewrite using `[hr]`. Conclude with `this`.

Establish `hodd' : Odd V'.rank` using `hr ▸ hodd`. Establish `key : ∀ ff, IsTestFin T U μf ff → SphRest T U ff → ∀ c : Fin m → ℂ, (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace ν (τ i) (finFn V ff) (c i)) → ∑ i, a i * c i = 0`. Introduce `ff hff hsph c hc`. Take `⟨hffin, hKinv⟩` from `hK μf hμf ff hff hsph`. Use `clear hμf`.

Establish `htd : IsTestData V lam M T U μa μf μ fa ff` using `⟨hodd, hgap, hlam, hnf, hμa, hfa, hff⟩`. Establish `h₁` using `hT D V lam S M T U μa μf μ fa ff htd ν hν m Ws τ hfamτ (cov ff hffin hKinv) c hc`. Establish `hff'` using `hTF' μf ff hff`. Establish `htd' : IsTestData V' lam' M' T' U' μa' μf' μ' fa' (transfer j ff)` using `⟨hodd', hgap', hlam', hNF' hnf, hμa', hfa', hff'⟩`. Establish `hc' : ∀ i, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace (ν.map Φ) (τ' i) (finFn V' (transfer j ff)) (c i)`.

Introduce `i`. Take `⟨A, hA, hA'⟩` from `hc i`. Conclude with `⟨A, ((GlobalTheory.T.representation_transport_topGroupEquiv _ _ Φ ν _ (τ i)).2.2 (finFn V ff) (finFn V' (transfer j ff)) (hfinFn ff) A).2 hA, hA'⟩`. Establish `h₂` using `hT D V' lam' S' M' T' U' μa' μf' μ' fa' (transfer j ff) htd' (ν.map Φ) hν' m Ws τ' hfamτ' (cov' ff hff'.isFinFamily hKinv) c hc'`. Take `⟨c₀, hc₁, hc₂⟩` from `hE D V lam S M T U μa μf μ fa ff htd V' hr S' M' hlam' j hj μa' μ' fa' hμa' hfa'`.

Establish `e : ∑ i, ((mCuspDS μ (τ i) M).toNat : ℂ) * c i = ∑ i, ((mCuspDS μ' (τ' i) M').toNat : ℂ) * c i` using `h₁.2.symm.trans (hc₁.2.trans (hc₂.2.symm.trans h₂.2))`. Simplify using `only [a, sub_mul, Finset.sum_sub_distrib, e, sub_self]`. Take `⟨hm₁, hm₂, htv₀⟩` from `hj₀ (fun X _ _ ρ => mCuspDS μ ρ M = mCuspDS μ σ M ∧ mCuspDS μ' (ρ.comp Φ.symm.toMulEquiv.toMonoidHom) M' = mCuspDS μ' (σ.comp Φ.symm.toMulEquiv.toMonoidHom) M' ∧ HasTypeVec T ρ) ⟨rfl, rfl, htv⟩`. Establish `ha` using `hS D V T U hU μf hμf h1 ν hν m Ws τ hfamτ a key j₀ htv₀`. Establish `hnat : (mCuspDS μ σ M).toNat = (mCuspDS μ' (σ.comp Φ.symm.toMulEquiv.toMonoidHom) M').toNat`.

Establish `: ((mCuspDS μ (τ j₀) M).toNat : ℂ) = ((mCuspDS μ' (τ' j₀) M').toNat : ℂ)` using `sub_eq_zero.1 ha`. Rewrite using `[← hm₁, ← hm₂]`. Conclude with `this` after adjusting the coercions. Establish `hσ'` using `GlobalTheory.T.representation_transport_topGroupEquiv _ _ Φ ν W σ`. Rewrite using `[← Cardinal.cast_toNat_of_lt_aleph0 (hfin W σ hirr hadm), ← Cardinal.cast_toNat_of_lt_aleph0 (hfin' W _ (hσ'.1 hirr) (hσ'.2.1 hadm)), hnat]`.
-/
theorem trCusp_of_steps (hP : GlobalTheory.Published.PseudoCoefficientUpq) (hF : SpecFin) (hT : SpecTrace) (hS : Separation)
    (hE : TraceEq) : TRCusp := by
  intro D V lam S M T hodd hgap hlam hnf V' hr S' M' hlam' j hj Φ hΦ μ _ _ μ' _ _ W _ _ σ hirr hadm htv
  obtain ⟨U, hU⟩ := GlobalTheory.T.exists_splitPlaceHermitianSpace_notMem_finset D V T.S
  let μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v) := fun v => haarLoc D.sp.cm.sig V.gram (frameLat V) v
  have hμf : ∀ v, (μf v).IsHaarMeasure := fun v => inferInstance
  have h1 : ∀ᶠ v in cofinite, μf v (Kv V v) = 1 := Eventually.of_forall fun v => haarLoc_stabLoc _ _ _ v
  have h1K : ∀ v, μf v (Kv V v) = 1 := fun v => haarLoc_stabLoc _ _ _ v
  clear_value μf
  obtain ⟨⟨μa, hμa⟩, ν, hν⟩ := GlobalTheory.T.exists_restrictedProduct_haar_given_finiteFactors D V μ μf hμf h1
  obtain ⟨hjK, hTU⟩ := GlobalTheory.T.testFunctions_transport_localLatticeIsometries D V V' hr j hj
  obtain ⟨T', U', hNF', hTF'⟩ := hTU T U
  let μf' : ∀ v, Measure (GLoc D.sp.cm.sig V'.gram v) := fun v => (μf v).map (j v)
  have hμf' : ∀ v, (μf' v).IsHaarMeasure := fun v => (j v).isHaarMeasure_map (μf v)
  have h1' : ∀ᶠ v in cofinite, μf' v (Kv V' v) = 1 := Eventually.of_forall fun v => by
    have hm : MeasurableSet (Kv V' v : Set (GLoc D.sp.cm.sig V'.gram v)) := (isOpen_stabLoc _ _ _ v).measurableSet
    rw [show μf' v (Kv V' v) = μf v ((j v) ⁻¹' (Kv V' v)) from Measure.map_apply (j v).continuous.measurable hm,
      show (j v) ⁻¹' (Kv V' v : Set _) = Kv V v from Set.ext fun g => hjK v g]
    exact h1K v
  obtain ⟨⟨μa', hμa'⟩, -⟩ := GlobalTheory.T.exists_restrictedProduct_haar_given_finiteFactors D V' μ' μf' hμf' h1'
  clear hμf'
  obtain ⟨hfinFn, hνmap⟩ := GlobalTheory.T.transport_pureTensors_productMeasure_finiteAdelic D V V' j hjK Φ hΦ
  have hν' := hνmap μf ν hν
  obtain ⟨fa, hfa⟩ := haveI := (isRestrictedProd_iff.1 hμa).1; hP.exists_isTestArchG M μa
  obtain ⟨fa', hfa'⟩ := haveI := (isRestrictedProd_iff.1 hμa').1; hP.exists_isTestArchG M' μa'
  obtain ⟨K, hKo, hKc, hK⟩ := GlobalTheory.T.exists_openCompact_level_sphericalOffTypes D V T U
  obtain ⟨hfin, hfam⟩ := hF D V S M μ
  obtain ⟨hfin', hfam'⟩ := hF D V' S' M' μ'
  obtain ⟨n₁, W₁, _, _, σ₁, hσ₁, hcov₁⟩ := hfam K hKo
  let K' : Subgroup (GfC V') := K.map Φ.toMulEquiv.toMonoidHom
  have hK'coe : (K' : Set (GfC V')) = Φ '' K := Subgroup.coe_map _ _
  have hK'o : IsOpen (K' : Set (GfC V')) := hK'coe ▸ Φ.toHomeomorph.isOpenMap _ hKo
  have hK'c : IsCompact (K' : Set (GfC V')) := hK'coe ▸ hKc.image Φ.continuous
  obtain ⟨n₂, W₂, _, _, σ₂, hσ₂, hcov₂⟩ := hfam' K' hK'o
  let B : ∀ i, Representation ℂ (GfC V) (W₂ i) := fun i => (σ₂ i).comp Φ.symm.symm.toMulEquiv.toMonoidHom
  obtain ⟨m, Ws, _, _, τ, hne, hA, hB, hmem, j₀, hj₀⟩ := exists_family σ₁ B σ

  have hBi : ∀ i, (B i).IsIrreducible ∧ IsAdmissible (B i) := fun i =>
    have h := GlobalTheory.T.representation_transport_topGroupEquiv _ _ Φ.symm (ν.map Φ) (W₂ i) (σ₂ i)
    ⟨h.1 (hσ₂.1 i), h.2.1 (hσ₂.2.1 i)⟩
  have hτ : ∀ i, (τ i).IsIrreducible ∧ IsAdmissible (τ i) :=
    hmem (fun X _ _ ρ => ρ.IsIrreducible ∧ IsAdmissible ρ) (fun i => ⟨hσ₁.1 i, hσ₁.2.1 i⟩) hBi ⟨hirr, hadm⟩
  let τ' : ∀ i, Representation ℂ (GfC V') (Ws i) := fun i => (τ i).comp Φ.symm.toMulEquiv.toMonoidHom
  have hfamτ : IsIrrFam τ := ⟨fun i => (hτ i).1, fun i => (hτ i).2, hne⟩
  have hfamτ' : IsIrrFam τ' := by
    refine ⟨fun i => (GlobalTheory.T.representation_transport_topGroupEquiv _ _ Φ ν _ (τ i)).1 (hτ i).1, fun i => (GlobalTheory.T.representation_transport_topGroupEquiv _ _ Φ ν _ (τ i)).2.1 (hτ i).2,
      fun i k hik => ⟨fun e => (hne i k hik).false ?_⟩⟩
    exact (equivCompSymm (τ i) Φ.toMulEquiv).trans
      ((equivComp e Φ.toMulEquiv.toMonoidHom).trans (equivCompSymm (τ k) Φ.toMulEquiv).symm)

  have cov : ∀ ff, IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff → (∀ k ∈ K, ∀ g, finFn V ff (k * g) = finFn V ff g) →
      ∀ (X : Type) [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (GfC V) X), ρ.IsIrreducible → IsAdmissible ρ →
        mCuspDS μ ρ M ≠ 0 → ¬ GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν ρ (finFn V ff) 0 → ∃ i, Nonempty (ρ.Equiv (τ i)) := by
    intro ff hffin hKinv X _ _ ρ hi ha hm hz
    haveI := hν.1
    obtain ⟨x, hx0, hx⟩ := (GlobalTheory.T.admissibleRep_hasTrace_finiteAdelicPureTensorFunction D V ν ff hffin X ρ ha).2 K hKo hKc hKinv hz
    obtain ⟨i, ⟨e⟩⟩ := hcov₁ X ρ hi ha hm ⟨x, hx0, hx⟩
    obtain ⟨k, ⟨e'⟩⟩ := hA i
    exact ⟨k, ⟨e.trans e'⟩⟩
  have cov' : ∀ ff, IsFinFamily D.sp.cm.sig V'.gram (frameLat V') (transfer j ff) →
      (∀ k ∈ K, ∀ g, finFn V ff (k * g) = finFn V ff g) →
      ∀ (X : Type) [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (GfC V') X), ρ.IsIrreducible → IsAdmissible ρ →
        mCuspDS μ' ρ M' ≠ 0 → ¬ GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp (ν.map Φ) ρ (finFn V' (transfer j ff)) 0 →
          ∃ i, Nonempty (ρ.Equiv (τ' i)) := by
    intro ff hffin hKinv X _ _ ρ hi ha hm hz
    haveI := hν'.1
    have hKinv' : ∀ k ∈ K', ∀ g, finFn V' (transfer j ff) (k * g) = finFn V' (transfer j ff) g := by
      intro k hk g
      obtain ⟨k₀, hk₀, rfl⟩ := Subgroup.mem_map.1 hk
      obtain ⟨g₀, rfl⟩ := Φ.surjective g
      change finFn V' (transfer j ff) (Φ k₀ * Φ g₀) = _
      rw [← map_mul, hfinFn, hfinFn, hKinv k₀ hk₀]
    obtain ⟨x, hx0, hx⟩ := (GlobalTheory.T.admissibleRep_hasTrace_finiteAdelicPureTensorFunction D V' (ν.map Φ) (transfer j ff) hffin X ρ ha).2 K' hK'o hK'c hKinv' hz
    obtain ⟨i, ⟨e⟩⟩ := hcov₂ X ρ hi ha hm ⟨x, hx0, hx⟩
    obtain ⟨k, ⟨e'⟩⟩ := hB i
    exact ⟨k, ⟨e.trans ((equivCompSymm' (σ₂ i) Φ).trans (equivComp e' Φ.symm.toMulEquiv.toMonoidHom))⟩⟩

  let a : Fin m → ℂ := fun i => ((mCuspDS μ (τ i) M).toNat : ℂ) - ((mCuspDS μ' (τ' i) M').toNat : ℂ)
  let lam' : D.what₂.Tau → Fin V'.rank → ℤ := fun ρ i => lam ρ (i.cast hr)
  have hgap' : ∀ ρ, Gap (lam' ρ) := fun ρ i k hik => by
    have := hgap ρ (i.cast hr) (k.cast hr) (by simpa using hik)
    rw [hr]; exact this
  have hodd' : Odd V'.rank := hr ▸ hodd
  have key : ∀ ff, IsTestFin T U μf ff → SphRest T U ff →
      ∀ c : Fin m → ℂ, (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace ν (τ i) (finFn V ff) (c i)) → ∑ i, a i * c i = 0 := by
    intro ff hff hsph c hc
    obtain ⟨hffin, hKinv⟩ := hK μf hμf ff hff hsph
    clear hμf
    have htd : IsTestData V lam M T U μa μf μ fa ff := ⟨hodd, hgap, hlam, hnf, hμa, hfa, hff⟩
    have h₁ := hT D V lam S M T U μa μf μ fa ff htd ν hν m Ws τ hfamτ (cov ff hffin hKinv) c hc
    have hff' := hTF' μf ff hff
    have htd' : IsTestData V' lam' M' T' U' μa' μf' μ' fa' (transfer j ff) :=
      ⟨hodd', hgap', hlam', hNF' hnf, hμa', hfa', hff'⟩
    have hc' : ∀ i, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace (ν.map Φ) (τ' i) (finFn V' (transfer j ff)) (c i) := by
      intro i
      obtain ⟨A, hA, hA'⟩ := hc i
      exact ⟨A, ((GlobalTheory.T.representation_transport_topGroupEquiv _ _ Φ ν _ (τ i)).2.2 (finFn V ff) (finFn V' (transfer j ff)) (hfinFn ff) A).2 hA, hA'⟩
    have h₂ := hT D V' lam' S' M' T' U' μa' μf' μ' fa' (transfer j ff) htd' (ν.map Φ) hν' m Ws τ' hfamτ'
      (cov' ff hff'.isFinFamily hKinv) c hc'
    obtain ⟨c₀, hc₁, hc₂⟩ := hE D V lam S M T U μa μf μ fa ff htd V' hr S' M' hlam' j hj μa' μ' fa' hμa' hfa'
    have e : ∑ i, ((mCuspDS μ (τ i) M).toNat : ℂ) * c i = ∑ i, ((mCuspDS μ' (τ' i) M').toNat : ℂ) * c i :=
      h₁.2.symm.trans (hc₁.2.trans (hc₂.2.symm.trans h₂.2))
    simp only [a, sub_mul, Finset.sum_sub_distrib, e, sub_self]
  obtain ⟨hm₁, hm₂, htv₀⟩ := hj₀ (fun X _ _ ρ => mCuspDS μ ρ M = mCuspDS μ σ M ∧
    mCuspDS μ' (ρ.comp Φ.symm.toMulEquiv.toMonoidHom) M' = mCuspDS μ' (σ.comp Φ.symm.toMulEquiv.toMonoidHom) M' ∧
    HasTypeVec T ρ) ⟨rfl, rfl, htv⟩
  have ha := hS D V T U hU μf hμf h1 ν hν m Ws τ hfamτ a key j₀ htv₀
  have hnat : (mCuspDS μ σ M).toNat = (mCuspDS μ' (σ.comp Φ.symm.toMulEquiv.toMonoidHom) M').toNat := by
    have : ((mCuspDS μ (τ j₀) M).toNat : ℂ) = ((mCuspDS μ' (τ' j₀) M').toNat : ℂ) := sub_eq_zero.1 ha
    rw [← hm₁, ← hm₂]
    exact_mod_cast this
  have hσ' := GlobalTheory.T.representation_transport_topGroupEquiv _ _ Φ ν W σ
  rw [← Cardinal.cast_toNat_of_lt_aleph0 (hfin W σ hirr hadm),
    ← Cardinal.cast_toNat_of_lt_aleph0 (hfin' W _ (hσ'.1 hirr) (hσ'.2.1 hadm)), hnat]

end GlobalTheory.TrMultEnd
