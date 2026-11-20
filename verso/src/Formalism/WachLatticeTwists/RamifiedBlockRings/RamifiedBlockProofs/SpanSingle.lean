import Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.KerEqOfFactor
import Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.ExistsSigma

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.ringDataObjects

open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities Formalism.RepresentationBoundsCohomology.BR

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem exists_kappa {O : Type} [CommRing O] [IsDomain O] {F : Type} [Field F] (f : O →+* F)
    (hf : Function.Injective f) :
    ∃ κ : FractionRing O →+* F, ∀ y, κ (algebraMap O (FractionRing O) y) = f y :=
  ⟨IsFractionRing.lift hf, IsFractionRing.lift_algebraMap hf⟩

section

variable {O O' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing O'] [IsDomain O']
  [IsDiscreteValuationRing O'] {X d G : Type} [Fintype d] [DecidableEq d] [Group G] {t : ℕ}
  {bl : d → Fin (t + 1)}

def bcHom (D : RingData O X d G t bl) (D' : RingData O' X d G t bl) (σ : D'.X' → D.X')
    (κ : FractionRing O →+* FractionRing O')
    (h : ∀ a ∈ D.R', (fun y' => (a (σ y')).map κ) ∈ D'.R') : D.R' →+* D'.R' :=
  RingHom.codRestrict ((RingHom.pi fun y' => κ.mapMatrix.comp
    (Pi.evalRingHom (fun _ : D.X' => Matrix d d (FractionRing O)) (σ y'))).comp D.R'.val.toRingHom) D'.R'
    (fun a => h a.1 a.2)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem bcHom_apply (D : RingData O X d G t bl) (D' : RingData O' X d G t bl) (σ : D'.X' → D.X')
    (κ : FractionRing O →+* FractionRing O')
    (h : ∀ a ∈ D.R', (fun y' => (a (σ y')).map κ) ∈ D'.R') (a : D.R') (y' : D'.X') :
    (bcHom D D' σ κ h a).1 y' = (a.1 (σ y')).map κ := rfl

end

/- English proof (translation)
Introduce a local definition for the expression. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem relMap_ev {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {X' d : Type} [Fintype d]
    [DecidableEq d] (R' : Subalgebra O (X' → Matrix d d (FractionRing O))) (x' : X') {m g : Type}
    [Fintype m] [Fintype g] (P : Matrix m g R') (v : g → EvalSp O d R' x') (i : m) (a : d) :
    relMap (FractionRing O) (EvalSp O d R' x') P v i a =
      ∑ q, ∑ b, (P i q).1 x' a b * (v q b : FractionRing O) := by
  let evA : EvalSp O d R' x' →+ FractionRing O :=
    { toFun := fun w => w a, map_zero' := rfl, map_add' := fun _ _ => rfl }
  show evA (∑ q, P i q • v q) = _
  rw [map_sum]
  rfl

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem span_single {R : Type*} [Ring R] {m g : Type} [Fintype m] [Fintype g] [DecidableEq g]
    (Θ : Matrix m g R) :
    Submodule.span R (Set.range fun j : g => (relSpan Θ).mkQ (Pi.single j (1 : R))) = ⊤ := by
  refine eq_top_iff.mpr fun z _ => ?_
  obtain ⟨w, rfl⟩ := (relSpan Θ).mkQ_surjective z
  have h : w = ∑ j, w j • (Pi.single j (1 : R) : g → R) := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  rw [h, map_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [map_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. By extensionality, compare the relevant components.

Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Extract witnesses or component facts from the available result. Introduce a local definition for the expression.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. By extensionality, compare the relevant components. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.

Introduce a local definition for the expression. Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Apply function extensionality and compare values at an arbitrary argument. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the indicated hypotheses using the stated equalities.

A detailed English derivation is pending.
-/
theorem moduleBc : StatModuleBc := by
  intro O O' _ _ _ _ _ _ _ _ _ e he X _ d G _ _ _ t bl T r π χ₁ ε g₀ eB e₁ s hX D D' hD hD' _ _ _
    NN _ _ g n hn
  have hj : Function.Injective (algebraMap O O') := FaithfulSMul.algebraMap_injective O O'
  have hι' : Function.Injective (algebraMap O' (FractionRing O')) :=
    IsFractionRing.injective O' (FractionRing O')
  obtain ⟨κ, hκ⟩ := exists_kappa ((algebraMap O' (FractionRing O')).comp (algebraMap O O')) (hι'.comp hj)
  have hκ' : ∀ y, κ (algebraMap O (FractionRing O) y) =
      algebraMap O' (FractionRing O') (algebraMap O O' y) := hκ
  obtain ⟨σ, hσ1, hσ2, hσπ⟩ := exists_sigma hj hX hD hD'
  have hmem : ∀ a ∈ D.R', (fun y' => (a (σ y')).map κ) ∈ D'.R' :=
    fun a ha => bcR'_mem hD hD' σ hσ1 hσ2 κ hκ' ha
  let bc : D.R' →+* D'.R' := bcHom D D' σ κ hmem
  have hbc : ∀ (a : D.R') y', (bc a).1 y' = (a.1 (σ y')).map κ := fun a y' => rfl

  have hblk : ∀ (a : D.R') k, D'.ρk k (bc a) = (D.ρk k a).map (algebraMap O O') := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h17, h18, -⟩ := hD
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h17', h18', -⟩ := hD'
    intro a k
    have h1 : D'.ρπ (bc a) = (D.ρπ a).map (algebraMap O O') := by
      ext u v
      apply hι'
      have e1 := congrFun (congrFun (h17' (bc a)) u) v
      have e2 := congrFun (congrFun (h17 a) u) v
      simp only [Matrix.map_apply] at e1 e2
      rw [e1, hbc, hσπ, Matrix.map_apply, ← e2, hκ']
      rfl
    rw [← h18', h1, ← h18]
    rfl
  obtain ⟨m, P, ⟨eq⟩⟩ := finPres D.R' NN g n hn
  let P' : Matrix (Fin m) (Fin g) D'.R' := P.map bc
  refine ⟨Coker P', inferInstance, inferInstance,
    fun j => (relSpan P').mkQ (Pi.single j (1 : D'.R')), span_single P', ?_, ?_⟩
  · intro Z hφ y' hy'
    obtain ⟨φ, hφ0⟩ := hφ (σ y') (by rw [hσ1]; exact hy')
    let ψ : Coker P →ₗ[D.R'] EvalSp O d D.R' (σ y') := φ ∘ₗ eq.symm.toLinearMap
    have hψ : ψ ≠ 0 := by
      intro h
      apply hφ0
      ext z
      have hz := LinearMap.congr_fun h (eq z)
      simpa [ψ] using hz
    let v := homEquiv (O := FractionRing O) P ψ
    have hv0 : v ≠ 0 := fun h => hψ ((LinearEquiv.map_eq_zero_iff _).mp h)
    let v' : Fin g → EvalSp O' d D'.R' y' := fun i a => κ ((v : Fin g → EvalSp O d D.R' (σ y')) i a)
    have hv' : v' ∈ LinearMap.ker (relMap (FractionRing O') (EvalSp O' d D'.R' y') P') := by
      rw [LinearMap.mem_ker]
      funext i
      funext a
      have h1 := congrFun (congrFun (LinearMap.mem_ker.mp v.2) i) a
      have h2 : ∑ q, ∑ b, (P i q).1 (σ y') a b *
          ((v : Fin g → EvalSp O d D.R' (σ y')) q b : FractionRing O) = 0 := by
        rw [← relMap_ev]
        exact h1
      rw [relMap_ev]
      show _ = (0 : FractionRing O')
      have h3 := congrArg κ h2
      rw [map_zero, map_sum] at h3
      rw [← h3]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [map_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [map_mul]
      rfl
    refine ⟨(homEquiv (O := FractionRing O') P').symm ⟨v', hv'⟩, fun h => hv0 ?_⟩
    have h4 : (⟨v', hv'⟩ : LinearMap.ker (relMap (FractionRing O') (EvalSp O' d D'.R' y') P')) = 0 :=
      (LinearEquiv.map_eq_zero_iff _).mp h
    have h5 : v' = 0 := congrArg Subtype.val h4
    apply Subtype.ext
    funext i a
    have h6 : κ ((v : Fin g → EvalSp O d D.R' (σ y')) i a) = 0 := congrFun (congrFun h5 i) a
    exact (map_eq_zero κ).mp h6
  · intro k
    have a1 := kerHomRect D.R' O (Fin m) (Fin g) {a // bl a = k} (D.ρk k).toRingHom P
    have a2 := (LinearEquiv.congrLeft (LatQ O {a // bl a = k} (D.ρk k).toRingHom) O eq).length_eq
    have a3 := kerHomRect D'.R' O' (Fin m) (Fin g) {a // bl a = k} (D'.ρk k).toRingHom P'
    have a4 := kerBc O O' e he (Fin m × {a // bl a = k}) (Fin g × {a // bl a = k})
      (fun p q => (D.ρk k).toRingHom (P p.1 q.1) p.2 q.2)
    have a5 : (Matrix.map (fun (p : Fin m × {a // bl a = k}) (q : Fin g × {a // bl a = k}) =>
        (D.ρk k).toRingHom (P p.1 q.1) p.2 q.2) (algebraMap O O')) =
        fun p q => (D'.ρk k).toRingHom (P' p.1 q.1) p.2 q.2 := by
      funext p q
      show algebraMap O O' (D.ρk k (P p.1 q.1) p.2 q.2) = D'.ρk k (bc (P p.1 q.1)) p.2 q.2
      rw [hblk]
      rfl
    rw [a5] at a4
    exact a3.symm.trans (a4.trans (by rw [a1, a2]))

end Formalism.RepresentationBoundsCohomology.ringDataObjects
