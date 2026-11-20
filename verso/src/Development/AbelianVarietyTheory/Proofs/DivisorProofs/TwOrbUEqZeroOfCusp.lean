import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MaxWeightGL1EqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockParOpp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocPartMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralizerSeparableCommutative
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjCentralizerLeBlockDiagonalLeviStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleCosetVolumeWeightedSumConjStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitSumVanishesOfParabolicSums
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DsumEqZeroOfFibreSumsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroCentralizerParabolicCosetStabilizeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumUnipotentConjEqZeroOfConstantTermZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMemBlockUpperUnipotentRadicalStatement

noncomputable section

open MeasureTheory Matrix
open scoped Classical

namespace GlobalTheory.OrbDesc

open GlobalTheory.OrbDesc in

/- English proof (translation)
Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem avg_const' {H : Type} [Group H] (c : ℂ) : GlobalTheory.BCT.avg (fun _ : H => c) = c := by
  have h : GlobalTheory.BCT.rStab (fun _ : H => c) = ⊤ := eq_top_iff.2 fun _ _ _ => rfl
  unfold GlobalTheory.BCT.avg
  haveI : Subsingleton (H ⧸ GlobalTheory.BCT.rStab (fun _ : H => c)) := by
    rw [h]; exact QuotientGroup.subsingleton_quotient_top
  rw [finsum_eq_single _ (QuotientGroup.mk 1 : H ⧸ GlobalTheory.BCT.rStab (fun _ : H => c))
    (fun x hx => absurd (Subsingleton.elim x _) hx), h, Subgroup.index_top]
  simp

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Reduce the equality to equality of the corresponding arguments. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem twOrbU_eq_dsum {G : Type} [Group G] (K0 U : Subgroup G) (γ : G) (f : G → ℂ)
    (hbi : ∀ k ∈ K0, ∀ k' ∈ K0, ∀ g, f (k * g * k') = f g) :
    GlobalTheory.LKLoc.twOrbU (MonoidHom.id G) K0 γ U f =
      GlobalTheory.OrbDesc.dsum (GlobalTheory.BCT.twCent (MonoidHom.id G) γ) K0 U (fun x => f (x⁻¹ * γ * x)) := by
  unfold GlobalTheory.LKLoc.twOrbU GlobalTheory.LKLoc.orbSum GlobalTheory.OrbDesc.dsum GlobalTheory.OrbDesc.wt
  refine finsum_congr fun q => ?_
  congr 1
  have hc : (fun k : K0 => f ((Quotient.out q * k)⁻¹ * γ * (MonoidHom.id G) (Quotient.out q * k))) =
      fun _ => f ((Quotient.out q)⁻¹ * γ * Quotient.out q) := by
    funext k
    have := hbi (k : G)⁻¹ (K0.inv_mem k.2) k k.2 ((Quotient.out q)⁻¹ * γ * Quotient.out q)
    rw [← this]
    simp only [MonoidHom.id_apply, _root_.mul_inv_rev, mul_assoc]
  rw [hc, avg_const']

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Express the relevant assertion in an equivalent form by its definition.

Express the relevant assertion in an equivalent form by its definition. Simplify using the standard rewrite rules. Chain the equalities or inequalities of the calculation. Fix the arbitrary inputs or assume the hypotheses. Express the relevant assertion in an equivalent form by its definition.

Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition. Simplify using the standard rewrite rules. Chain the equalities or inequalities of the calculation.
-/
theorem twCent_conj {G : Type} [Group G] (γ c : G) :
    (GlobalTheory.BCT.twCent (MonoidHom.id G) γ).map (MulAut.conj c⁻¹).toMonoidHom =
      GlobalTheory.BCT.twCent (MonoidHom.id G) (c⁻¹ * γ * c) := by
  ext g
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨x, hx, rfl⟩
    change _ * _ = _ * _
    change x * γ = γ * x at hx
    simp only [MonoidHom.id_apply, inv_inv]
    calc c⁻¹ * x * c * (c⁻¹ * γ * c) = c⁻¹ * (x * γ) * c := by group
      _ = c⁻¹ * (γ * x) * c := by rw [hx]
      _ = c⁻¹ * γ * c * (c⁻¹ * x * c) := by group
  · intro hg
    change g * (c⁻¹ * γ * c) = (c⁻¹ * γ * c) * g at hg
    refine ⟨c * g * c⁻¹, ?_, by group⟩
    change _ * _ = _ * _
    simp only [MonoidHom.id_apply]
    calc c * g * c⁻¹ * γ = c * (g * (c⁻¹ * γ * c)) * c⁻¹ := by group
      _ = c * ((c⁻¹ * γ * c) * g) * c⁻¹ := by rw [hg]
      _ = γ * (c * g * c⁻¹) := by group

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Supply the required witnesses or components.
-/
theorem conj_open_compact {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (S : Subgroup G) (d : G)
    (ho : IsOpen (S : Set G)) (hc : IsCompact (S : Set G)) :
    IsOpen ((S.map (MulAut.conj d).toMonoidHom : Subgroup G) : Set G) ∧
      IsCompact ((S.map (MulAut.conj d).toMonoidHom : Subgroup G) : Set G) := by
  let h : G ≃ₜ G := (Homeomorph.mulLeft d).trans (Homeomorph.mulRight d⁻¹)
  have e : ((S.map (MulAut.conj d).toMonoidHom : Subgroup G) : Set G) = h '' (S : Set G) := by
    ext x
    simp [h, MulAut.conj_apply]
  rw [e]
  exact ⟨h.isOpenMap _ ho, hc.image h.continuous⟩

/- English proof (translation)
Assume the hypotheses and unpack their components. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Express the relevant assertion in an equivalent form by its definition. Simplify using the standard rewrite rules.

Apply the first step, then apply the next step to every resulting obligation.
-/
theorem blockUni_le_blockPar {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] {a b : ℕ}
    (e : ι ≃ Fin a ⊕ Fin b) : GlobalTheory.OrbDesc.blockUni (K := K) e ≤ GlobalTheory.OrbDesc.blockPar e := by
  rintro _ ⟨X, rfl⟩
  intro i j hij
  simp only [GlobalTheory.OrbDesc.side] at hij
  change (Matrix.reindex e.symm e.symm (Matrix.fromBlocks 1 (Matrix.of X.toAdd) 0 1)) i j = 0
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
  rcases hi : e i with i' | i' <;> rcases hj : e j with j' | j' <;> simp_all <;> exact absurd hij (by decide)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem charpoly_conj_sep {K ι : Type} [Field K] [Fintype ι] [DecidableEq ι] (γ c : GL ι K)
    (h : (γ : Matrix ι ι K).charpoly.Separable) : ((c⁻¹ * γ * c : GL ι K) : Matrix ι ι K).charpoly.Separable := by
  rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj']
  exact h

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem conj_props {K : Type} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [MeasurableSpace K]
    {ι : Type} [Fintype ι] [DecidableEq ι] (f : GL ι K → ℂ) (d : GL ι K)
    (hlc : IsLocallyConstant f) (hcs : HasCompactSupport f)
    (hyp : ∀ (a b : ℕ) (e : ι ≃ Fin a ⊕ Fin b), 0 < a → 0 < b → ∀ (μ : Measure (Fin a → Fin b → K)), μ.IsAddHaarMeasure →
      ∀ u : (Fin a → Fin b → K) → GL ι K,
        (∀ X, (u X : Matrix ι ι K) = Matrix.reindex e.symm e.symm (Matrix.fromBlocks 1 (Matrix.of X) 0 1)) →
        ∀ g h : GL ι K, ∫ X, f (g * (h⁻¹ * u X * h)) ∂μ = 0) :
    IsLocallyConstant (fun g => f (d * g * d⁻¹)) ∧ HasCompactSupport (fun g => f (d * g * d⁻¹)) ∧
    ∀ (a b : ℕ) (e : ι ≃ Fin a ⊕ Fin b), 0 < a → 0 < b → ∀ (μ : Measure (Fin a → Fin b → K)), μ.IsAddHaarMeasure →
      ∀ g h : GL ι K, ∫ X, (fun g => f (d * g * d⁻¹)) (g * (h⁻¹ * GlobalTheory.OrbDesc.uGL e X * h)) ∂μ = 0 := by
  have hcont : Continuous (fun g : GL ι K => d * g * d⁻¹) := (continuous_const.mul continuous_id).mul continuous_const
  refine ⟨hlc.comp_continuous hcont, ?_, ?_⟩
  · have : (fun g => f (d * g * d⁻¹)) = f ∘ (Homeomorph.mulRight d⁻¹) ∘ (Homeomorph.mulLeft d) := by
      funext g; simp
    rw [this]
    exact (hcs.comp_homeomorph _).comp_homeomorph _
  · intro a b e ha hb μ hμ g h
    have := hyp a b e ha hb μ hμ (GlobalTheory.OrbDesc.uGL e) (fun X => rfl) (d * g * d⁻¹) (h * d⁻¹)
    have hX : ∀ X, d * (g * (h⁻¹ * GlobalTheory.OrbDesc.uGL e X * h)) * d⁻¹ =
        d * g * d⁻¹ * ((h * d⁻¹)⁻¹ * GlobalTheory.OrbDesc.uGL e X * (h * d⁻¹)) := fun X => by group
    simp only [hX]
    exact this

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Reduce the equality to equality of the corresponding arguments. Chain the equalities or inequalities of the calculation.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the hypotheses and the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Reduce the equality to equality of the corresponding arguments.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Rewrite the hypotheses and the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Reduce the claim to the hypotheses of an applicable result.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. Rewrite the hypotheses and the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Consider separately whether the proposition holds or fails. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem twOrbU_eq_zero_of_cusp : ∀ (K : Type) [Field K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K] [MeasurableSpace K] [BorelSpace K]
  (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (f : GL ι K → ℂ), IsLocallyConstant f → HasCompactSupport f →
  (∀ (a b : ℕ) (e : ι ≃ Fin a ⊕ Fin b), 0 < a → 0 < b → ∀ (μ : Measure (Fin a → Fin b → K)), μ.IsAddHaarMeasure →
    ∀ u : (Fin a → Fin b → K) → GL ι K,
      (∀ X, (u X : Matrix ι ι K) = Matrix.reindex e.symm e.symm (Matrix.fromBlocks 1 (Matrix.of X) 0 1)) →
      ∀ g h : GL ι K, ∫ X, f (g * (h⁻¹ * u X * h)) ∂μ = 0) →
  ∀ γ : GL ι K, (γ : Matrix ι ι K).charpoly.Separable → ¬ Irreducible (γ : Matrix ι ι K).charpoly →
  ∀ (K0 K1 : Subgroup (GL ι K)), IsOpen (K0 : Set (GL ι K)) → IsCompact (K0 : Set (GL ι K)) →
    IsOpen (K1 : Set (GL ι K)) → IsCompact (K1 : Set (GL ι K)) →
    (∀ k ∈ K0, ∀ k' ∈ K0, ∀ g, f (k * g * k') = f g) →
    GlobalTheory.LKLoc.twOrbU (MonoidHom.id (GL ι K)) K0 γ (GlobalTheory.BCT.twCent (MonoidHom.id (GL ι K)) γ ⊓ K1) f = 0 := by
  intro K _ _ _ _ _ _ ι _ _ _ f hlc hcs hyp γ hsep hirr K0 K1 hK0o hK0c hK1o hK1c hbi
  obtain ⟨a, b, e, ha, hb, c, hT⟩ := GlobalTheory.T.exists_conj_centralizer_le_blockDiagonalLevi K ι γ hsep hirr
  set T := GlobalTheory.BCT.twCent (MonoidHom.id (GL ι K)) γ with hTdef
  set γ' := c⁻¹ * γ * c with hγ'
  have hsep' : (γ' : Matrix ι ι K).charpoly.Separable := charpoly_conj_sep γ c hsep
  have hcomm : ∀ s ∈ T, ∀ t ∈ T, s * t = t * s := fun s hs t ht => GlobalTheory.T.centralizer_separable_commutative K ι γ s t hsep hs ht
  have hleft : ∀ t ∈ T, ∀ x, (fun x => f (x⁻¹ * γ * x)) (t * x) = (fun x => f (x⁻¹ * γ * x)) x := by
    intro t ht x
    have ht' : t * γ = γ * t := ht
    simp only
    congr 1
    calc (t * x)⁻¹ * γ * (t * x) = x⁻¹ * (t⁻¹ * (t * γ)) * x := by rw [ht']; group
      _ = x⁻¹ * γ * x := by group
  have hright : ∀ l ∈ K0, ∀ x, (fun x => f (x⁻¹ * γ * x)) (x * l) = (fun x => f (x⁻¹ * γ * x)) x := by
    intro l hl x
    simp only
    rw [← hbi l⁻¹ (K0.inv_mem hl) l hl (x⁻¹ * γ * x)]
    congr 1; group
  rw [twOrbU_eq_dsum K0 _ γ f hbi, GlobalTheory.T.doubleCosetVolumeWeightedSum_conj _ T K0 (T ⊓ K1) _ c⁻¹ hcomm hleft hright, twCent_conj γ c]
  set T' := GlobalTheory.BCT.twCent (MonoidHom.id (GL ι K)) γ'
  set K0' := K0.map (MulAut.conj c⁻¹).toMonoidHom with hK0'
  set Ψ : GL ι K → ℂ := fun x => (fun x => f (x⁻¹ * γ * x)) (c⁻¹⁻¹ * x * c⁻¹) with hΨdef
  have hΨ : ∀ x, Ψ x = f (c * (x⁻¹ * γ' * x) * c⁻¹) := by
    intro x; simp only [hΨdef, hγ']; congr 1; group
  set P := blockPar (K := K) e
  have hTP : T' ≤ P := hT.trans inf_le_left
  have hcomm' : ∀ s ∈ T', ∀ t ∈ T', s * t = t * s := fun s hs t ht => GlobalTheory.T.centralizer_separable_commutative K ι γ' s t hsep' hs ht
  have hleft' : ∀ t ∈ T', ∀ x, Ψ (t * x) = Ψ x := by
    intro t ht x
    have ht' : t * γ' = γ' * t := ht
    have e1 : (t * x)⁻¹ * γ' * (t * x) = x⁻¹ * γ' * x := by
      calc (t * x)⁻¹ * γ' * (t * x) = x⁻¹ * (t⁻¹ * (t * γ')) * x := by rw [ht']; group
        _ = x⁻¹ * γ' * x := by group
    rw [hΨ, hΨ, e1]
  have hright' : ∀ l ∈ K0', ∀ x, Ψ (x * l) = Ψ x := by
    intro l hl x
    obtain ⟨k, hk, rfl⟩ := hl
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hΨdef]
    rw [← hbi k⁻¹ (K0.inv_mem hk) k hk ((c⁻¹⁻¹ * x * c⁻¹)⁻¹ * γ * (c⁻¹⁻¹ * x * c⁻¹))]
    congr 1; group
  apply GlobalTheory.T.orbit_sum_vanishes_of_parabolic_sums _ T' P K0' _ Ψ hTP hcomm' hleft' hright'
  intro y
  set N := blockUni (K := K) e
  have hNP : N ≤ P := blockUni_le_blockPar e
  have hK' : IsOpen ((K0'.map (MulAut.conj y).toMonoidHom : Subgroup (GL ι K)) : Set (GL ι K)) ∧
      IsCompact ((K0'.map (MulAut.conj y).toMonoidHom : Subgroup (GL ι K)) : Set (GL ι K)) := by
    have h1 := conj_open_compact K0 c⁻¹ hK0o hK0c
    exact conj_open_compact K0' y h1.1 h1.2
  apply GlobalTheory.T.dsum_eq_zero_of_fibre_sums' _ T' P N (P ⊓ K0'.map (MulAut.conj y).toMonoidHom) _ _ hTP hNP inf_le_left
    (GlobalTheory.T.conj_mem_blockUpperUnipotentRadical K ι a b e) hcomm'
  · intro t ht x
    have : t * x ∈ P ↔ x ∈ P := ⟨fun h => by simpa using P.mul_mem (P.inv_mem (hTP ht)) h,
      fun h => P.mul_mem (hTP ht) h⟩
    rw [if_congr this rfl rfl, mul_assoc, hleft' t ht]
  · intro l hl x
    have : x * l ∈ P ↔ x ∈ P := ⟨fun h => by simpa using P.mul_mem h (P.inv_mem hl.1),
      fun h => P.mul_mem h hl.1⟩
    rw [if_congr this rfl rfl]
    split_ifs
    · obtain ⟨k, hk, hkl⟩ := hl.2
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hkl
      have : x * l * y = x * y * k := by rw [← hkl]; group
      rw [this, hright' k hk]
    · rfl
  · intro x hx
    simp only [if_neg hx]
  · exact GlobalTheory.T.relIndex_ne_zero_centralizer_parabolicCosetStabilizer K ι a b e γ' hT _ hK'.1 hK'.2
  · intro m hm
    set d := c * y⁻¹
    obtain ⟨hlc', hcs', hyp'⟩ := conj_props f d hlc hcs hyp
    have hbi' : ∀ k ∈ K0'.map (MulAut.conj y).toMonoidHom, ∀ k' ∈ K0'.map (MulAut.conj y).toMonoidHom, ∀ g,
        (fun g => f (d * g * d⁻¹)) (k * g * k') = (fun g => f (d * g * d⁻¹)) g := by
      rintro _ ⟨_, ⟨k0, hk0, rfl⟩, rfl⟩ _ ⟨_, ⟨k1, hk1, rfl⟩, rfl⟩ g
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [← hbi k0 hk0 k1 hk1 (d * g * d⁻¹)]
      congr 1
      simp only [d]
      group
    have hγ'T : γ' ∈ T' := (rfl : γ' * γ' = γ' * γ')
    have hγ''P : m⁻¹ * γ' * m ∈ P := P.mul_mem (P.mul_mem (P.inv_mem hm) (hTP hγ'T)) hm
    have hC2 := GlobalTheory.T.finsum_unipotentConj_eq_zero_of_constantTerm_zero K ι a b e _ hlc' hcs' (hyp' a b e ha hb) _ hK'.1 hK'.2 hbi' _ hγ''P
      (charpoly_conj_sep γ' m hsep')
    refine Eq.trans (finsum_congr fun q => ?_) hC2
    by_cases h1 : Quotient.out q ∈ N
    · have h2 : m * Quotient.out q ∈ P := P.mul_mem hm (hNP h1)
      rw [if_pos h1, if_pos h1]
      change (if m * Quotient.out q ∈ P then Ψ (m * Quotient.out q * y) else 0) = _
      rw [if_pos h2, hΨ]
      exact congrArg f (by simp only [d]; group)
    · rw [if_neg h1, if_neg h1]

end GlobalTheory.OrbDesc
