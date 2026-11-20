import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.AdjointEta
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.CyclicCharacterEigen.ToIdeleSq
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ClosedHeckeCosets.IsClosedSmall
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanEqTopOfIrreducibleOverAlgClosed
import GroundTheory.GlobalFields.AnalyticClassNumber.DirichletHeckeCorrespondence
import GroundTheory.GlobalFields.AnalyticClassNumber.DirichletHeckeLocal

open NumberField IsDedekindDomain Polynomial UpperTheory.V UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Sd.EG GroundTheory.Global GroundTheory.LocalField GroundTheory.Global.DirichletHecke
open GroundTheory.Automorphic.GodementSection (localChar coe_localChar)

/- English proof (translation)
Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. By extensionality, compare the relevant components. Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.

Establish an intermediate fact. A detailed English derivation is pending.
-/
private theorem coset_trace {k Γ : Type} [Field k] [IsAlgClosed k] [Group Γ] (r : Γ →* GL (Fin 2) k) (H : Subgroup Γ)
    (hirr : IsIrr (r.comp H.subtype)) (t : Γ)
    (ht : ∀ h ∈ H, (r (t * h) : Matrix (Fin 2) (Fin 2) k).trace = 0) : False := by
  obtain ⟨-, -, hmin⟩ := hirr
  let R : H →* Matrix (Fin 2) (Fin 2) k := (Units.coeHom _).comp (r.comp H.subtype)
  have hspan := GlobalTheory.BurnsideMonoid.span_matrix_eq_top_of_isAlgClosed R fun W hW => hmin W le_top fun s v hv => hW s v hv
  let L : Matrix (Fin 2) (Fin 2) k →ₗ[k] k :=
    (Matrix.traceLinearMap (Fin 2) k k) ∘ₗ LinearMap.mulLeft k (r t : Matrix (Fin 2) (Fin 2) k)
  have hL : Submodule.span k (Set.range R) ≤ LinearMap.ker L := by
    rw [Submodule.span_le]
    rintro _ ⟨h, rfl⟩
    have := ht h h.2
    rw [map_mul, Units.val_mul] at this
    exact this
  rw [hspan] at hL
  have hz : (r t : Matrix (Fin 2) (Fin 2) k) = 0 := by
    ext i j
    have h := hL (Submodule.mem_top (x := Matrix.single j i (1 : k)))
    have h2 : ((r t : Matrix (Fin 2) (Fin 2) k) * Matrix.single j i (1 : k)).trace = 0 := h
    simpa [Matrix.trace_mul_single] using h2
  have := (r t).isUnit.ne_zero
  exact this hz

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Evaluate the numerical expressions.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
private theorem loc_val (η : HeckeCharacter ℚ) (v : Ad3.Pl) (h : IsUnramifiedChar (localChar η v)) :
    ((localChar η v (unifUnit (Ad3.Qv v)) : ℂˣ) : ℂ) = (η (IdeleClassGroup.mk ℚ (IdeleGroup.finiteEmbedding v (uniformizer v))) : ℂ) := by
  have h1 : ord ((uniformizer v : (Ad3.Qv v)ˣ) : Ad3.Qv v) = 1 := by
    rw [Ad3P.DihedralUnramifiedPlaces.ord_eq v (Units.ne_zero _), valued_uniformizer, WithZero.log_exp, neg_neg]
  have hord : ord (((unifUnit (Ad3.Qv v)) * (uniformizer v)⁻¹ : (Ad3.Qv v)ˣ) : Ad3.Qv v) = 0 := by
    rw [ord_units_mul, ord_units_inv, h1, ord_unifUnit]
    norm_num
  have h2 := isUnramifiedChar_iff.1 h _ hord
  rw [map_mul, map_inv, mul_inv_eq_one] at h2
  rw [h2, coe_localChar, HeckeCharacter.localComponent_apply, HeckeCharacter.toIdele_apply]

/- English proof (translation)
Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
private theorem hecke_ne_one {M : ℕ} [NeZero M] {ψ : DirichletCharacter ℂ M} (h : heckeCharacter ψ ≠ 1) : ψ ≠ 1 := by
  rintro rfl
  refine h ?_
  ext x
  rw [coe_heckeCharacter_apply, ← coe_unitsMod, MulChar.one_apply (Units.isUnit _)]
  rfl

/- English proof (translation)
Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Establish an intermediate fact. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the indicated hypotheses using the stated equalities. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

A detailed English derivation is pending.
-/
theorem UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.notDih :
    UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.NotDih := by
  rintro l _ Ω _ _ _ ι k N _ χ g ρ hc hirr hrep ⟨η, h1, h2, hev⟩
  obtain ⟨M, _, ψ, -, rfl⟩ := exists_heckeCharacter_eq (isOfFinOrder_iff_pow_eq_one.2 ⟨2, two_pos, h2⟩)
  set δ : G ℚ Ω →* (Qbar l)ˣ := Chr.dirG ℚ Ω (ψ.ringHomComp ι.symm.toRingHom) with hδ
  have hδc : Continuous fun s => (δ s : Qbar l) := dirG_cont _

  obtain ⟨t, ht⟩ : ∃ t, (δ t : Qbar l) ≠ 1 := by
    obtain ⟨u, hu⟩ : ∃ u : (ZMod M)ˣ, ψ u ≠ 1 := by
      by_contra hall
      push_neg at hall
      exact hecke_ne_one h1 (MulChar.ext fun u => by rw [hall u, MulChar.one_apply (Units.isUnit _)])
    obtain ⟨t, rfl⟩ := (Chr.clsOnto Ω M).1 u
    refine ⟨t, fun h => hu ?_⟩
    rw [dirG_val] at h
    apply ι.symm.injective
    rw [map_one]
    exact h

  have hM : ∀ᶠ w : Ad3.Pl in Filter.cofinite, ¬ normV w ∣ M :=
    Filter.eventually_cofinite.2 (by simpa using fin_dvd (NeZero.ne M))
  have hS := Filter.eventually_cofinite.1 (hrep.and (hev.and hM))
  have hdense := GlobalTheory.Published.ChebotarevDegreeOne.dense (F := ℚ) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne' hS
  have c1 : Continuous fun s : G ℚ Ω => (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)).trace * ((δ s : Qbar l) - 1) :=
    (Units.continuous_val.comp hc).matrix_trace.mul (hδc.sub continuous_const)
  have key : ∀ s, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)).trace * ((δ s : Qbar l) - 1) = 0 := fun s => by
    refine (isClosed_eq c1 continuous_const).closure_subset_iff.2 ?_ (hdense s)
    rintro σ ⟨w, hw, -, A, hA, hσ⟩
    simp only [Set.mem_setOf_eq, not_not] at hw
    obtain ⟨hr, ⟨hu, hv⟩, hwM⟩ := hw
    have hAq := (over_iff hA _).2 dvd_rfl
    have hp := normV_prime w
    obtain ⟨htr, -⟩ := tr_det ι _ ((hr A hA).2 σ hσ)
    show _ = (0 : Qbar l)
    rcases hv with h0 | h0
    · have hpe : RationalSymbol.prime w = normV w := by
        rw [← absNorm_asIdeal, Ad3P.DihedralUnramifiedPlaces.normV_eq, Ad3.pOf]
      have h3 : ¬ RationalSymbol.prime w ∣ M := by rwa [hpe]
      have h4 := (loc_val _ w hu).symm.trans (congrArg Units.val h0)
      rw [coe_heckeCharacter_uniformizer _ h3, hpe] at h4
      have h5 : (δ σ : Qbar l) = 1 := by
        rw [hδ, dirG_frob _ hp hAq hwM hσ]
        show ι.symm (ψ _) = 1
        rw [h4, Units.val_one]
        exact map_one _
      rw [h5, sub_self, mul_zero]
    · have h0' : g.a (normV w) = 0 := by rw [Ad3P.DihedralUnramifiedPlaces.normV_eq]; exact h0
      rw [htr, h0', map_zero, zero_mul]
  have hker : IsOpen (δ.ker : Set (G ℚ Ω)) := dirG_open _
  refine coset_trace ρ δ.ker (hirr _ hker) t fun h hh => ?_
  have h3 := key (t * h)
  have h4 : (δ (t * h) : Qbar l) = δ t := by rw [map_mul, MonoidHom.mem_ker.1 hh, mul_one]
  rw [h4] at h3
  exact (mul_eq_zero.1 h3).resolve_right (sub_ne_zero.2 ht)
