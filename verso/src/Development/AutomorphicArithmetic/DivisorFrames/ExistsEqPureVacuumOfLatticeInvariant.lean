import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzEqPureTensorOfFiniteSlicesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerFixedFunctionsProportionalOfSelfDualStatement
import Development.AutomorphicArithmetic.LocalEmbeddings.FinMatchDefs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaussianDatumFlippedFiniteTensorBigRoute
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewGramInrInl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalIdempotentCharacterValue
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeAtFinitePlaceEqSumSplitPlacePartsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergLatticeSelfDualEveryFinitePlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvFinMkPt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLocalDictionarySplitPlace

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model piW chrW unifAt latAtV At SInf)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Establish `h : evFin F v (⅟(2 : AF F)) * algebraMap F (Fv F v) (algebraMap (𝓞 F) F 2) = 1`. Rewrite using `[map_ofNat, map_ofNat, ← map_ofNat (evFin F v) 2, ← map_mul, invOf_mul_self, map_one]`. Establish `hv : Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F 2)) = 1`. Use `v.valuedAdicCompletion_eq_valuation' (K := F) (algebraMap (𝓞 F) F 2)` as an intermediate fact. Rewrite `this` using `[HeightOneSpectrum.valuation_of_algebraMap, (HeightOneSpectrum.intValuation_eq_one_iff).2 h2]`.

Conclude with `this`. Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers]`. Establish `h'` using `congrArg (Valued.v : v.adicCompletion F → _) h`. Rewrite `h'` using `[map_mul, map_one, hv, mul_one]`. Conclude with `h'.le`.
-/
private theorem invTwo_mem (v : HeightOneSpectrum (𝓞 F)) (h2 : (2 : 𝓞 F) ∉ v.asIdeal) :
    evFin F v (⅟(2 : AF F)) ∈ v.adicCompletionIntegers F := by
  have h : evFin F v (⅟(2 : AF F)) * algebraMap F (Fv F v) (algebraMap (𝓞 F) F 2) = 1 := by
    rw [map_ofNat, map_ofNat, ← map_ofNat (evFin F v) 2, ← map_mul, invOf_mul_self, map_one]
  have hv : Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F 2)) = 1 := by
    have := v.valuedAdicCompletion_eq_valuation' (K := F) (algebraMap (𝓞 F) F 2)
    rw [HeightOneSpectrum.valuation_of_algebraMap, (HeightOneSpectrum.intValuation_eq_one_iff).2 h2] at this
    exact this
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have h' := congrArg (Valued.v : v.adicCompletion F → _) h
  rw [map_mul, map_one, hv, mul_one] at h'
  exact h'.le

/- English proof (translation)
Proceed by induction on `hγ using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨a, ha, hav, x, hx, y, hy, rfl⟩` from `hz`. Use `AddSubgroup.subset_closure ⟨c * a, fun u hu => ?_, ?_, x, hx, y, hy, smul_smul _ _ _⟩` and prove the remaining obligations. Rewrite using `[smul_eq_mul, mul_left_comm, ← smul_eq_mul u a, ha u hu, mul_zero]`.

Rewrite using `[map_mul]`. Conclude with `mul_mem hc hav`. Consider the case `zero => rw [smul_zero]`. Conclude with `zero_mem _`. Consider the case `add z z' _ _ h h' => rw [smul_add]`.

Conclude with `add_mem h h'`. Consider the case `neg z _ h => rw [smul_neg]`. Conclude with `neg_mem h`.
-/
private theorem smul_mem_lat {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (v : HeightOneSpectrum (𝓞 F)) {c : AF F}
    (hc : evFin F v c ∈ v.adicCompletionIntegers F) {γ : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)}
    (hγ : γ ∈ latAtV X W v) : c • γ ∈ latAtV X W v := by
  induction hγ using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hav, x, hx, y, hy, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨c * a, fun u hu => ?_, ?_, x, hx, y, hy, smul_smul _ _ _⟩
    · rw [smul_eq_mul, mul_left_comm, ← smul_eq_mul u a, ha u hu, mul_zero]
    · rw [map_mul]; exact mul_mem hc hav
  | zero => rw [smul_zero]; exact zero_mem _
  | add z z' _ _ h h' => rw [smul_add]; exact add_mem h h'
  | neg z _ h => rw [smul_neg]; exact neg_mem h

/- English proof (translation)
Establish `h0` using `GlobalTheory.SwapAtPlace.one_sub_smul hγ`. Rewrite `h0` using `[sub_smul, one_smul, sub_eq_zero]`. Establish `ht' : ∀ i j, piW t (γ i j) = 0` using `fun i j => congrFun (congrFun ht i) j`. Establish `hσ : (t.comp σ).comp σ = t` using `GlobalTheory.AdelicU.comp_conj_conj h t`. Unfold `GlobalTheory.WeilM.hTens`.

Use `Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun l _ => ?_` and prove the remaining obligations. Establish `h3 : GlobalTheory.LatVac.liftV v (1 : Fv F v) • γ i j = γ i j` using `(congrFun (congrFun h0 i) j).symm`. Use `GlobalTheory.SwapAtPlace.eq_zero_of_piW h t ?_ ?_ ?_` and prove the remaining obligations. Rewrite using `[← smul_mul_assoc, ← smul_mul_assoc, ← smul_mul_assoc, h3]`. Rewrite using `[map_mul, map_mul, map_mul, ht', zero_mul, zero_mul, zero_mul]`.

Rewrite using `[map_mul, GlobalTheory.SplitDict.piW_cA, hσ, ht', mul_zero]`.
-/
private theorem hTens_half {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {n d : ℕ} {v : HeightOneSpectrum (𝓞 F)}
    (t : E →ₐ[F] Fv F v) (JA : Matrix (Fin n) (Fin n) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E))
    (JB : Matrix (Fin d) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)) {γ : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)}
    (hγ : At (evFin F v) γ) (ht : γ.map (piW t) = 0) :
    GlobalTheory.WeilM.hTens (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) JA JB γ γ = 0 := by
  have h0 := GlobalTheory.SwapAtPlace.one_sub_smul hγ
  rw [sub_smul, one_smul, sub_eq_zero] at h0
  have ht' : ∀ i j, piW t (γ i j) = 0 := fun i j => congrFun (congrFun ht i) j
  have hσ : (t.comp σ).comp σ = t := GlobalTheory.AdelicU.comp_conj_conj h t
  unfold GlobalTheory.WeilM.hTens
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ =>
    Finset.sum_eq_zero fun l _ => ?_
  have h3 : GlobalTheory.LatVac.liftV v (1 : Fv F v) • γ i j = γ i j := (congrFun (congrFun h0 i) j).symm
  refine GlobalTheory.SwapAtPlace.eq_zero_of_piW h t ?_ ?_ ?_
  · rw [← smul_mul_assoc, ← smul_mul_assoc, ← smul_mul_assoc, h3]
  · rw [map_mul, map_mul, map_mul, ht', zero_mul, zero_mul, zero_mul]
  · rw [map_mul, GlobalTheory.SplitDict.piW_cA, hσ, ht', mul_zero]

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n d X W M r s r' s' hB hX hW hG Ψ hΨ h2 hh`. Establish `hstd` using `hB.std`. Take `⟨f, hf⟩` from `GlobalTheory.T.adelicSchwartz_eq_pureTensor_of_finite_slices M.vac (fun v => (hG.vac v).2.1) hG.std Ψ hΨ fun v y hy => by`. Set `gen : Set (Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E))` to `{γ | (∃ γ' ∈ latAtV X W v, γ = 2 • γ') ∨ (γ ∈ latAtV X W v ∧ ∃ t : E →ₐ[F] Fv F v, γ.map (piW t) = 0)}`. Establish `hsub : ∀ γ ∈ gen, γ ∈ latAtV X W v`.

Introduce and unpack `γ (⟨γ', h, rfl⟩ | ⟨h, -⟩)`. Conclude with `nsmul_mem h 2`. Conclude with `h`. Establish `hgen : latAtV X W v ≤ AddSubgroup.closure gen`. Introduce `γ hγ`.

Distinguish the cases in `hv : ∀ w : HeightOneSpectrum (𝓞 E), ¬ Formalism.UG.IsInertAt F E v w`. Use `haveI := hB.unram`. Take `⟨t⟩` from `GlobalTheory.SplitDict.nonempty_emb hB.cm v hv`. Take `⟨γ₁, h₁, γ₂, h₂, rfl, e₁, e₂⟩` from `GlobalTheory.T.tensorLatticeAtFinitePlace_eq_sum_splitPlace_parts hB.cm X W v t γ hγ`. Conclude with `add_mem (AddSubgroup.subset_closure (.inr ⟨h₁, _, e₁⟩)) (AddSubgroup.subset_closure (.inr ⟨h₂, _, e₂⟩))`.

Take `⟨w, hw⟩` from `not_forall_not.1 hv`. Use `AddSubgroup.subset_closure (.inl ⟨⅟(2 : AF F) • γ, smul_mem_lat X W v (invTwo_mem v (hB.inert v w hw).1) hγ, ?_⟩)` and prove the remaining obligations. Rewrite using `[two_nsmul, ← add_smul, invOf_two_add_invOf_two, one_smul]`. Take `⟨c, hc0, hc⟩` from `GlobalTheory.LatBound.locCo_latAtV_bounded X W v M.co hX.lat hW.lat`. Take `⟨a, ha⟩` from `GlobalTheory.T.schroedinger_fixed_functions_proportional_of_selfDual v (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.VacAny.continuous_psiV hstd.1 v) (GlobalTheory.PsiNontriv.psiAt_ne_one B.ψ hstd v) (GlobalTheory.LatVac.locCo M.co v '' gen) ((latAtV X W v).map (GlobalTheory.La …`.

Introduce and unpack `_ ⟨γ, hγ, rfl⟩`. Use `GlobalTheory.BigDat.schr_eq_of_acts _ _ (GlobalTheory.VacLine.at_latAtV (hsub γ hγ)) (hG.vac v).1 ?_` and prove the remaining obligations. Take `⟨-, -, θ, -, hθ⟩` from `hG.vac v`. Establish `h1` using `hθ γ (hsub γ hγ)`. Establish `h3 : B.ψ (⅟(2 : AF F) * GlobalTheory.WeilM.symp (R` using `AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) (θ : E)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F W.J) γ γ) = 1 := by`.

Break down `hγ with ⟨γ', hγ', rfl⟩ | ⟨hγ, t, ht⟩` into its components or cases. Conclude with `GlobalTheory.BigDat.VacFix.psi_double _ B X W _ _ _ _ hB hX hW v θ γ' hγ'`. Unfold `GlobalTheory.WeilM.symp`. Rewrite using `[hTens_half hB.cm t _ _ (GlobalTheory.VacLine.at_latAtV hγ) ht, mul_zero, map_zero, mul_zero, AddChar.map_zero_eq_one]`. Rewrite using `[h3, one_smul] at h1)` and apply the resulting hypothesis.

Use the proof step `(by`. Introduce and unpack `_ ⟨γ, hγ, rfl⟩`. Use `GlobalTheory.BigDat.schr_slice _ _ (GlobalTheory.VacLine.at_latAtV (hsub γ hγ)) ?_ hy` and prove the remaining obligations. Break down `hγ with ⟨γ', hγ', rfl⟩ | ⟨hγ, t, ht⟩` into its components or cases. Conclude with `h2 v γ' hγ'`.

Conclude with `hh v t γ hγ ht) (hG.vac v).2.1`. Conclude with `⟨a, congrFun ha⟩`. Conclude with `⟨f, hf⟩`.
-/
theorem UpperTheory.exists_eq_pure_vacuum_of_lattice_invariant :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
        (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s →
        W.IsSkew σ B r' s' → M.IsGood B.ψ →
        ∀ Ψ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d), (∀ v, ∀ γ ∈ latAtV X W v, M.co.rho B.ψ (2 • γ) Ψ = Ψ) →
        (∀ (v : HeightOneSpectrum (𝓞 F)) (t : E →ₐ[F] Fv F v), ∀ γ ∈ latAtV X W v, γ.map (piW t) = 0 → M.co.rho B.ψ γ Ψ = Ψ) →
        ∃ g : SInf F (Fin n × Fin d), Ψ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g M.vac := by
  intro F E _ _ _ _ _ σ B n d X W M r s r' s' hB hX hW hG Ψ hΨ h2 hh
  have hstd := hB.std
  obtain ⟨f, hf⟩ := GlobalTheory.T.adelicSchwartz_eq_pureTensor_of_finite_slices M.vac (fun v => (hG.vac v).2.1) hG.std Ψ hΨ fun v y hy => by
    let gen : Set (Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)) :=
      {γ | (∃ γ' ∈ latAtV X W v, γ = 2 • γ') ∨ (γ ∈ latAtV X W v ∧ ∃ t : E →ₐ[F] Fv F v, γ.map (piW t) = 0)}
    have hsub : ∀ γ ∈ gen, γ ∈ latAtV X W v := by
      rintro γ (⟨γ', h, rfl⟩ | ⟨h, -⟩)
      · exact nsmul_mem h 2
      · exact h
    have hgen : latAtV X W v ≤ AddSubgroup.closure gen := by
      intro γ hγ
      by_cases hv : ∀ w : HeightOneSpectrum (𝓞 E), ¬ Formalism.UG.IsInertAt F E v w
      · haveI := hB.unram
        obtain ⟨t⟩ := GlobalTheory.SplitDict.nonempty_emb hB.cm v hv
        obtain ⟨γ₁, h₁, γ₂, h₂, rfl, e₁, e₂⟩ := GlobalTheory.T.tensorLatticeAtFinitePlace_eq_sum_splitPlace_parts hB.cm X W v t γ hγ
        exact add_mem (AddSubgroup.subset_closure (.inr ⟨h₁, _, e₁⟩)) (AddSubgroup.subset_closure (.inr ⟨h₂, _, e₂⟩))
      · obtain ⟨w, hw⟩ := not_forall_not.1 hv
        refine AddSubgroup.subset_closure (.inl ⟨⅟(2 : AF F) • γ, smul_mem_lat X W v (invTwo_mem v (hB.inert v w hw).1) hγ, ?_⟩)
        rw [two_nsmul, ← add_smul, invOf_two_add_invOf_two, one_smul]
    obtain ⟨c, hc0, hc⟩ := GlobalTheory.LatBound.locCo_latAtV_bounded X W v M.co hX.lat hW.lat
    obtain ⟨a, ha⟩ := GlobalTheory.T.schroedinger_fixed_functions_proportional_of_selfDual v (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.VacAny.continuous_psiV hstd.1 v)
      (GlobalTheory.PsiNontriv.psiAt_ne_one B.ψ hstd v) (GlobalTheory.LatVac.locCo M.co v '' gen)
      ((latAtV X W v).map (GlobalTheory.LatVac.locCo M.co v)) c
      (by rw [← AddMonoidHom.map_closure]; exact AddSubgroup.map_mono hgen) hc0
      (GlobalTheory.LatVac.DualLoc.map_selfDual v M.co B.ψ _ (fun γ hγ => GlobalTheory.VacLine.at_latAtV hγ)
        (GlobalTheory.T.heisenbergLattice_selfDual_every_finitePlace F E σ B n d X W r s r' s' hB hX hW v))
      (by rintro _ ⟨γ, hγ, rfl⟩; exact hc γ hγ) (M.vac v)
      (fun ξ => Ψ (y + fun k => GlobalTheory.LatVac.liftV v (ξ k)))
      (by
        rintro _ ⟨γ, hγ, rfl⟩
        refine GlobalTheory.BigDat.schr_eq_of_acts _ _ (GlobalTheory.VacLine.at_latAtV (hsub γ hγ)) (hG.vac v).1 ?_
        obtain ⟨-, -, θ, -, hθ⟩ := hG.vac v
        have h1 := hθ γ (hsub γ hγ)
        have h3 : B.ψ (⅟(2 : AF F) * GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ)
            (inclR (F := F) (AF F) (θ : E)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J)
            (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F W.J) γ γ) = 1 := by
          rcases hγ with ⟨γ', hγ', rfl⟩ | ⟨hγ, t, ht⟩
          · exact GlobalTheory.BigDat.VacFix.psi_double _ B X W _ _ _ _ hB hX hW v θ γ' hγ'
          · unfold GlobalTheory.WeilM.symp
            rw [hTens_half hB.cm t _ _ (GlobalTheory.VacLine.at_latAtV hγ) ht, mul_zero, map_zero, mul_zero,
              AddChar.map_zero_eq_one]
        rwa [h3, one_smul] at h1)
      (by
        rintro _ ⟨γ, hγ, rfl⟩
        refine GlobalTheory.BigDat.schr_slice _ _ (GlobalTheory.VacLine.at_latAtV (hsub γ hγ)) ?_ hy
        rcases hγ with ⟨γ', hγ', rfl⟩ | ⟨hγ, t, ht⟩
        · exact h2 v γ' hγ'
        · exact hh v t γ hγ ht) (hG.vac v).2.1
    exact ⟨a, congrFun ha⟩
  exact ⟨f, hf⟩
