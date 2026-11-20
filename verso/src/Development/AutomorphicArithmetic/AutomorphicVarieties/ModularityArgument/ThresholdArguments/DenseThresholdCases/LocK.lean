import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SphericalDecomposition.SphOfWit
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidueFlagPoints.CycIne
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.NewformTwistNorms.WeilDeligneFrobeniusEigenvalueOfFullFlag
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TLocCompC
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TWDAbove
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TSatLoc

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
open UpperTheory.Zero.LLC UpperTheory.V.Z.Win UpperTheory.V.Z.Kato UpperTheory.V.Z.Kato.WeilSphericalRecords
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Introduce `P hRec hC hPR hW hSph hFrob K Ω _ _ _ _ _ _ l _ hl ι e he r π hc hreg hpol hatt w A κ hlw hA hex hplain`. Take `⟨hfl, hI⟩` from `hex`. Establish `hAl : A.valuation (l : Ω) < 1` using `by simpa using (hA _).2 hlw`. Set `m : Fin 2 → ℤ` to `![(e : ℤ), -(e : ℤ)]`. Establish `hκm : ∀ i (s : ↥(Dec (F` using `K) A)), (s : G K Ω) ∈ Ine (F := K) A → κ i s = cycBar K Ω l s ^ m i * (1 : G K Ω →* (Qbar l)ˣ) s := by`.

Introduce `i s hs`. Use `fin_cases i`. Simplify `(hI s hs).1` using `[m]`. Simplify `(hI s hs).2` using `[m]`. Establish `hor : ∀ i j, κ i ≠ κ j * (cycBar K Ω l).comp (Dec (F` using `K) A).subtype := by`.

Introduce `i j hij`. Apply the tactic sequence `obtain ⟨s, hs, hne⟩ := UpperTheory.V.Ws.Pt.cycIne K Ω l A hAl (m i - m j - 1) (by fin_cases i <;> fin_cases j <;> simp [m] <;> omega)`. Establish `h1` using `congrArg (fun f => f ⟨s, Ine_le_Dec A hs⟩) hij`. Simplify using `only [MonoidHom.mul_apply, MonoidHom.comp_apply, Subgroup.coe_subtype] at h1`. Rewrite `h1` using `[hκm i _ hs, hκm j _ hs]`.

Apply `hne` to reduce the goal to its premises. Simplify using `only [MonoidHom.one_apply, mul_one] at h1`. Rewrite using `[zpow_sub, zpow_sub, h1, zpow_one]`. Use `group`. Establish `hfa : FlagAt 1 m r A κ` using `⟨fun _ => 1, fun _ _ _ => rfl, hfl, hκm⟩`.

Take `⟨⟨σ, hσ⟩, hiso⟩` from `_root_.UpperTheory.V.Af.local_comp_complex_of_printed_results P K 2 π w`. Take `⟨rc, hrc⟩` from `hRec K Ω A w hA`. Take `⟨t, ht⟩` from `hW K 2 (by norm_num) π`. Take `⟨hpl, htor, hmono⟩` from `hPR K Ω A w hA rc hrc 2 π t (ht w hplain) σ hσ`. Establish `hgd : Gd (rc (algNorm σ))` using `⟨htor, hmono⟩`.

Take `⟨j, L0, hj0, hB⟩` from `GlobalTheory.PlaceBridge.exists_locBridge l K Ω w A hlw hA`. Take `⟨Bw, hBj, -⟩` from `hB L0 le_rfl`. Establish `hj : Induces Bw` using `fun x => by rw [hBj]; exact hj0 x`. Take `⟨HT, -, hcomp⟩` from `hC K Ω l ι 2 (by norm_num) r π hc hreg hpol hatt`. Take `⟨hpst, hwd⟩` from `((hcomp w σ hσ).1 A hA rc hrc).2 _ Bw hj hgd`.

Establish `hlev : IsLevelWD 1 2 (rc (algNorm σ))`. Rewrite using `[← hwd]`. Conclude with `_root_.UpperTheory.V.Af.weil_deligne_above_of_printed_results P K Ω l hl ι 2 1 le_rfl m r hc w A hA _ Bw hj κ hfa hpst (Or.inl hor)`. Establish `hK : HasFixed σ.ρ (GlobalTheory.LFun.KGL w 2)` using `hSph K Ω A w hA rc hrc 2 σ hpl hlev`. Establish `hsat` using `_root_.UpperTheory.V.Af.satake_local_of_printed_results P K 2 w σ`.

Use `⟨?_, fun B hBs τ hτ => ?_⟩` and prove the remaining obligations. Take `⟨B, hB'⟩` from `hsat.1 hK`. Conclude with `⟨B, (hsat.2 _ π.finPart (hiso σ hσ) B).2 hB'⟩`. Establish `hBσ` using `(hsat.2 _ π.finPart (hiso σ hσ) B).1 hBs`. Set `φ : ↥(Weil hA)` to `⟨τ, mem_Weil_of_isFrob hA hτ⟩`.

Establish `hd : deg φ = 1` using `deg_eq_one_iff.2 hτ`. Establish `h1` using `GlobalTheory.T.weilDeligne_frobenius_eigenvalue_of_full_flag K Ω l ι 2 1 le_rfl m r hc w A hA _ Bw hj κ hfa hpst 0 φ hd`. Rewrite `h1` using `[hwd]`. Take `⟨b, hb, hzb⟩` from `hFrob K Ω A w hA rc hrc 2 σ B hpl hBσ φ hd _ h1`. Use `⟨b, hb, ?_⟩` and prove the remaining obligations.

Conclude with `hzb`.
-/
theorem UpperTheory.V.Z.Kato.WeilSphericalRecords.local_k_of_printed_rec_compat_sph_frob :
    _root_.UpperTheory.V.Af.Hypotheses' → RecTExists → CompatT → PlainRec → WinPt → RecSph → RecFrob → LocK := by
  intro P hRec hC hPR hW hSph hFrob K Ω _ _ _ _ _ _ l _ hl ι e he r π hc hreg hpol hatt w A κ hlw hA hex hplain
  obtain ⟨hfl, hI⟩ := hex
  have hAl : A.valuation (l : Ω) < 1 := by simpa using (hA _).2 hlw
  let m : Fin 2 → ℤ := ![(e : ℤ), -(e : ℤ)]
  have hκm : ∀ i (s : ↥(Dec (F := K) A)), (s : G K Ω) ∈ Ine (F := K) A →
      κ i s = cycBar K Ω l s ^ m i * (1 : G K Ω →* (Qbar l)ˣ) s := by
    intro i s hs
    fin_cases i
    · simpa [m] using (hI s hs).1
    · simpa [m] using (hI s hs).2
  have hor : ∀ i j, κ i ≠ κ j * (cycBar K Ω l).comp (Dec (F := K) A).subtype := by
    intro i j hij
    obtain ⟨s, hs, hne⟩ := UpperTheory.V.Ws.Pt.cycIne K Ω l A hAl (m i - m j - 1) (by
      fin_cases i <;> fin_cases j <;> simp [m] <;> omega)
    have h1 := congrArg (fun f => f ⟨s, Ine_le_Dec A hs⟩) hij
    simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, Subgroup.coe_subtype] at h1
    rw [hκm i _ hs, hκm j _ hs] at h1
    apply hne
    simp only [MonoidHom.one_apply, mul_one] at h1
    rw [zpow_sub, zpow_sub, h1, zpow_one]
    group
  have hfa : FlagAt 1 m r A κ := ⟨fun _ => 1, fun _ _ _ => rfl, hfl, hκm⟩
  obtain ⟨⟨σ, hσ⟩, hiso⟩ := _root_.UpperTheory.V.Af.local_comp_complex_of_printed_results P K 2 π w
  obtain ⟨rc, hrc⟩ := hRec K Ω A w hA
  obtain ⟨t, ht⟩ := hW K 2 (by norm_num) π
  obtain ⟨hpl, htor, hmono⟩ := hPR K Ω A w hA rc hrc 2 π t (ht w hplain) σ hσ
  have hgd : Gd (rc (algNorm σ)) := ⟨htor, hmono⟩
  obtain ⟨j, L0, hj0, hB⟩ := GlobalTheory.PlaceBridge.exists_locBridge l K Ω w A hlw hA
  obtain ⟨Bw, hBj, -⟩ := hB L0 le_rfl
  have hj : Induces Bw := fun x => by rw [hBj]; exact hj0 x
  obtain ⟨HT, -, hcomp⟩ := hC K Ω l ι 2 (by norm_num) r π hc hreg hpol hatt
  obtain ⟨hpst, hwd⟩ := ((hcomp w σ hσ).1 A hA rc hrc).2 _ Bw hj hgd
  have hlev : IsLevelWD 1 2 (rc (algNorm σ)) := by
    rw [← hwd]
    exact _root_.UpperTheory.V.Af.weil_deligne_above_of_printed_results P K Ω l hl ι 2 1 le_rfl m r hc w A hA _ Bw hj κ hfa hpst (Or.inl hor)
  have hK : HasFixed σ.ρ (GlobalTheory.LFun.KGL w 2) := hSph K Ω A w hA rc hrc 2 σ hpl hlev
  have hsat := _root_.UpperTheory.V.Af.satake_local_of_printed_results P K 2 w σ
  refine ⟨?_, fun B hBs τ hτ => ?_⟩
  · obtain ⟨B, hB'⟩ := hsat.1 hK
    exact ⟨B, (hsat.2 _ π.finPart (hiso σ hσ) B).2 hB'⟩
  · have hBσ := (hsat.2 _ π.finPart (hiso σ hσ) B).1 hBs
    let φ : ↥(Weil hA) := ⟨τ, mem_Weil_of_isFrob hA hτ⟩
    have hd : deg φ = 1 := deg_eq_one_iff.2 hτ
    have h1 := GlobalTheory.T.weilDeligne_frobenius_eigenvalue_of_full_flag K Ω l ι 2 1 le_rfl m r hc w A hA _ Bw hj κ hfa hpst 0 φ hd
    rw [hwd] at h1
    obtain ⟨b, hb, hzb⟩ := hFrob K Ω A w hA rc hrc 2 σ B hpl hBσ φ hd _ h1
    refine ⟨b, hb, ?_⟩
    exact hzb
end
end
