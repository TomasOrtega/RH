import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BadAtTopLevel
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsRepresentativeOfDeformationClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.LocalShareNumberBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BadAtTopLevelStatement

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
namespace GlobalTheory.CovTop
/- English proof (translation)
Introduce `hP hGr hG`. Establish `h1` using `_root_.GlobalTheory.T.deformation_class_has_representative hP hG`. Establish `h2` using `_root_.GlobalTheory.CovTop.LocShareNum.local_share_count_le_exp hP hGr`. Unfold `Lifts at h1 h2 ⊢`. Use `(h1.and h2).imp fun Fm CH _ h => ?_` and prove the remaining obligations.

Take `⟨⟨C1, -, e1⟩, ⟨C2, -, e2⟩⟩` from `h`. Take `⟨x0, e⟩` from `e1.and e2`. Use `⟨0, le_rfl, x0, fun x hx hle ι p hp i hi => ?_⟩` and prove the remaining obligations. Take `⟨a1, a2⟩` from `e x hx hle ι p hp`. Take `⟨Γ, _, _, V, _, _, _, π, s, ρ, Pb, lam, ψ, lamb, H, hS, hW, hl, hH, hfree, hT, hB⟩` from `a1 i hi`.

Take `⟨ψ₀, hψ₀, hsh⟩` from `a2 i`. Establish `hc : ∀ k, ∃ n : ℕ, EmbReg ρ ((H k).comap π) n ∧ (n : ℝ) * Nat.card ((H k).comap π) ≤ 1 * Nat.card (Pb.comap π) * Module.finrank ℂ (eig ρ (Pb.comap π) lamb)`. Introduce `k`. Take `⟨X, _, _, _, A, hf, hA, hpm⟩` from `hfree k`. Take `⟨n, hn, hn'⟩` from `embReg_of_free_permuted_summands ℂ Γ V X ρ _ hf A hA hpm`.

Establish `hle : Pb.comap π ≤ (H k).comap π` using `fun g hg => (hH k (π g)).2 fun kv _ => (hW.2.1 (π g)).1 hg kv`. Establish `h3` using `card_mul_finrank_eig_of_free ℂ Γ V X ρ _ hf A hA hpm (Pb.comap π) hle lamb`. Use `⟨n, hn, ?_⟩` and prove the remaining obligations. Rewrite using `[one_mul]`. Conclude with `(hn'.trans h3.symm).le` after adjusting the coercions.

Use `choose n hn hn' using hc`. Take `⟨S, hSb, hbd⟩` from `GlobalTheory.BadCount.bad_part_le_locShare (Fm.D x ι) Γ V π s hS ρ Pb lam ψ hW lamb hl H hH n 1 hn hn' ψ₀ hψ₀`. Establish `hs` using `hsh S hSb`. Unfold `BadAt`. Rewrite using `[hT, hB]`.

Establish `hr : (0 : ℝ) ≤ (Module.finrank ℂ (eig ρ (Pb.comap π) lamb) : ℝ)` using `Nat.cast_nonneg _`. Establish `hx` using `Real.exp_pos (-((Fm.L x ι).sc.x ^ ((Fm.L x ι).sc.ez / 7)))`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[one_mul]`. Conclude with `mul_le_mul_of_nonneg_right hs hr`.

Use `_ ≤ _ := by nlinarith`.
-/
theorem definite_bad_place_lift : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GreenCuspidal → Gram → Lifts fun Fm x _ ι p i _ _ => (i : ℕ) + 1 = (Fm.D x ι).R.m → BadAt p i := by
  intro hP hGr hG
  have h1 := _root_.GlobalTheory.T.deformation_class_has_representative hP hG
  have h2 := _root_.GlobalTheory.CovTop.LocShareNum.local_share_count_le_exp hP hGr
  unfold Lifts at h1 h2 ⊢
  refine (h1.and h2).imp fun Fm CH _ h => ?_
  obtain ⟨⟨C1, -, e1⟩, ⟨C2, -, e2⟩⟩ := h
  obtain ⟨x0, e⟩ := e1.and e2
  refine ⟨0, le_rfl, x0, fun x hx hle ι p hp i hi => ?_⟩
  obtain ⟨a1, a2⟩ := e x hx hle ι p hp
  obtain ⟨Γ, _, _, V, _, _, _, π, s, ρ, Pb, lam, ψ, lamb, H, hS, hW, hl, hH, hfree, hT, hB⟩ := a1 i hi
  obtain ⟨ψ₀, hψ₀, hsh⟩ := a2 i
  have hc : ∀ k, ∃ n : ℕ, EmbReg ρ ((H k).comap π) n ∧ (n : ℝ) * Nat.card ((H k).comap π) ≤
      1 * Nat.card (Pb.comap π) * Module.finrank ℂ (eig ρ (Pb.comap π) lamb) := by
    intro k
    obtain ⟨X, _, _, _, A, hf, hA, hpm⟩ := hfree k
    obtain ⟨n, hn, hn'⟩ := embReg_of_free_permuted_summands ℂ Γ V X ρ _ hf A hA hpm
    have hle : Pb.comap π ≤ (H k).comap π := fun g hg => (hH k (π g)).2 fun kv _ => (hW.2.1 (π g)).1 hg kv
    have h3 := card_mul_finrank_eig_of_free ℂ Γ V X ρ _ hf A hA hpm (Pb.comap π) hle lamb
    refine ⟨n, hn, ?_⟩
    rw [one_mul]
    exact_mod_cast (hn'.trans h3.symm).le
  choose n hn hn' using hc
  obtain ⟨S, hSb, hbd⟩ := GlobalTheory.BadCount.bad_part_le_locShare (Fm.D x ι) Γ V π s hS ρ Pb lam ψ hW lamb hl H hH n 1 hn hn' ψ₀ hψ₀
  have hs := hsh S hSb
  unfold BadAt
  rw [hT, hB]
  have hr : (0 : ℝ) ≤ (Module.finrank ℂ (eig ρ (Pb.comap π) lamb) : ℝ) := Nat.cast_nonneg _
  have hx := Real.exp_pos (-((Fm.L x ι).sc.x ^ ((Fm.L x ι).sc.ez / 7)))
  calc _ ≤ _ := hbd
    _ ≤ Real.exp (-((Fm.L x ι).sc.x ^ ((Fm.L x ι).sc.ez / 7))) * (Module.finrank ℂ (eig ρ (Pb.comap π) lamb) : ℝ) := by
        rw [one_mul]; exact mul_le_mul_of_nonneg_right hs hr
    _ ≤ _ := by nlinarith
end GlobalTheory.CovTop
end

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @_root_.GlobalTheory.CovTop.definite_bad_place_lift | exact _root_.GlobalTheory.CovTop.definite_bad_place_lift | (intros; apply _root_.GlobalTheory.CovTop.definite_bad_place_lift <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.exists_lift_at_definite_bad_places : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GreenCuspidal → Gram → Lifts fun Fm x _ ι p i _ _ => (i : ℕ) + 1 = (Fm.D x ι).R.m → BadAt p i := by
  first | exact @_root_.GlobalTheory.CovTop.definite_bad_place_lift | exact _root_.GlobalTheory.CovTop.definite_bad_place_lift | (intros; apply _root_.GlobalTheory.CovTop.definite_bad_place_lift <;> assumption)
end
