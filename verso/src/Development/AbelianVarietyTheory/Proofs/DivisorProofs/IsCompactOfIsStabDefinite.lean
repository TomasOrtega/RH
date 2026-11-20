import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsRationalDblCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAdeleE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativelyCompactStabilizer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedAdelicLatticeClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarOfIsCompact
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cont

namespace GlobalTheory.DefDoubling

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hcm B n X hdef K hK`. Take `⟨r, s, hX⟩ : ∃ r s : ℕ, X.IsHerm σ B r s` from `hdef.elim (fun h => ⟨_, _, h⟩) (fun h => ⟨_, _, h⟩)`. Establish `e : K = GlobalTheory.StabHaar.stabK B X`. Use extensionality with `g`. Rewrite using `[hK g, GlobalTheory.StabHaar.isStab_stabK B X g]`.

Substitute `e` using the available equality. Establish `hJ : X.J.det ≠ 0`. Introduce `h0`. Take `⟨w⟩ : Nonempty (InfinitePlace F)` from `inferInstance`. Establish `hd : (X.J.map (B.emb w).1).det = 0`.

Rewrite using `[← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]`. Take `⟨v, hv, hMv⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 hd`. Establish `hx : star v ≠ 0` using `by simpa using hv`. Use `(hX.cartan w).2.2 (star v) hx` as an intermediate fact. Rewrite `this` using `[star_star, hMv, dotProduct_zero, Complex.zero_re]`.

Conclude with `lt_irrefl _ this`. Use `choose Rw hRw using fun w => GlobalTheory.T.cartan_commuting_isometries_bounded _ _ (hX.cartan w)`. Use `set R : ℝ := ∑ w, |Rw w|`. Establish `hlat` using `hX.lat`. Take `⟨Cf, hCf, hCfe⟩` from `GlobalTheory.StabCompact.exists_compact_entries F E X.L hlat.fg hlat.span_eq_top`.

Take `⟨K, hK, hKe⟩` from `GlobalTheory.T.bounded_norm_compact_preimage F E σ hcm B.emb Cf hCf R`. Take `⟨C, hC, hCe⟩` from `GlobalTheory.T.unitary_group_bounded_entries_compact F E σ n X.J hJ K hK`. Establish `hsub : ((GlobalTheory.StabHaar.stabK B X : Subgroup (UA σ X.J)) : Set (UA σ X.J)) ⊆ C`. Use `fun g hg => hCe g fun i j => hKe _ ?_ ?_` and prove the remaining obligations. Conclude with `hCfe _ (GlobalTheory.T.lattice_completion_stable_base_change F E n X (mat g) fun z hz => (hg.2 z hz).1) i j`.

Introduce `w`. Establish `hu : ((mat g).map (piInf (B.emb w))).transpose * X.J.map (B.emb w).1 * ((mat g).map (piInf (B.emb w))).map star = X.J.map (B.emb w).1`. Establish `h2` using `congrArg (fun Y : Matrix (Fin n) (Fin n) (AE F E) => Y.map (piInf (B.emb w))) (show (mat g).transpose * incM F X.J * (mat g).map (cA σ) = incM F X.J from g.2)`. Simplify using `only [Matrix.map_mul] at h2`. Establish `e1 : (incM F X.J).map (piInf (B.emb w)) = X.J.map (B.emb w).1`.

Use extensionality with `i j`. Simplify using `[incM, piInf, compInf, inclR, infEmb_tmul]`. Establish `e2 : ((mat g).map (cA σ)).map (piInf (B.emb w)) = ((mat g).map (piInf (B.emb w))).map star`. Use extensionality with `i j`. Simplify using `only [Matrix.map_apply]`.

Conclude with `GlobalTheory.StabBounded.cA_piInf hcm _ _`. Rewrite `h2` using `[e1]`. Rewrite using `[← e2, ← Matrix.transpose_map]`. Conclude with `h2`. Establish `hb` using `hRw w _ hu (hg.1 w).eq i j`.

Combine the equalities or inequalities in the displayed calculation. Conclude with `hC.of_isClosed_subset (GlobalTheory.StabHaar.isClosed_stabK B X (GlobalTheory.LatHatClosed.isClosed_latHat F E n X hX.lat)) hsub`.
-/
theorem isCompact_of_isStab_definite : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E}, IsCMExt F E σ → ∀ {B : Base F E} {n : ℕ} {X : Spc F E n}, (X.IsHerm σ B n 0 ∨ X.IsHerm σ B 0 n) →
    ∀ {K : Subgroup (UA σ X.J)}, IsStab B K → IsCompact (K : Set (UA σ X.J)) := by
  intro F E _ _ _ _ _ σ hcm B n X hdef K hK
  obtain ⟨r, s, hX⟩ : ∃ r s : ℕ, X.IsHerm σ B r s := hdef.elim (fun h => ⟨_, _, h⟩) (fun h => ⟨_, _, h⟩)
  have e : K = GlobalTheory.StabHaar.stabK B X := by
    ext g
    rw [hK g, GlobalTheory.StabHaar.isStab_stabK B X g]
  subst e
  have hJ : X.J.det ≠ 0 := by
    intro h0
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    have hd : (X.J.map (B.emb w).1).det = 0 := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
    obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hd
    have hx : star v ≠ 0 := by simpa using hv
    have := (hX.cartan w).2.2 (star v) hx
    rw [star_star, hMv, dotProduct_zero, Complex.zero_re] at this
    exact lt_irrefl _ this
  choose Rw hRw using fun w => GlobalTheory.T.cartan_commuting_isometries_bounded _ _ (hX.cartan w)
  set R : ℝ := ∑ w, |Rw w|
  have hlat := hX.lat
  obtain ⟨Cf, hCf, hCfe⟩ := GlobalTheory.StabCompact.exists_compact_entries F E X.L hlat.fg hlat.span_eq_top
  obtain ⟨K, hK, hKe⟩ := GlobalTheory.T.bounded_norm_compact_preimage F E σ hcm B.emb Cf hCf R
  obtain ⟨C, hC, hCe⟩ := GlobalTheory.T.unitary_group_bounded_entries_compact F E σ n X.J hJ K hK
  have hsub : ((GlobalTheory.StabHaar.stabK B X : Subgroup (UA σ X.J)) : Set (UA σ X.J)) ⊆ C := by
    refine fun g hg => hCe g fun i j => hKe _ ?_ ?_
    · exact hCfe _ (GlobalTheory.T.lattice_completion_stable_base_change F E n X (mat g) fun z hz => (hg.2 z hz).1) i j
    · intro w
      have hu : ((mat g).map (piInf (B.emb w))).transpose * X.J.map (B.emb w).1 * ((mat g).map (piInf (B.emb w))).map star = X.J.map (B.emb w).1 := by
        have h2 := congrArg (fun Y : Matrix (Fin n) (Fin n) (AE F E) => Y.map (piInf (B.emb w)))
          (show (mat g).transpose * incM F X.J * (mat g).map (cA σ) = incM F X.J from g.2)
        simp only [Matrix.map_mul] at h2
        have e1 : (incM F X.J).map (piInf (B.emb w)) = X.J.map (B.emb w).1 := by
          ext i j
          simp [incM, piInf, compInf, inclR, infEmb_tmul]
        have e2 : ((mat g).map (cA σ)).map (piInf (B.emb w)) = ((mat g).map (piInf (B.emb w))).map star := by
          ext i j
          simp only [Matrix.map_apply]
          exact GlobalTheory.StabBounded.cA_piInf hcm _ _
        rw [e1] at h2
        rw [← e2, ← Matrix.transpose_map]
        exact h2
      have hb := hRw w _ hu (hg.1 w).eq i j
      calc ‖piInf (B.emb w) (mat g i j)‖ = ‖(mat g).map (piInf (B.emb w)) i j‖ := rfl
        _ ≤ Rw w := hb
        _ ≤ |Rw w| := le_abs_self _
        _ ≤ R := Finset.single_le_sum (f := fun w => |Rw w|) (fun _ _ => abs_nonneg _) (Finset.mem_univ w)
  exact hC.of_isClosed_subset (GlobalTheory.StabHaar.isClosed_stabK B X (GlobalTheory.LatHatClosed.isClosed_latHat F E n X hX.lat)) hsub

end GlobalTheory.DefDoubling
