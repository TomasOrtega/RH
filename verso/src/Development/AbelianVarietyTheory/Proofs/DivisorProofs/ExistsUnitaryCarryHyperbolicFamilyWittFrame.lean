import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ParabolicLeviDecomposition
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllipticTraceFromModelStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalFramePairsDifferIsometryUnitriangular
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WittExtensionTheorem
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TruncKer GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt GlobalTheory.Chamber GlobalTheory.Cusp
open scoped TensorProduct

namespace GlobalTheory.WittCarry

/- English proof (translation)
Introduce `D V Φ a ha x x' hli h1 h2 h3`. Establish `hs : ∀ u w, star (V.hT u w) = V.hT w u` using `fun u w => V.herm.eq u w`. Establish `hn : ∀ u, (∀ w, V.hT u w = 0) → u = 0` using `fun u hu => V.nondeg.1 u hu`. Establish `sw : ∀ u w, V.hD u w = star (V.hD w u)` using `fun u w => (hs u w).symm`. Establish `hcast : ∀ i j : Fin a, (Fin.castLE ha i = Fin.castLE ha j) ↔ i = j` using `fun i j => (Fin.castLE_injective ha).eq_iff`.

Set `e' : Fin a → V.V` to `fun i => Φ.e (Fin.castLE ha i)`. Set `f' : Fin a → V.V` to `fun i => Φ.f (Fin.castLE ha i)`. Establish `hli' : LinearIndependent D.host.E (Sum.elim e' f')`. Use `LinearIndependent.of_pairwise_dual_eq_zero_one _ (Sum.elim (fun i => V.hT (f' i)) (fun i => V.hT (e' i))) ?_ ?_` and prove the remaining obligations. Introduce and unpack `(i | i) (j | j) hij`.

Establish `: Fin.castLE ha j ≠ Fin.castLE ha i` using `fun h => hij (congrArg Sum.inl ((hcast j i).1 h).symm)`. Conclude with `(Φ.ef _ _).trans (if_neg this)`. Conclude with `Φ.ff _ _`. Conclude with `Φ.ee _ _`. Establish `: Fin.castLE ha i ≠ Fin.castLE ha j` using `fun h => hij (congrArg Sum.inr ((hcast i j).1 h)) show V.hD (f' j) (e' i) = 0`.

Rewrite using `[sw]`. Use `show star (V.hD (Φ.e (Fin.castLE ha i)) (Φ.f (Fin.castLE ha j))) = 0`. Rewrite using `[Φ.ef, if_neg this, star_zero]`. Introduce and unpack `(i | i)`. Conclude with `(Φ.ef _ _).trans (if_pos rfl)`.

Use `show V.hD (f' i) (e' i) = 1`. Rewrite using `[sw]`. Use `show star (V.hD (Φ.e (Fin.castLE ha i)) (Φ.f (Fin.castLE ha i))) = 1`. Rewrite using `[Φ.ef, if_pos rfl, star_one]`. Establish `hg : ∀ p q, V.hT (Sum.elim x x' p) (Sum.elim x x' q) = V.hT (Sum.elim e' f' p) (Sum.elim e' f' q)`.

Introduce and unpack `(i | i) (j | j)`. Use `show V.hD (x j) (x i) = V.hD (e' j) (e' i)`. Rewrite using `[h1, Φ.ee]`. Use `show V.hD (x' j) (x i) = V.hD (f' j) (e' i)`. Rewrite using `[sw, sw (f' j)]`.

Use `show star (V.hD (x i) (x' j)) = star (V.hD (Φ.e (Fin.castLE ha i)) (Φ.f (Fin.castLE ha j)))`. Rewrite using `[h3, Φ.ef]`. Simplify using `only [hcast]`. Use `show V.hD (x j) (x' i) = V.hD (e' j) (f' i) show _ = V.hD (Φ.e (Fin.castLE ha j)) (Φ.f (Fin.castLE ha i))`. Rewrite using `[h3, Φ.ef]`.

Simplify using `only [hcast]`. Use `show V.hD (x' j) (x' i) = V.hD (f' j) (f' i)`. Rewrite using `[h2, Φ.ff]`. Take `⟨g, hgB, hgv⟩` from `GlobalTheory.LocOver.WittFrames.exists_isom_of_gram witt_extension_theorem V.hT hs hn _ _ hli hli' hg`. Set `M : Matrix (Fin V.rank) (Fin V.rank) D.host.E` to `LinearMap.toMatrix V.frame V.frame g.toLinearMap`.

Set `N : Matrix (Fin V.rank) (Fin V.rank) D.host.E` to `LinearMap.toMatrix V.frame V.frame g.symm.toLinearMap`. Establish `hMN : M * N = 1`. Rewrite using `[← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_one V.frame]`. Use `congr 1`. Use extensionality with `y`.

Simplify using the standard rewrite rules. Establish `hNM : N * M = 1`. Rewrite using `[← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_one V.frame]`. Use `congr 1`. Use extensionality with `y`.

Simplify using the standard rewrite rules. Set `U : GL (Fin V.rank) D.host.E` to `⟨M, N, hMN, hNM⟩`. Establish `hrat : ∀ γ : GF V, γ.1 = U → GlobalTheory.Cusp.ratAct D.sp.cm V γ = g.toLinearMap` using `fun γ h => by show Matrix.toLin V.frame V.frame γ.1.1 = _`. Rewrite using `[h]`. Conclude with `Matrix.toLin_toMatrix _ _ _`.

Use `⟨⟨U, ?_⟩, fun i => ?_⟩` and prove the remaining obligations. Use `show Formalism.UG.cT _ M * V.gram * M = V.gram`. Use function extensionality and compare the values at `i j`. Establish `hexp : ∀ k, g (V.frame k) = ∑ l, M l k • V.frame l` using `fun k => by conv_lhs => rw [← V.frame.sum_repr (g (V.frame k))]`. Simplify using `[M, LinearMap.toMatrix_apply]`.

Rewrite using `[show V.gram i j = V.hT (V.frame i) (V.frame j) from rfl, ← hgB, hexp, hexp]`. Simplify using `only [Formalism.UG.cT, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]`. Establish `hσ : ∀ z, (D.sp.cm.sig : D.host.E →+* D.host.E) z = star z` using `fun z => rfl`. Simplify using `only [hσ, starRingEnd_apply, HSpace.gram, RingHom.id_apply]`. Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hrat _ rfl]`. Conclude with `⟨hgv (Sum.inl i), hgv (Sum.inr i)⟩`.
-/
theorem exists_GF_carry_hyperbolic : ∀ {D : D7} {V : HSp D} (Φ : WittFrame V) {a : ℕ} (ha : a ≤ wittIndex V) (x x' : Fin a → V.V), LinearIndependent D.host.E (Sum.elim x x') → (∀ i j, V.hD (x i) (x j) = 0) → (∀ i j, V.hD (x' i) (x' j) = 0) → (∀ i j, V.hD (x i) (x' j) = if i = j then 1 else 0) → ∃ g : GF V, ∀ i, GlobalTheory.Cusp.ratAct D.sp.cm V g (x i) = Φ.e (Fin.castLE ha i) ∧ GlobalTheory.Cusp.ratAct D.sp.cm V g (x' i) = Φ.f (Fin.castLE ha i) := by
  intro D V Φ a ha x x' hli h1 h2 h3
  classical
  have hs : ∀ u w, star (V.hT u w) = V.hT w u := fun u w => V.herm.eq u w
  have hn : ∀ u, (∀ w, V.hT u w = 0) → u = 0 := fun u hu => V.nondeg.1 u hu
  have sw : ∀ u w, V.hD u w = star (V.hD w u) := fun u w => (hs u w).symm
  have hcast : ∀ i j : Fin a, (Fin.castLE ha i = Fin.castLE ha j) ↔ i = j :=
    fun i j => (Fin.castLE_injective ha).eq_iff
  let e' : Fin a → V.V := fun i => Φ.e (Fin.castLE ha i)
  let f' : Fin a → V.V := fun i => Φ.f (Fin.castLE ha i)
  have hli' : LinearIndependent D.host.E (Sum.elim e' f') := by
    refine LinearIndependent.of_pairwise_dual_eq_zero_one _
      (Sum.elim (fun i => V.hT (f' i)) (fun i => V.hT (e' i))) ?_ ?_
    · rintro (i | i) (j | j) hij
      · have : Fin.castLE ha j ≠ Fin.castLE ha i := fun h => hij (congrArg Sum.inl ((hcast j i).1 h).symm)
        exact (Φ.ef _ _).trans (if_neg this)
      · exact Φ.ff _ _
      · exact Φ.ee _ _
      · have : Fin.castLE ha i ≠ Fin.castLE ha j := fun h => hij (congrArg Sum.inr ((hcast i j).1 h))
        show V.hD (f' j) (e' i) = 0
        rw [sw]; show star (V.hD (Φ.e (Fin.castLE ha i)) (Φ.f (Fin.castLE ha j))) = 0
        rw [Φ.ef, if_neg this, star_zero]
    · rintro (i | i)
      · exact (Φ.ef _ _).trans (if_pos rfl)
      · show V.hD (f' i) (e' i) = 1
        rw [sw]; show star (V.hD (Φ.e (Fin.castLE ha i)) (Φ.f (Fin.castLE ha i))) = 1
        rw [Φ.ef, if_pos rfl, star_one]
  have hg : ∀ p q, V.hT (Sum.elim x x' p) (Sum.elim x x' q) = V.hT (Sum.elim e' f' p) (Sum.elim e' f' q) := by
    rintro (i | i) (j | j)
    · show V.hD (x j) (x i) = V.hD (e' j) (e' i)
      rw [h1, Φ.ee]
    · show V.hD (x' j) (x i) = V.hD (f' j) (e' i)
      rw [sw, sw (f' j)]
      show star (V.hD (x i) (x' j)) = star (V.hD (Φ.e (Fin.castLE ha i)) (Φ.f (Fin.castLE ha j)))
      rw [h3, Φ.ef]; simp only [hcast]
    · show V.hD (x j) (x' i) = V.hD (e' j) (f' i)
      show _ = V.hD (Φ.e (Fin.castLE ha j)) (Φ.f (Fin.castLE ha i))
      rw [h3, Φ.ef]; simp only [hcast]
    · show V.hD (x' j) (x' i) = V.hD (f' j) (f' i)
      rw [h2, Φ.ff]
  obtain ⟨g, hgB, hgv⟩ := GlobalTheory.LocOver.WittFrames.exists_isom_of_gram witt_extension_theorem V.hT hs hn _ _ hli hli' hg
  let M : Matrix (Fin V.rank) (Fin V.rank) D.host.E := LinearMap.toMatrix V.frame V.frame g.toLinearMap
  let N : Matrix (Fin V.rank) (Fin V.rank) D.host.E := LinearMap.toMatrix V.frame V.frame g.symm.toLinearMap
  have hMN : M * N = 1 := by
    rw [← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_one V.frame]; congr 1; ext y; simp
  have hNM : N * M = 1 := by
    rw [← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_one V.frame]; congr 1; ext y; simp
  let U : GL (Fin V.rank) D.host.E := ⟨M, N, hMN, hNM⟩
  have hrat : ∀ γ : GF V, γ.1 = U → GlobalTheory.Cusp.ratAct D.sp.cm V γ = g.toLinearMap := fun γ h => by
    show Matrix.toLin V.frame V.frame γ.1.1 = _
    rw [h]; exact Matrix.toLin_toMatrix _ _ _
  refine ⟨⟨U, ?_⟩, fun i => ?_⟩
  · show Formalism.UG.cT _ M * V.gram * M = V.gram
    funext i j
    have hexp : ∀ k, g (V.frame k) = ∑ l, M l k • V.frame l := fun k => by
      conv_lhs => rw [← V.frame.sum_repr (g (V.frame k))]
      simp [M, LinearMap.toMatrix_apply]
    rw [show V.gram i j = V.hT (V.frame i) (V.frame j) from rfl, ← hgB, hexp, hexp]
    simp only [Formalism.UG.cT, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, map_sum, map_smulₛₗ,
      LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
    have hσ : ∀ z, (D.sp.cm.sig : D.host.E →+* D.host.E) z = star z := fun z => rfl
    simp only [hσ, starRingEnd_apply, HSpace.gram, RingHom.id_apply]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  · rw [hrat _ rfl]
    exact ⟨hgv (Sum.inl i), hgv (Sum.inr i)⟩

end GlobalTheory.WittCarry
