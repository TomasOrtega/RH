import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnSourceIffOfDensity
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniqueComplexPointUnder
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiprojectivePrimeEqPointIdeal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PointIdealMultiprojectivePrime
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SpecializesIffPointIdealLeStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLiftClosedImmersionOfDense
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)

noncomputable section

namespace GlobalTheory.CompanionTheory.MPDict.UnderSub

open GroundTheory.Heights₂.Heights.HilbertSamuel.BlockImageInverse (mConeMap_of_isMultiHomog)
open GlobalTheory.CompanionTheory.MPDict.Onto GlobalTheory.CompanionTheory.MPDict.Under

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

/- English proof (translation)
Unfold `GlobalTheory.TuplePoint.point GlobalTheory.ProjSpace.pt`. Use `congr 1`.
-/
theorem point_eq_pt {N : ℕ} (t : Fin (N + 1) → ℂ) (ht : t ≠ 0) (hu : Ideal.span (Set.range t) = ⊤) :
    GlobalTheory.TuplePoint.point ℤ t ht = GlobalTheory.ProjSpace.pt (Int.castRingHom ℂ) t hu := by
  unfold GlobalTheory.TuplePoint.point GlobalTheory.ProjSpace.pt
  congr 1

/- English proof (translation)
Take `⟨S, hS, hPS⟩` from `hP`. Establish `h0` using `hz.2`. Rewrite using `[hPS, Ideal.span_le]`. Introduce `f hf`. Take `⟨a, ha⟩` from `hS f hf`.

Establish `e : aeval z f = 0`. Use `h0 f (hPS ▸ Ideal.subset_span hf)` as an intermediate fact. Rewrite using `[MvPolynomial.aeval_def, MvPolynomial.eval₂_eq_eval_map]`. Simplify using `using this`. Rewrite using `[SetLike.mem_coe, Geo.mCoordIdeal, RingHom.mem_ker, mConeMap_of_isMultiHomog _ ha, e, C_0, mul_zero]`.
-/
theorem le_mCoordIdeal_of_mem_mcPts {P : Ideal (Geo.MRing (Bk n))} (hP : Geo.IsMultiHomogIdeal P)
    {z : (Σ k, Bk n k) → ℂ} (hz : z ∈ mcPts P) : P ≤ Geo.mCoordIdeal z := by
  obtain ⟨S, hS, hPS⟩ := hP
  have h0 := hz.2
  rw [hPS, Ideal.span_le]
  intro f hf
  obtain ⟨a, ha⟩ := hS f hf
  have e : aeval z f = 0 := by
    have := h0 f (hPS ▸ Ideal.subset_span hf)
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq_eval_map]
    simpa using this
  rw [SetLike.mem_coe, Geo.mCoordIdeal, RingHom.mem_ker, mConeMap_of_isMultiHomog _ ha, e, C_0, mul_zero]

/- English proof (translation)
Establish `ht` using `blockVec_ne_zero hz'`. Establish `hu : ∀ k, Ideal.span (Set.range fun i : Bk n k => z ⟨k, i⟩) = ⊤` using `fun k => by`. Take `⟨i, hi⟩` from `hz' k`. Conclude with `Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨i, rfl⟩) (isUnit_iff_ne_zero.2 hi)`. Set `a : ∀ k, Sp ℂ ⟶ PSpace ℤ (n k)` to `fun k => GlobalTheory.ProjSpace.pt (Int.castRingHom ℂ) (fun i : Bk n k => z ⟨k, i⟩) (hu k)`.

Set `g : Sp ℂ ⟶ MP ℤ m n` to `w.1`. Establish `hg : ∀ k, g ≫ prB n k = a k` using `fun k => (comp_of_isUnder ht hz' H k).trans (point_eq_pt _ _ (hu k))`. Set `p : Sp ℂ` to `IsLocalRing.closedPoint ℂ`. Set `x : MP ℤ m n` to `g p`. Set `θ : ℂ →+* (Sp ℂ).residueField p` to `((Sp ℂ).evaluation ⊤ p trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom`.

Set `ρ : (MP ℤ m n).residueField x →+* (Sp ℂ).residueField p` to `(g.residueFieldMap p).hom`. Establish `key : ∀ (k : Fin (m + 1)) (j : Bk n k), θ (z ⟨k, ptChart x k⟩) * ρ (ptCoord x ⟨k, j⟩) = θ (z ⟨k, j⟩)`. Introduce `k j`. Establish `hx : g p ∈ blockChart n k (ptChart x k)` using `mem_ptChart x k`. Establish `hW : g ⁻¹ᵁ blockChart n k (ptChart x k) ≤ a k ⁻¹ᵁ chart ℤ (n k) (ptChart x k)`.

Rewrite using `[← hg k]`. Conclude with `le_of_eq rfl`. Establish `e1 : ρ (ptCoord x ⟨k, j⟩) = ((Sp ℂ).evaluation _ p hx).hom (pullRatio (a k) (g ⁻¹ᵁ blockChart n k (ptChart x k)) (ptChart x k) hW j)`. Use `(Scheme.evaluation_naturality_apply g p hx _).trans ?_` and prove the remaining obligations. Use `congrArg _ ?_` and prove the remaining obligations.

Use `appLE_pullRatio (φ := prB n k) (W := blockChart n k (ptChart x k)) (i := ptChart x k) (hi := le_rfl) (j := j) g (T := g ⁻¹ᵁ blockChart n k (ptChart x k)) le_rfl` as an intermediate fact. Conclude with `this.trans (pullRatio_of_eq (hg k) _ _)`. Establish `e2` using `pullRatio_pt_mul (Int.castRingHom ℂ) (fun i : Bk n k => z ⟨k, i⟩) (hu k) (W := g ⁻¹ᵁ blockChart n k (ptChart x k)) (ptChart x k) j hW`. Establish `e3 : ∀ b : ℂ, ((Sp ℂ).evaluation _ p hx).hom (fnOn (g ⁻¹ᵁ blockChart n k (ptChart x k)) b) = θ b` using `fun b => evaluation_resG' le_top p hx _`. Use `congrArg ((Sp ℂ).evaluation _ p hx).hom e2` as an intermediate fact.

Rewrite `this` using `[map_mul, e3, e3]`. Rewrite using `[e1, mul_comm]`. Conclude with `this`. Establish `hne : ∀ k, θ (z ⟨k, ptChart x k⟩) ≠ 0`. Introduce `k`.

Use `(map_ne_zero θ).2 fun h0 => ?_` and prove the remaining obligations. Establish `hx : p ∈ a k ⁻¹ᵁ chart ℤ (n k) (ptChart x k)`. Establish `: g p ∈ blockChart n k (ptChart x k)` using `mem_ptChart x k`. Rewrite using `[← hg k]`. Conclude with `this`.

Rewrite `hx` using `[GlobalTheory.ProjSpace.pt_preimage_chart, GlobalTheory.ProjSpace.mem_spOpen]`. Conclude with `hx (h0 ▸ Ideal.zero_mem _)`. Express the relevant statement in the definitionally equal form `ptIdeal x = _`. Rewrite using `[ptIdeal, ← mCoordIdeal_comp_ringHom ρ, ← mCoordIdeal_comp_ringHom θ z, ← mCoordIdeal_blockScale (fun k => θ (z ⟨k, ptChart x k⟩)) hne]`. Use `congr 1`.

Use function extensionality and compare the values at `q`. Take `⟨k, j⟩` from `q`. Conclude with `key k j`.
-/
theorem ptIdeal_of_isUnder {z : (Σ k, Bk n k) → ℂ} (hz' : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0)
    {w : CxPts (mpStr ℤ m n) σ₀} (H : IsUnder w z) :
    ptIdeal (w.1 (IsLocalRing.closedPoint ℂ)) = Geo.mCoordIdeal z := by
  have ht := blockVec_ne_zero hz'
  have hu : ∀ k, Ideal.span (Set.range fun i : Bk n k => z ⟨k, i⟩) = ⊤ := fun k => by
    obtain ⟨i, hi⟩ := hz' k
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨i, rfl⟩) (isUnit_iff_ne_zero.2 hi)
  let a : ∀ k, Sp ℂ ⟶ PSpace ℤ (n k) := fun k =>
    GlobalTheory.ProjSpace.pt (Int.castRingHom ℂ) (fun i : Bk n k => z ⟨k, i⟩) (hu k)
  let g : Sp ℂ ⟶ MP ℤ m n := w.1
  have hg : ∀ k, g ≫ prB n k = a k := fun k =>
    (comp_of_isUnder ht hz' H k).trans (point_eq_pt _ _ (hu k))
  let p : Sp ℂ := IsLocalRing.closedPoint ℂ
  let x : MP ℤ m n := g p
  let θ : ℂ →+* (Sp ℂ).residueField p :=
    ((Sp ℂ).evaluation ⊤ p trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  let ρ : (MP ℤ m n).residueField x →+* (Sp ℂ).residueField p := (g.residueFieldMap p).hom
  have key : ∀ (k : Fin (m + 1)) (j : Bk n k),
      θ (z ⟨k, ptChart x k⟩) * ρ (ptCoord x ⟨k, j⟩) = θ (z ⟨k, j⟩) := by
    intro k j
    have hx : g p ∈ blockChart n k (ptChart x k) := mem_ptChart x k
    have hW : g ⁻¹ᵁ blockChart n k (ptChart x k) ≤ a k ⁻¹ᵁ chart ℤ (n k) (ptChart x k) := by
      rw [← hg k]
      exact le_of_eq rfl
    have e1 : ρ (ptCoord x ⟨k, j⟩) = ((Sp ℂ).evaluation _ p hx).hom
        (pullRatio (a k) (g ⁻¹ᵁ blockChart n k (ptChart x k)) (ptChart x k) hW j) := by
      refine (Scheme.evaluation_naturality_apply g p hx _).trans ?_
      refine congrArg _ ?_
      have := appLE_pullRatio (φ := prB n k) (W := blockChart n k (ptChart x k)) (i := ptChart x k)
        (hi := le_rfl) (j := j) g (T := g ⁻¹ᵁ blockChart n k (ptChart x k)) le_rfl
      exact this.trans (pullRatio_of_eq (hg k) _ _)
    have e2 := pullRatio_pt_mul (Int.castRingHom ℂ) (fun i : Bk n k => z ⟨k, i⟩) (hu k)
      (W := g ⁻¹ᵁ blockChart n k (ptChart x k)) (ptChart x k) j hW
    have e3 : ∀ b : ℂ, ((Sp ℂ).evaluation _ p hx).hom (fnOn (g ⁻¹ᵁ blockChart n k (ptChart x k)) b) = θ b :=
      fun b => evaluation_resG' le_top p hx _
    have := congrArg ((Sp ℂ).evaluation _ p hx).hom e2
    rw [map_mul, e3, e3] at this
    rw [e1, mul_comm]
    exact this
  have hne : ∀ k, θ (z ⟨k, ptChart x k⟩) ≠ 0 := by
    intro k
    refine (map_ne_zero θ).2 fun h0 => ?_
    have hx : p ∈ a k ⁻¹ᵁ chart ℤ (n k) (ptChart x k) := by
      have : g p ∈ blockChart n k (ptChart x k) := mem_ptChart x k
      rw [← hg k]
      exact this
    rw [GlobalTheory.ProjSpace.pt_preimage_chart, GlobalTheory.ProjSpace.mem_spOpen] at hx
    exact hx (h0 ▸ Ideal.zero_mem _)
  change ptIdeal x = _
  rw [ptIdeal, ← mCoordIdeal_comp_ringHom ρ, ← mCoordIdeal_comp_ringHom θ z,
    ← mCoordIdeal_blockScale (fun k => θ (z ⟨k, ptChart x k⟩)) hne]
  congr 1
  funext q
  obtain ⟨k, j⟩ := q
  exact key k j

/- English proof (translation)
Introduce `m n X _ i _ z hz`. Take `⟨w, hw, -⟩` from `existsUnique_isUnder m n z hz.1`. Establish `hP : ptIdeal (i (genericPoint X)) ≤ ptIdeal (w.1 (IsLocalRing.closedPoint ℂ))`. Rewrite using `[ptIdeal_of_isUnder hz.1 hw]`. Conclude with `le_mCoordIdeal_of_mem_mcPts (isMultiProjPrime_ptIdeal m n _).2.1 hz`.

Establish `hs` using `(GlobalTheory.T.specializes_iff_point_ideal_le m n _ _).2 hP`. Establish `hr : w.1 (IsLocalRing.closedPoint ℂ) ∈ Set.range i` using `hs.mem_closed i.isClosedEmbedding.isClosed_range ⟨_, rfl⟩`. Establish `: Subsingleton (Sp ℂ)` using `inferInstanceAs (Subsingleton (PrimeSpectrum ℂ))`. Take `⟨f, hf⟩` from `GlobalTheory.exists_lift_closedImmersion_of_dense i w.1 Set.univ dense_univ fun q _ => by rwa [Subsingleton.elim q (IsLocalRing.closedPoint ℂ)]`. Use `⟨⟨f, by rw [← Category.assoc, hf]; exact w.2⟩, ?_⟩` and prove the remaining obligations.

Establish `e : PtsOver.map i rfl _ (⟨f, by rw [← Category.assoc, hf]; exact w.2⟩ : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) = w` using `Subtype.ext hf`. Rewrite using `[e]`. Conclude with `hw`.
-/
theorem exists_cxPt_of_mem_mcPts : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i]
    (z : (Σ k, Bk n k) → ℂ), z ∈ mcPts (ptIdeal (i (genericPoint X))) →
    ∃ y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀, IsUnder (PtsOver.map i rfl _ y) z := by
  intro m n X _ i _ z hz
  obtain ⟨w, hw, -⟩ := existsUnique_isUnder m n z hz.1
  have hP : ptIdeal (i (genericPoint X)) ≤ ptIdeal (w.1 (IsLocalRing.closedPoint ℂ)) := by
    rw [ptIdeal_of_isUnder hz.1 hw]
    exact le_mCoordIdeal_of_mem_mcPts (isMultiProjPrime_ptIdeal m n _).2.1 hz
  have hs := (GlobalTheory.T.specializes_iff_point_ideal_le m n _ _).2 hP
  have hr : w.1 (IsLocalRing.closedPoint ℂ) ∈ Set.range i :=
    hs.mem_closed i.isClosedEmbedding.isClosed_range ⟨_, rfl⟩
  have : Subsingleton (Sp ℂ) := inferInstanceAs (Subsingleton (PrimeSpectrum ℂ))
  obtain ⟨f, hf⟩ := GlobalTheory.exists_lift_closedImmersion_of_dense i w.1 Set.univ dense_univ
    fun q _ => by rwa [Subsingleton.elim q (IsLocalRing.closedPoint ℂ)]
  refine ⟨⟨f, by rw [← Category.assoc, hf]; exact w.2⟩, ?_⟩
  have e : PtsOver.map i rfl _ (⟨f, by rw [← Category.assoc, hf]; exact w.2⟩ : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) = w :=
    Subtype.ext hf
  rw [e]
  exact hw

end GlobalTheory.CompanionTheory.MPDict.UnderSub
