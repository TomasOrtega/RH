import Mathlib
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StDefinite
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.FinOfPI
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HilbertSchurOfAdjointClosed
open CompanionTheory.D.gk.admitted (stdPoly)
open GlobalTheory.AutomorphicL2Unitary
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.Factor

/- English proof (translation)
Introduce `H _ _ _ N Q hstar hQc hQinv hmin A hcomm`. Use `haveI : CompleteSpace Q := hQc.completeSpace_coe`. Set `σ : N → (Q →L[ℂ] Q)` to `fun T => (T.1.comp Q.subtypeL).codRestrict Q (fun v => hQinv T.1 T.2 v v.2)`. Establish `hσ : ∀ (T : N) (v : Q), ((σ T v : Q) : H) = T.1 v` using `fun _ _ => rfl`. Establish `hperp : ∀ T ∈ N, ∀ w ∈ Qᗮ, T w ∈ Qᗮ`.

Introduce `T hT w hw`. Rewrite `hw`, the goal using `[Submodule.mem_orthogonal]`. Introduce `u hu`. Establish `h1 : ⟪u, T w⟫_ℂ = ⟪(star T) u, w⟫_ℂ`. Rewrite using `[ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]`.

Rewrite using `[h1]`. Conclude with `hw _ (hQinv _ (hstar T hT) u hu)`. Establish `hproj : ∀ T ∈ N, ∀ w : H, Q.starProjection (T w) = T (Q.starProjection w)`. Introduce `T hT w`. Apply `Submodule.eq_starProjection_of_mem_orthogonal` to reduce the goal to its premises.

Conclude with `hQinv T hT _ (Submodule.starProjection_apply_mem Q w)`. Rewrite using `[← map_sub]`. Conclude with `hperp T hT _ (Submodule.sub_starProjection_mem_orthogonal w)`. Set `B : Q →L[ℂ] Q` to `(Q.orthogonalProjection).comp (A.comp Q.subtypeL)`. Establish `hB : ∀ v : Q, ((B v : Q) : H) = Q.starProjection (A v)` using `fun _ => rfl`.

Take `⟨c, hc⟩` from `GlobalTheory.hilbert_schur_of_adjoint_closed N Q σ (by`. Introduce `g`. Use `⟨⟨star g.1, hstar g.1 g.2⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[ContinuousLinearMap.eq_adjoint_iff]`. Introduce `x y`.

Express the relevant statement in the definitionally equal form `⟪(star g.1) (x : H), (y : H)⟫_ℂ = ⟪(x : H), g.1 (y : H)⟫_ℂ`. Rewrite using `[ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left])`. Use the proof step `(by`. Introduce `S hS hSinv`. Establish `hclosed : IsClosed ((S.map Q.subtype : Submodule ℂ H) : Set H)`.

Conclude with `hQc.isClosedEmbedding_subtypeVal.isClosedMap _ hS`. Establish `hle : S.map Q.subtype ≤ Q`. Introduce and unpack `_ ⟨x, -, rfl⟩`. Conclude with `x.2`. Establish `hinv : ∀ T ∈ N, ∀ v ∈ S.map Q.subtype, T v ∈ S.map Q.subtype`.

Introduce and unpack `T hT _ ⟨x, hx, rfl⟩`. Conclude with `⟨σ ⟨T, hT⟩ x, hSinv ⟨T, hT⟩ x hx, rfl⟩`. Break down `hmin _ hclosed hle hinv with h | h` into its components or cases. Use `left`. Rewrite using `[eq_bot_iff]`.

Introduce `x hx`. Establish `hx' : (x : H) ∈ S.map Q.subtype` using `⟨x, hx, rfl⟩`. Rewrite `hx'` using `[h, Submodule.mem_bot]`. Conclude with `(Submodule.mem_bot ℂ).2 (Subtype.ext hx')`. Use `right`.

Rewrite using `[eq_top_iff]`. Introduce `x _`. Establish `hx : (x : H) ∈ S.map Q.subtype`. Rewrite using `[h]`. Conclude with `x.2`.

Take `⟨y, hy, hyx⟩` from `hx`. Establish `: y = x` using `Subtype.ext hyx`. Conclude with `this ▸ hy)`. Use `B`. Use the proof step `(by`.

Introduce `g`. Use extensionality with `v`. Express the relevant statement in the definitionally equal form `Q.starProjection (A (g.1 v)) = g.1 (Q.starProjection (A v))`. Establish `h` using `congrArg (fun X : H →L[ℂ] H => X (v : H)) (hcomm g.1 g.2)`. Establish `h' : g.1 (A v) = A (g.1 v)` using `h`.

Rewrite using `[← h', hproj g.1 g.2])`. Use `⟨c, fun v hv => ?_⟩` and prove the remaining obligations. Establish `h1 : Q.starProjection (A v) = c • v`. Use `hB ⟨v, hv⟩` as an intermediate fact. Rewrite `this` using `[hc]`.

Simplify using `using this.symm`. Rewrite using `[← h1]`. Conclude with `Submodule.sub_starProjection_mem_orthogonal _`.
-/
theorem schur_on_minimal_subspace :
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (N : Set (H →L[ℂ] H))
    (Q : Submodule ℂ H), (∀ T ∈ N, star T ∈ N) → IsClosed (Q : Set H) → (∀ T ∈ N, ∀ v ∈ Q, T v ∈ Q) →
    (∀ U : Submodule ℂ H, IsClosed (U : Set H) → U ≤ Q → (∀ T ∈ N, ∀ v ∈ U, T v ∈ U) → U = ⊥ ∨ U = Q) →
    ∀ A : H →L[ℂ] H, (∀ T ∈ N, T * A = A * T) → ∃ c : ℂ, ∀ v ∈ Q, A v - c • v ∈ Qᗮ := by
  intro H _ _ _ N Q hstar hQc hQinv hmin A hcomm
  haveI : CompleteSpace Q := hQc.completeSpace_coe

  let σ : N → (Q →L[ℂ] Q) := fun T =>
    (T.1.comp Q.subtypeL).codRestrict Q (fun v => hQinv T.1 T.2 v v.2)
  have hσ : ∀ (T : N) (v : Q), ((σ T v : Q) : H) = T.1 v := fun _ _ => rfl

  have hperp : ∀ T ∈ N, ∀ w ∈ Qᗮ, T w ∈ Qᗮ := by
    intro T hT w hw
    rw [Submodule.mem_orthogonal] at hw ⊢
    intro u hu
    have h1 : ⟪u, T w⟫_ℂ = ⟪(star T) u, w⟫_ℂ := by
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
    rw [h1]
    exact hw _ (hQinv _ (hstar T hT) u hu)

  have hproj : ∀ T ∈ N, ∀ w : H, Q.starProjection (T w) = T (Q.starProjection w) := by
    intro T hT w
    apply Submodule.eq_starProjection_of_mem_orthogonal
    · exact hQinv T hT _ (Submodule.starProjection_apply_mem Q w)
    · rw [← map_sub]
      exact hperp T hT _ (Submodule.sub_starProjection_mem_orthogonal w)
  let B : Q →L[ℂ] Q := (Q.orthogonalProjection).comp (A.comp Q.subtypeL)
  have hB : ∀ v : Q, ((B v : Q) : H) = Q.starProjection (A v) := fun _ => rfl
  obtain ⟨c, hc⟩ := GlobalTheory.hilbert_schur_of_adjoint_closed N Q σ
    (by
      intro g
      refine ⟨⟨star g.1, hstar g.1 g.2⟩, ?_⟩
      rw [ContinuousLinearMap.eq_adjoint_iff]
      intro x y
      change ⟪(star g.1) (x : H), (y : H)⟫_ℂ = ⟪(x : H), g.1 (y : H)⟫_ℂ
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left])
    (by
      intro S hS hSinv
      have hclosed : IsClosed ((S.map Q.subtype : Submodule ℂ H) : Set H) := by
        exact hQc.isClosedEmbedding_subtypeVal.isClosedMap _ hS
      have hle : S.map Q.subtype ≤ Q := by
        rintro _ ⟨x, -, rfl⟩
        exact x.2
      have hinv : ∀ T ∈ N, ∀ v ∈ S.map Q.subtype, T v ∈ S.map Q.subtype := by
        rintro T hT _ ⟨x, hx, rfl⟩
        exact ⟨σ ⟨T, hT⟩ x, hSinv ⟨T, hT⟩ x hx, rfl⟩
      rcases hmin _ hclosed hle hinv with h | h
      · left
        rw [eq_bot_iff]
        intro x hx
        have hx' : (x : H) ∈ S.map Q.subtype := ⟨x, hx, rfl⟩
        rw [h, Submodule.mem_bot] at hx'
        exact (Submodule.mem_bot ℂ).2 (Subtype.ext hx')
      · right
        rw [eq_top_iff]
        intro x _
        have hx : (x : H) ∈ S.map Q.subtype := by
          rw [h]
          exact x.2
        obtain ⟨y, hy, hyx⟩ := hx
        have : y = x := Subtype.ext hyx
        exact this ▸ hy)
    B
    (by
      intro g
      ext v
      change Q.starProjection (A (g.1 v)) = g.1 (Q.starProjection (A v))
      have h := congrArg (fun X : H →L[ℂ] H => X (v : H)) (hcomm g.1 g.2)
      have h' : g.1 (A v) = A (g.1 v) := h
      rw [← h', hproj g.1 g.2])
  refine ⟨c, fun v hv => ?_⟩
  have h1 : Q.starProjection (A v) = c • v := by
    have := hB ⟨v, hv⟩
    rw [hc] at this
    simpa using this.symm
  rw [← h1]
  exact Submodule.sub_starProjection_mem_orthogonal _

end GlobalTheory.CompanionTheory.Factor
