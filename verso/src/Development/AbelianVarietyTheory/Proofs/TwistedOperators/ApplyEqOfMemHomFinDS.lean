import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ExponentSeparation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFixed
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntertwinerOfInvariantPairingAdmissibleStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchurAdmissibleAlt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfinitePartActDiscreteSeriesHomFactorwiseStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S

namespace GlobalTheory.TrExt

open scoped InnerProductSpace ComplexConjugate

/- English proof (translation)
Use `set p := Finsupp.linearCombination ℂ v with hp`. Use `set p' := Finsupp.linearCombination ℂ v' with hp'`. Establish `hin : ∀ f f', ⟪p' f, p' f'⟫_ℂ = c * ⟪p f, p f'⟫_ℂ`. Introduce `f f'`. Simplify using `only [p, p', Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum, inner_smul_left, inner_smul_right, hc, Finset.mul_sum]`.

Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring`. Establish `hn : ∀ f, ‖p' f‖ = Real.sqrt ‖c‖ * ‖p f‖`. Introduce `f`. Establish `h` using `congrArg norm (hin f f)`. Rewrite `h` using `[inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, norm_mul, norm_pow, norm_pow]`.

Simplify using `only [RCLike.norm_ofReal, Complex.norm_real, abs_norm, norm_norm] at h`. Rewrite using `[← Real.sqrt_sq (norm_nonneg (p' f)), h, Real.sqrt_mul (norm_nonneg c), Real.sqrt_sq (norm_nonneg _)]`. Establish `hker : LinearMap.ker p ≤ LinearMap.ker p'` using `fun f hf => by`. Rewrite `hf`, the goal using `[LinearMap.mem_ker]`. Rewrite using `[← norm_eq_zero, hn, hf, norm_zero, mul_zero]`.

Set `L : LinearMap.range p →ₗ[ℂ] K` to `(LinearMap.ker p).liftQ p' hker ∘ₗ p.quotKerEquivRange.symm.toLinearMap`. Establish `hL : ∀ f, L ⟨p f, f, rfl⟩ = p' f` using `fun f => by`. Establish `: p.quotKerEquivRange.symm ⟨p f, f, rfl⟩ = Submodule.Quotient.mk f`. Rewrite using `[LinearEquiv.symm_apply_eq]`. Both sides reduce to the same expression.

Simplify using `only [L, LinearMap.comp_apply, LinearEquiv.coe_coe, this, Submodule.liftQ_apply]`. Establish `hb : ∀ x, ‖L x‖ ≤ Real.sqrt ‖c‖ * ‖x‖`. Introduce and unpack `⟨_, f, rfl⟩`. Rewrite using `[hL, hn]`. Both sides reduce to the same expression.

Set `A0` to `L.mkContinuous _ hb`. Set `e` to `(LinearMap.range p).subtypeL`. Establish `hrange : (LinearMap.range p : Set H) = Submodule.span ℂ (Set.range v)`. Rewrite using `[hp, Finsupp.range_linearCombination]`. Establish `hdense : DenseRange e`.

Establish `: Dense ((Submodule.span ℂ (Set.range v) : Submodule ℂ H) : Set H)` using `(Submodule.dense_iff_topologicalClosure_eq_top).2 hd`. Rewrite `this` using `[← hrange]`. Conclude with `this.denseRange_val`. Establish `hui : IsUniformInducing e` using `isUniformEmbedding_subtype_val.isUniformInducing`. Use `⟨A0.extend e, fun i => ?_⟩` and prove the remaining obligations.

Establish `h1 : p (Finsupp.single i 1) = v i` using `by simp [p]`. Establish `h2 : p' (Finsupp.single i 1) = v' i` using `by simp [p']`. Use `ContinuousLinearMap.extend_eq A0 hdense hui ⟨p (Finsupp.single i 1), _, rfl⟩` as an intermediate fact. Simplify using `only [e, Submodule.subtypeL_apply, A0, LinearMap.mkContinuous_apply, hL] at this`. Rewrite using `[← h1, this, h2]`.
-/
theorem exists_clm_of_inner_eq {ι H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (v : ι → H) (v' : ι → K) (c : ℂ) (hc : ∀ i j, ⟪v' i, v' j⟫_ℂ = c * ⟪v i, v j⟫_ℂ)
    (hd : (Submodule.span ℂ (Set.range v)).topologicalClosure = ⊤) :
    ∃ A : H →L[ℂ] K, ∀ i, A (v i) = v' i := by
  set p := Finsupp.linearCombination ℂ v with hp
  set p' := Finsupp.linearCombination ℂ v' with hp'
  have hin : ∀ f f', ⟪p' f, p' f'⟫_ℂ = c * ⟪p f, p f'⟫_ℂ := by
    intro f f'
    simp only [p, p', Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum, inner_smul_left,
      inner_smul_right, hc, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hn : ∀ f, ‖p' f‖ = Real.sqrt ‖c‖ * ‖p f‖ := by
    intro f
    have h := congrArg norm (hin f f)
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, norm_mul, norm_pow, norm_pow] at h
    simp only [RCLike.norm_ofReal, Complex.norm_real, abs_norm, norm_norm] at h
    rw [← Real.sqrt_sq (norm_nonneg (p' f)), h, Real.sqrt_mul (norm_nonneg c), Real.sqrt_sq (norm_nonneg _)]
  have hker : LinearMap.ker p ≤ LinearMap.ker p' := fun f hf => by
    rw [LinearMap.mem_ker] at hf ⊢
    rw [← norm_eq_zero, hn, hf, norm_zero, mul_zero]
  let L : LinearMap.range p →ₗ[ℂ] K := (LinearMap.ker p).liftQ p' hker ∘ₗ p.quotKerEquivRange.symm.toLinearMap
  have hL : ∀ f, L ⟨p f, f, rfl⟩ = p' f := fun f => by
    have : p.quotKerEquivRange.symm ⟨p f, f, rfl⟩ = Submodule.Quotient.mk f := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    simp only [L, LinearMap.comp_apply, LinearEquiv.coe_coe, this, Submodule.liftQ_apply]
  have hb : ∀ x, ‖L x‖ ≤ Real.sqrt ‖c‖ * ‖x‖ := by
    rintro ⟨_, f, rfl⟩
    rw [hL, hn]; rfl
  let A0 := L.mkContinuous _ hb
  let e := (LinearMap.range p).subtypeL
  have hrange : (LinearMap.range p : Set H) = Submodule.span ℂ (Set.range v) := by
    rw [hp, Finsupp.range_linearCombination]
  have hdense : DenseRange e := by
    have : Dense ((Submodule.span ℂ (Set.range v) : Submodule ℂ H) : Set H) :=
      (Submodule.dense_iff_topologicalClosure_eq_top).2 hd
    rw [← hrange] at this
    exact this.denseRange_val
  have hui : IsUniformInducing e := isUniformEmbedding_subtype_val.isUniformInducing
  refine ⟨A0.extend e, fun i => ?_⟩
  have h1 : p (Finsupp.single i 1) = v i := by simp [p]
  have h2 : p' (Finsupp.single i 1) = v' i := by simp [p']
  have := ContinuousLinearMap.extend_eq A0 hdense hui ⟨p (Finsupp.single i 1), _, rfl⟩
  simp only [e, Submodule.subtypeL_apply, A0, LinearMap.mkContinuous_apply, hL] at this
  rw [← h1, this, h2]

end GlobalTheory.TrExt

namespace GlobalTheory.TrExt

open scoped InnerProductSpace ComplexConjugate

/- English proof (translation)
Establish `hm` using `mem_homTensorPi.1 h`. Use `conv_lhs => rw [← toInf_mul_toFin g, map_mul, ContinuousLinearMap.mul_apply]`. Establish `h1 : ρ (toFin V g : GA D V) (T w y) = T (σ (toFin V g) w) y` using `(hm.2.1 (toFin V g) w y).symm`. Rewrite using `[h1]`. Conclude with `GlobalTheory.T.infinitePart_act_discreteSeriesHom_factorwise D V S M X ρ U _ (h.1 _) g y`.
-/
theorem apply_eq_of_mem_homFinDS {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {W : Type}
    [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (GfC V) W} {X : Type} [NormedAddCommGroup X]
    [InnerProductSpace ℂ X] [CompleteSpace X] {ρ : GA D V →* (X →L[ℂ] X)} {U : Submodule ℂ X}
    {T : W →ₗ[ℂ] ContinuousMultilinearMap ℂ M.H X} (h : T ∈ homFinDS σ M ρ U) (g : GA D V) (w : W)
    (y : ∀ τ, M.H τ) : ρ g (T w y) =
      T (σ (toFin V g) w) (fun τ => dsRep M τ (projArch D.sp.cm.sig V.gram (placeOf D τ) g) (y τ)) := by
  classical
  have hm := mem_homTensorPi.1 h
  conv_lhs => rw [← toInf_mul_toFin g, map_mul, ContinuousLinearMap.mul_apply]
  have h1 : ρ (toFin V g : GA D V) (T w y) = T (σ (toFin V g) w) y := (hm.2.1 (toFin V g) w y).symm
  rw [h1]
  exact GlobalTheory.T.infinitePart_act_discreteSeriesHom_factorwise D V S M X ρ U _ (h.1 _) g y

open Classical in

/- English proof (translation)
Introduce `D V S M W _ _ σ hirr hadm H _ _ _ π hπ T hT hinj hd K _ _ _ ρ hρ U hU T' hT'`. Establish `hδ : ∀ τ, IsIrrUnitary (dsRep M τ)` using `isIrrUnitary_dsRep M`. Establish `hTw : ∀ w, T w ∈ homDS M π ⊤` using `fun w => hT.1 w`. Establish `hTw' : ∀ w, T' w ∈ homDS M ρ U` using `fun w => hT'.1 w`. Establish `hTm` using `mem_homTensorPi.1 hT`.

Establish `hTm'` using `mem_homTensorPi.1 hT'`. Set `B : W →ₗ[ℂ] W →ₛₗ[starRingEnd ℂ] ℂ` to `LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun v w => bePi (T v) (T w)) (fun _ _ _ => by simp [bePi, inner_add_right]) (fun _ _ _ => by simp [bePi]) (fun _ _ _ => by simp [bePi, inner_add_left]) (fun _ _ _ => by simp [bePi, inner_smul_left, mul_comm])`. Set `C : W →ₗ[ℂ] W →ₛₗ[starRingEnd ℂ] ℂ` to `LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun v w => bePi (T' v) (T' w)) (fun _ _ _ => by simp [bePi, inner_add_right]) (fun _ _ _ => by simp [bePi]) (fun _ _ _ => by simp [bePi, inner_add_left]) (fun _ _ _ => by simp [bePi, inner_smul_left, mul_comm])`. Establish `hBpos : ∀ x, x ≠ 0 → 0 < (B x x).re` using `fun x hx => bePi_self_pos hδ hπ (hTw x) ((map_ne_zero_iff T hinj).2 hx)`. Establish `hB : ∀ g x y, B (σ g x) (σ g y) = B x y` using `fun g x y => by`.

Express the relevant statement in the definitionally equal form `⟪T (σ g y) _, T (σ g x) _⟫_ℂ = ⟪T y _, T x _⟫_ℂ`. Rewrite using `[hTm.2.1, hTm.2.1, inner_map_map hπ]`. Establish `hC : ∀ g x y, C (σ g x) (σ g y) = C x y` using `fun g x y => by`. Express the relevant statement in the definitionally equal form `⟪T' (σ g y) _, T' (σ g x) _⟫_ℂ = ⟪T' y _, T' x _⟫_ℂ`. Rewrite using `[hTm'.2.1, hTm'.2.1, inner_map_map hρ]`.

Take `⟨K₀, hKo, hKc⟩` from `GlobalTheory.CuspDec.exists_compact_open V`. Take `⟨φ, hφ, hCB⟩` from `GlobalTheory.T.exists_intertwiner_of_invariantPairing_admissible (GfC V) K₀ hKo hKc W W σ σ hadm hadm.1 B C hBpos hB hC`. Take `⟨c, rfl⟩` from `GlobalTheory.SchurAdm.schur_admissible (GfC V) K₀ hKo hKc W σ hirr hadm φ hφ`. Establish `hbe : ∀ x y, bePi (T' x) (T' y) = conj c * bePi (T x) (T y)` using `fun x y => by`. Establish `: bePi (T' x) (T' y) = bePi (T x) (T (c • y))` using `hCB x y`.

Rewrite using `[this, map_smul, bePi, bePi, ContinuousMultilinearMap.smul_apply, inner_smul_left]`. Establish `hinner : ∀ q r : W × (∀ τ, M.H τ), ⟪T' q.1 q.2, T' r.1 r.2⟫_ℂ = conj c * ⟪T q.1 q.2, T r.1 r.2⟫_ℂ`. Introduce and unpack `⟨w, y⟩ ⟨w', y'⟩`. Rewrite using `[inner_eq_bePi hδ hρ (hTw' w') (hTw' w), inner_eq_bePi hδ hπ (hTw w') (hTw w), hbe, mul_assoc]`. Establish `hset : {v | ∃ w y, v = T w y} = Set.range (fun q : W × (∀ τ, M.H τ) => T q.1 q.2)`.

Use extensionality with `v`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, y, rfl⟩`. Conclude with `⟨(w, y), rfl⟩`. Introduce and unpack `⟨⟨w, y⟩, rfl⟩`.

Conclude with `⟨w, y, rfl⟩`. Rewrite `hd` using `[hset]`. Take `⟨A, hA⟩` from `exists_clm_of_inner_eq _ _ _ hinner hd`. Establish `hA' : ∀ w y, A (T w y) = T' w y` using `fun w y => hA (w, y)`. Establish `hdense : Dense ((Submodule.span ℂ (Set.range fun q : W × (∀ τ, M.H τ) => T q.1 q.2)) : Set H)` using `(Submodule.dense_iff_topologicalClosure_eq_top).2 hd`.

Use `⟨A, ⟨fun x => ?_, fun g => ?_⟩, fun w y => hA (w, y)⟩` and prove the remaining obligations. Establish `hle : Submodule.span ℂ (Set.range fun q : W × (∀ τ, M.H τ) => T q.1 q.2) ≤ U.comap (A : H →ₗ[ℂ] K)` using `Submodule.span_le.2 (by`. Introduce and unpack `_ ⟨⟨w, y⟩, rfl⟩`. Use `show A (T w y) ∈ U`. Rewrite using `[show A (T w y) = T' w y from hA (w, y)]`.

Conclude with `hTm'.1 w y)`. Use `Submodule.topologicalClosure_minimal _ hle (hU.preimage A.continuous)` as an intermediate fact. Rewrite `this` using `[hd]`. Conclude with `this trivial`. Use `DFunLike.congr_fun (ContinuousLinearMap.ext_on (f := A ∘L π g) (g := ρ g ∘L A) hdense ?_)` and prove the remaining obligations.

Introduce and unpack `_ ⟨⟨w, y⟩, rfl⟩`. Simplify using `only [ContinuousLinearMap.comp_apply]`. Rewrite using `[apply_eq_of_mem_homFinDS hT, hA', hA', apply_eq_of_mem_homFinDS hT']`.
-/
theorem exists_homIn_extend : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), σ.IsIrreducible → IsAdmissible σ → ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : GA D V →* (H →L[ℂ] H)), IsUnitaryRep π → ∀ T ∈ homFinDS σ M π ⊤, Function.Injective T → (Submodule.span ℂ {v | ∃ w y, v = T w y}).topologicalClosure = ⊤ → ∀ (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (ρ : GA D V →* (K →L[ℂ] K)), IsUnitaryRep ρ → ∀ U : Submodule ℂ K, IsClosed (U : Set K) → ∀ T' ∈ homFinDS σ M ρ U, ∃ A ∈ homIn π ρ U, ∀ w y, A (T w y) = T' w y := by
  intro D V S M W _ _ σ hirr hadm H _ _ _ π hπ T hT hinj hd K _ _ _ ρ hρ U hU T' hT'
  have hδ : ∀ τ, IsIrrUnitary (dsRep M τ) := isIrrUnitary_dsRep M
  have hTw : ∀ w, T w ∈ homDS M π ⊤ := fun w => hT.1 w
  have hTw' : ∀ w, T' w ∈ homDS M ρ U := fun w => hT'.1 w
  have hTm := mem_homTensorPi.1 hT
  have hTm' := mem_homTensorPi.1 hT'

  let B : W →ₗ[ℂ] W →ₛₗ[starRingEnd ℂ] ℂ := LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun v w => bePi (T v) (T w))
    (fun _ _ _ => by simp [bePi, inner_add_right]) (fun _ _ _ => by simp [bePi])
    (fun _ _ _ => by simp [bePi, inner_add_left]) (fun _ _ _ => by simp [bePi, inner_smul_left, mul_comm])
  let C : W →ₗ[ℂ] W →ₛₗ[starRingEnd ℂ] ℂ := LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun v w => bePi (T' v) (T' w))
    (fun _ _ _ => by simp [bePi, inner_add_right]) (fun _ _ _ => by simp [bePi])
    (fun _ _ _ => by simp [bePi, inner_add_left]) (fun _ _ _ => by simp [bePi, inner_smul_left, mul_comm])
  have hBpos : ∀ x, x ≠ 0 → 0 < (B x x).re := fun x hx =>
    bePi_self_pos hδ hπ (hTw x) ((map_ne_zero_iff T hinj).2 hx)
  have hB : ∀ g x y, B (σ g x) (σ g y) = B x y := fun g x y => by
    change ⟪T (σ g y) _, T (σ g x) _⟫_ℂ = ⟪T y _, T x _⟫_ℂ
    rw [hTm.2.1, hTm.2.1, inner_map_map hπ]
  have hC : ∀ g x y, C (σ g x) (σ g y) = C x y := fun g x y => by
    change ⟪T' (σ g y) _, T' (σ g x) _⟫_ℂ = ⟪T' y _, T' x _⟫_ℂ
    rw [hTm'.2.1, hTm'.2.1, inner_map_map hρ]
  obtain ⟨K₀, hKo, hKc⟩ := GlobalTheory.CuspDec.exists_compact_open V
  obtain ⟨φ, hφ, hCB⟩ := GlobalTheory.T.exists_intertwiner_of_invariantPairing_admissible (GfC V) K₀ hKo hKc W W σ σ hadm hadm.1 B C hBpos hB hC
  obtain ⟨c, rfl⟩ := GlobalTheory.SchurAdm.schur_admissible (GfC V) K₀ hKo hKc W σ hirr hadm φ hφ

  have hbe : ∀ x y, bePi (T' x) (T' y) = conj c * bePi (T x) (T y) := fun x y => by
    have : bePi (T' x) (T' y) = bePi (T x) (T (c • y)) := hCB x y
    rw [this, map_smul, bePi, bePi, ContinuousMultilinearMap.smul_apply, inner_smul_left]
  have hinner : ∀ q r : W × (∀ τ, M.H τ), ⟪T' q.1 q.2, T' r.1 r.2⟫_ℂ = conj c * ⟪T q.1 q.2, T r.1 r.2⟫_ℂ := by
    rintro ⟨w, y⟩ ⟨w', y'⟩
    rw [inner_eq_bePi hδ hρ (hTw' w') (hTw' w), inner_eq_bePi hδ hπ (hTw w') (hTw w), hbe, mul_assoc]
  have hset : {v | ∃ w y, v = T w y} = Set.range (fun q : W × (∀ τ, M.H τ) => T q.1 q.2) := by
    ext v; constructor
    · rintro ⟨w, y, rfl⟩; exact ⟨(w, y), rfl⟩
    · rintro ⟨⟨w, y⟩, rfl⟩; exact ⟨w, y, rfl⟩
  rw [hset] at hd
  obtain ⟨A, hA⟩ := exists_clm_of_inner_eq _ _ _ hinner hd
  have hA' : ∀ w y, A (T w y) = T' w y := fun w y => hA (w, y)
  have hdense : Dense ((Submodule.span ℂ (Set.range fun q : W × (∀ τ, M.H τ) => T q.1 q.2)) : Set H) :=
    (Submodule.dense_iff_topologicalClosure_eq_top).2 hd
  refine ⟨A, ⟨fun x => ?_, fun g => ?_⟩, fun w y => hA (w, y)⟩
  · have hle : Submodule.span ℂ (Set.range fun q : W × (∀ τ, M.H τ) => T q.1 q.2) ≤ U.comap (A : H →ₗ[ℂ] K) :=
      Submodule.span_le.2 (by
        rintro _ ⟨⟨w, y⟩, rfl⟩
        show A (T w y) ∈ U
        rw [show A (T w y) = T' w y from hA (w, y)]
        exact hTm'.1 w y)
    have := Submodule.topologicalClosure_minimal _ hle (hU.preimage A.continuous)
    rw [hd] at this
    exact this trivial
  ·
    refine DFunLike.congr_fun (ContinuousLinearMap.ext_on (f := A ∘L π g) (g := ρ g ∘L A) hdense ?_)
    rintro _ ⟨⟨w, y⟩, rfl⟩
    simp only [ContinuousLinearMap.comp_apply]
    rw [apply_eq_of_mem_homFinDS hT, hA', hA', apply_eq_of_mem_homFinDS hT']

end GlobalTheory.TrExt
