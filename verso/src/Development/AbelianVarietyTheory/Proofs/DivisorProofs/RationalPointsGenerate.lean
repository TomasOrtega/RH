import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemClosureUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RealAdelesCmFieldEquivComplexCmType
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit

noncomputable section

namespace GlobalTheory.RatGen

open scoped TensorProduct Matrix ComplexOrder

/- English proof (translation)
Use `set H := Subgroup.closure (φ ⁻¹' N) with hH`. Establish `hsub : N ⊆ (H.map φ).topologicalClosure`. Use `(hφ.open_subset_closure_inter hN).trans (closure_mono ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨hx, γ, rfl⟩`. Conclude with `⟨γ, Subgroup.subset_closure hx, rfl⟩`.

Establish `ho : IsOpen ((H.map φ).topologicalClosure : Set G)` using `Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset (hN.mem_nhds h1) hsub)`. Establish `hall : ((H.map φ).topologicalClosure : Set G) = Set.univ` using `IsClopen.eq_univ ⟨Subgroup.isClosed_topologicalClosure _, ho⟩ ⟨1, one_mem _⟩`. Use `(Subgroup.eq_top_iff' _).2 fun γ => ?_` and prove the remaining obligations. Establish `h2 : φ γ ∈ closure (H.map φ : Set G)`. Establish `: φ γ ∈ ((H.map φ).topologicalClosure : Set G)` using `hall ▸ Set.mem_univ _`.

Conclude with `this`. Take `⟨_, hx, h, hh, rfl⟩` from `mem_closure_iff.1 h2 {x | x⁻¹ * φ γ ∈ N} (hN.preimage (continuous_inv.mul continuous_const)) (by simpa using h1)`. Establish `h3 : h⁻¹ * γ ∈ H` using `Subgroup.subset_closure (by simpa using hx)`. Simplify using `using H.mul_mem hh h3`.
-/
theorem closure_preimage_eq_top {Γ G : Type} [Group Γ] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [PreconnectedSpace G] (φ : Γ →* G) (hφ : DenseRange φ) (N : Set G) (hN : IsOpen N) (h1 : (1 : G) ∈ N) :
    Subgroup.closure (φ ⁻¹' N) = ⊤ := by
  set H := Subgroup.closure (φ ⁻¹' N) with hH
  have hsub : N ⊆ (H.map φ).topologicalClosure := by
    refine (hφ.open_subset_closure_inter hN).trans (closure_mono ?_)
    rintro _ ⟨hx, γ, rfl⟩
    exact ⟨γ, Subgroup.subset_closure hx, rfl⟩
  have ho : IsOpen ((H.map φ).topologicalClosure : Set G) :=
    Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset (hN.mem_nhds h1) hsub)
  have hall : ((H.map φ).topologicalClosure : Set G) = Set.univ :=
    IsClopen.eq_univ ⟨Subgroup.isClosed_topologicalClosure _, ho⟩ ⟨1, one_mem _⟩
  refine (Subgroup.eq_top_iff' _).2 fun γ => ?_
  have h2 : φ γ ∈ closure (H.map φ : Set G) := by
    have : φ γ ∈ ((H.map φ).topologicalClosure : Set G) := hall ▸ Set.mem_univ _
    exact this
  obtain ⟨_, hx, h, hh, rfl⟩ := mem_closure_iff.1 h2 {x | x⁻¹ * φ γ ∈ N}
    (hN.preimage (continuous_inv.mul continuous_const)) (by simpa using h1)
  have h3 : h⁻¹ * γ ∈ H := Subgroup.subset_closure (by simpa using hx)
  simpa using H.mul_mem hh h3

open Formalism.UG GlobalTheory.UnRep.WeakApprox in

/- English proof (translation)
Establish `he : Topology.IsEmbedding (Units.val : GL (Fin n) R → Matrix (Fin n) (Fin n) R)` using `Units.isEmbedding_val_mk' (f := Inv.inv) (fun M hM => (continuousAt_matrix_inv M (h2 _ ((Matrix.isUnit_iff_isUnit_det _).1 hM))).continuousWithinAt) (fun u => (Matrix.coe_units_inv u).symm)`. Establish `he' : Topology.IsInducing (fun h : UJ σ J => h.1.1)` using `he.isInducing.comp Topology.IsInducing.subtypeVal`. Establish `h2' : IsUnit (2 : R)`. Use `(two_ne_zero (α := K)).isUnit.map ι` as an intermediate fact. Rewrite `this` using `[map_ofNat]`. Then use the resulting hypothesis.

Establish `hdet' : IsUnit (Jᵀ).det` using `by rwa [Matrix.det_transpose]`. Take `⟨c1, c2, c3, -⟩` from `GlobalTheory.CayleyInv.cayley_transform R σ n Jᵀ hσ (by rw [Matrix.transpose_map]; exact congrArg Matrix.transpose hJ) hdet' h2'`. Establish `mk : ∀ M : Matrix (Fin n) (Fin n) R, Mᵀ * Jᵀ * M.map σ = Jᵀ → ∃ u : UJ σ J, u.1.1 = M`. Introduce `M hM`. Establish `hu : IsUnit M.det`.

Use `hdet'` as an intermediate fact. Rewrite `this` using `[← hM, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose M]`. Conclude with `isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left this)`. Take `⟨u, rfl⟩` from `(Matrix.isUnit_iff_isUnit_det _).2 hu`. Conclude with `⟨⟨u, (GlobalTheory.Mass.OnePlace.unitary_transpose _ _ _).2 hM⟩, rfl⟩`.

Establish `step : ∀ k : UJ σ J, IsUnit (1 + k.1.1).det → k ∈ Subgroup.connectedComponentOfOne (UJ σ J)`. Introduce `k hk`. Take `⟨hS, -⟩` from `c1 k.1.1 ((GlobalTheory.Mass.OnePlace.unitary_transpose _ _ _).1 k.2) hk`. Establish `hkS` using `c2 k.1.1 hk`. Use `set S : Matrix (Fin n) (Fin n) R := (1 - k.1.1) * (1 + k.1.1)⁻¹`.

Establish `hsk : ∀ a, (p a • S)ᵀ * Jᵀ + Jᵀ * (p a • S).map σ = 0` using `fun a => by`. Rewrite using `[map_smul'', hpσ, Matrix.transpose_smul, smul_mul_assoc, mul_smul_comm, ← smul_add, hS, smul_zero]`. Use `choose f hf using fun a => mk _ (c3 _ (hsk a) (hdef _ (hsk a)))`. Establish `hT : Continuous fun a => p a • S` using `hp.smul continuous_const`. Establish `hfc : Continuous f`.

Rewrite using `[he'.continuous_iff]`. Establish `: ((fun h : UJ σ J => h.1.1) ∘ f) = fun a => (1 - p a • S) * (1 + p a • S)⁻¹` using `funext hf`. Rewrite using `[this]`. Use `(continuous_const.sub hT).mul (continuous_iff_continuousAt.2 fun a => ?_)` and prove the remaining obligations. Conclude with `ContinuousAt.comp (f := fun a => 1 + p a • S) (continuousAt_matrix_inv _ (h2 _ (hdef _ (hsk a)))) (continuous_const.add hT).continuousAt`.

Establish `e0 : f a₀ = 1` using `Subtype.ext (Units.ext (by rw [hf, h₀]; simp))`. Establish `e1 : f a₁ = k` using `Subtype.ext (Units.ext (by rw [hf, h₁, one_smul, hkS]))`. Conclude with `(isPreconnected_range hfc).subset_connectedComponent ⟨a₀, e0⟩ ⟨a₁, e1⟩`. Establish `all : ∀ g : UJ σ J, g ∈ Subgroup.connectedComponentOfOne (UJ σ J)`. Introduce `g`.

Take `⟨lam, ⟨hlam, hl1⟩, hu⟩` from `GlobalTheory.NormSum.RepAt.exists_unit_det ι g.1.1 _ (GlobalTheory.NormSum.RepAt.normOne_infinite c hc hne)`. Establish `hl : ι lam * σ (ι lam) = 1` using `by rw [hσι, ← map_mul, hlam, map_one]`. Take `⟨s, hs⟩` from `mk (ι lam • 1) (by`. Rewrite using `[map_smul'', Matrix.transpose_smul, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul, hl, one_smul, Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.transpose_one, one_mul, mul_one])`. Establish `m1` using `step s (by`.

Establish `: (1 : Matrix (Fin n) (Fin n) R) + ι lam • 1 = ι (1 + lam) • 1`. Rewrite using `[map_add, map_one, add_smul, one_smul]`. Rewrite using `[hs, this, Matrix.det_smul, Matrix.det_one, mul_one]`. Conclude with `(hl1.isUnit.map ι).pow _)`. Establish `m2` using `step (s * g) (by`.

Establish `: (s * g).1.1 = s.1.1 * g.1.1` using `rfl`. Rewrite using `[this, hs, smul_mul_assoc, one_mul]`. Conclude with `hu)`. Simplify using `using mul_mem (inv_mem m1) m2`. Use `⟨?_⟩` and prove the remaining obligations.

Establish `: connectedComponent (1 : UJ σ J) = Set.univ` using `Set.eq_univ_of_forall all`. Rewrite using `[← this]`. Conclude with `isPreconnected_connectedComponent`.
-/
theorem preconnected_unitary {K R A : Type} [Field K] [CharZero K] [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [IsArtinianRing R] (ι : K →+* R) (c : K →+* K) (σ : R →+* R)
    (hσι : ∀ x, σ (ι x) = ι (c x)) (hc : ∀ x, c (c x) = x) (hne : ∃ z, c z ≠ z) (hσ : ∀ x, σ (σ x) = x)
    (h2 : ∀ x : R, IsUnit x → ContinuousAt Ring.inverse x)
    [TopologicalSpace A] [PreconnectedSpace A] (p : A → R) (hp : Continuous p) (hpσ : ∀ a, σ (p a) = p a)
    (a₀ a₁ : A) (h₀ : p a₀ = 0) (h₁ : p a₁ = 1) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) R) (hJ : cT σ J = J) (hdet : IsUnit J.det)
    (hdef : ∀ S : Matrix (Fin n) (Fin n) R, Sᵀ * Jᵀ + Jᵀ * S.map σ = 0 → IsUnit (1 + S).det) :
    PreconnectedSpace (UJ σ J) := by
  have he : Topology.IsEmbedding (Units.val : GL (Fin n) R → Matrix (Fin n) (Fin n) R) :=
    Units.isEmbedding_val_mk' (f := Inv.inv)
      (fun M hM => (continuousAt_matrix_inv M (h2 _ ((Matrix.isUnit_iff_isUnit_det _).1 hM))).continuousWithinAt)
      (fun u => (Matrix.coe_units_inv u).symm)
  have he' : Topology.IsInducing (fun h : UJ σ J => h.1.1) :=
    he.isInducing.comp Topology.IsInducing.subtypeVal
  have h2' : IsUnit (2 : R) := by
    have := (two_ne_zero (α := K)).isUnit.map ι
    rwa [map_ofNat] at this
  have hdet' : IsUnit (Jᵀ).det := by rwa [Matrix.det_transpose]
  obtain ⟨c1, c2, c3, -⟩ := GlobalTheory.CayleyInv.cayley_transform R σ n Jᵀ hσ
    (by rw [Matrix.transpose_map]; exact congrArg Matrix.transpose hJ) hdet' h2'
  have mk : ∀ M : Matrix (Fin n) (Fin n) R, Mᵀ * Jᵀ * M.map σ = Jᵀ → ∃ u : UJ σ J, u.1.1 = M := by
    intro M hM
    have hu : IsUnit M.det := by
      have := hdet'
      rw [← hM, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose M] at this
      exact isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left this)
    obtain ⟨u, rfl⟩ := (Matrix.isUnit_iff_isUnit_det _).2 hu
    exact ⟨⟨u, (GlobalTheory.Mass.OnePlace.unitary_transpose _ _ _).2 hM⟩, rfl⟩
  have step : ∀ k : UJ σ J, IsUnit (1 + k.1.1).det → k ∈ Subgroup.connectedComponentOfOne (UJ σ J) := by
    intro k hk
    obtain ⟨hS, -⟩ := c1 k.1.1 ((GlobalTheory.Mass.OnePlace.unitary_transpose _ _ _).1 k.2) hk
    have hkS := c2 k.1.1 hk
    set S : Matrix (Fin n) (Fin n) R := (1 - k.1.1) * (1 + k.1.1)⁻¹
    have hsk : ∀ a, (p a • S)ᵀ * Jᵀ + Jᵀ * (p a • S).map σ = 0 := fun a => by
      rw [map_smul'', hpσ, Matrix.transpose_smul, smul_mul_assoc, mul_smul_comm, ← smul_add, hS, smul_zero]
    choose f hf using fun a => mk _ (c3 _ (hsk a) (hdef _ (hsk a)))
    have hT : Continuous fun a => p a • S := hp.smul continuous_const
    have hfc : Continuous f := by
      rw [he'.continuous_iff]
      have : ((fun h : UJ σ J => h.1.1) ∘ f) = fun a => (1 - p a • S) * (1 + p a • S)⁻¹ := funext hf
      rw [this]
      refine (continuous_const.sub hT).mul (continuous_iff_continuousAt.2 fun a => ?_)
      exact ContinuousAt.comp (f := fun a => 1 + p a • S)
        (continuousAt_matrix_inv _ (h2 _ (hdef _ (hsk a)))) (continuous_const.add hT).continuousAt
    have e0 : f a₀ = 1 := Subtype.ext (Units.ext (by rw [hf, h₀]; simp))
    have e1 : f a₁ = k := Subtype.ext (Units.ext (by rw [hf, h₁, one_smul, hkS]))
    exact (isPreconnected_range hfc).subset_connectedComponent ⟨a₀, e0⟩ ⟨a₁, e1⟩
  have all : ∀ g : UJ σ J, g ∈ Subgroup.connectedComponentOfOne (UJ σ J) := by
    intro g
    obtain ⟨lam, ⟨hlam, hl1⟩, hu⟩ := GlobalTheory.NormSum.RepAt.exists_unit_det ι g.1.1 _
      (GlobalTheory.NormSum.RepAt.normOne_infinite c hc hne)
    have hl : ι lam * σ (ι lam) = 1 := by rw [hσι, ← map_mul, hlam, map_one]
    obtain ⟨s, hs⟩ := mk (ι lam • 1) (by
      rw [map_smul'', Matrix.transpose_smul, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul, hl,
        one_smul, Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.transpose_one, one_mul, mul_one])
    have m1 := step s (by
      have : (1 : Matrix (Fin n) (Fin n) R) + ι lam • 1 = ι (1 + lam) • 1 := by
        rw [map_add, map_one, add_smul, one_smul]
      rw [hs, this, Matrix.det_smul, Matrix.det_one, mul_one]
      exact (hl1.isUnit.map ι).pow _)
    have m2 := step (s * g) (by
      have : (s * g).1.1 = s.1.1 * g.1.1 := rfl
      rw [this, hs, smul_mul_assoc, one_mul]
      exact hu)
    simpa using mul_mem (inv_mem m1) m2
  refine ⟨?_⟩
  have : connectedComponent (1 : UJ σ J) = Set.univ := Set.eq_univ_of_forall all
  rw [← this]
  exact isPreconnected_connectedComponent

/- English proof (translation)
Introduce `h`. Take `⟨v, hv, h0⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 h`. Establish `h1 : S *ᵥ v = -v`. Rewrite `h0` using `[Matrix.add_mulVec, Matrix.one_mulVec]`. Conclude with `eq_neg_of_add_eq_zero_right h0`.

Establish `h2 : star v ⬝ᵥ ((Sᴴ * J + J * S) *ᵥ v) = 0` using `by rw [hS]; simp`. Rewrite `h2` using `[Matrix.add_mulVec, dotProduct_add, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, h1, Matrix.mulVec_neg, star_neg, neg_dotProduct, dotProduct_neg]`. Establish `h3` using `(hJ.dotProduct_mulVec_pos hv).ne'`. Conclude with `h3 (by linear_combination (-1 / 2 : ℂ) * h2)`.
-/
theorem det_one_add_ne_zero {n : ℕ} {J S : Matrix (Fin n) (Fin n) ℂ} (hJ : J.PosDef) (hS : Sᴴ * J + J * S = 0) :
    (1 + S).det ≠ 0 := by
  intro h
  obtain ⟨v, hv, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  have h1 : S *ᵥ v = -v := by
    rw [Matrix.add_mulVec, Matrix.one_mulVec] at h0
    exact eq_neg_of_add_eq_zero_right h0
  have h2 : star v ⬝ᵥ ((Sᴴ * J + J * S) *ᵥ v) = 0 := by rw [hS]; simp
  rw [Matrix.add_mulVec, dotProduct_add, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    ← Matrix.star_mulVec, h1, Matrix.mulVec_neg, star_neg, neg_dotProduct, dotProduct_neg] at h2
  have h3 := (hJ.dotProduct_mulVec_pos hv).ne'
  exact h3 (by linear_combination (-1 / 2 : ℂ) * h2)

/- English proof (translation)
Establish `e2 : ((S.map σ)ᵀ).map θ = (S.map θ)ᴴ` using `Matrix.ext fun i j => h _`. Establish `e4` using `congrArg Matrix.transpose hS`. Rewrite `e4` using `[Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_transpose, Matrix.transpose_zero]`. Establish `e3 : (J * S + (S.map σ)ᵀ * J).map θ = (0 : Matrix _ _ _).map θ` using `by rw [e4]`. Rewrite `e3` using `[Matrix.map_add _ (map_add θ), Matrix.map_mul, Matrix.map_mul, e2, Matrix.map_zero _ (map_zero θ), add_comm]`.

Use `det_one_add_ne_zero hJ e3` as an intermediate fact. Rewrite using `[RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_add _ (map_add θ), Matrix.map_one _ (map_zero θ) (map_one θ)]` and apply the resulting hypothesis.
-/
theorem map_det_one_add_ne_zero {R : Type} [CommRing R] (σ : R →+* R) (θ : R →+* ℂ)
    (h : ∀ z, θ (σ z) = starRingEnd ℂ (θ z)) {n : ℕ} {J S : Matrix (Fin n) (Fin n) R} (hJ : (J.map θ).PosDef)
    (hS : Sᵀ * Jᵀ + Jᵀ * S.map σ = 0) : θ (1 + S).det ≠ 0 := by
  have e2 : ((S.map σ)ᵀ).map θ = (S.map θ)ᴴ := Matrix.ext fun i j => h _
  have e4 := congrArg Matrix.transpose hS
  rw [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.transpose_transpose, Matrix.transpose_zero] at e4
  have e3 : (J * S + (S.map σ)ᵀ * J).map θ = (0 : Matrix _ _ _).map θ := by rw [e4]
  rw [Matrix.map_add _ (map_add θ), Matrix.map_mul, Matrix.map_mul, e2, Matrix.map_zero _ (map_zero θ),
    add_comm] at e3
  have := det_one_add_ne_zero hJ e3
  rwa [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_add _ (map_add θ),
    Matrix.map_one _ (map_zero θ) (map_one θ)]

open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Use `haveI : ∀ w : InfinitePlace F, PreconnectedSpace w.Completion := fun w => by`. Break down `w.isReal_or_isComplex with hw | hw` into its components or cases. Set `e` to `(InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm`. Conclude with `(e.surjective.connectedSpace e.continuous).toPreconnectedSpace`. Set `e` to `(InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).symm`.

Conclude with `(e.surjective.connectedSpace e.continuous).toPreconnectedSpace`. Conclude with `inferInstanceAs (PreconnectedSpace (∀ w : InfinitePlace F, w.Completion))`.
-/
theorem preconnected_infAdele (F : Type) [Field F] [NumberField F] : PreconnectedSpace (Ainf F) := by
  haveI : ∀ w : InfinitePlace F, PreconnectedSpace w.Completion := fun w => by
    rcases w.isReal_or_isComplex with hw | hw
    · let e := (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm
      exact (e.surjective.connectedSpace e.continuous).toPreconnectedSpace
    · let e := (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).symm
      exact (e.surjective.connectedSpace e.continuous).toPreconnectedSpace
  exact inferInstanceAs (PreconnectedSpace (∀ w : InfinitePlace F, w.Completion))

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push Not at h`. Establish `hs : Function.Surjective (algebraMap D.host.F D.host.E)` using `fun z => (D.sp.cm.fixed z).1 (h z)`. Establish `h1 : Module.finrank D.host.F D.host.E = 1` using `Algebra.finrank_eq_one_iff_bijective_algebraMap.2 ⟨(algebraMap D.host.F D.host.E).injective, hs⟩`. Establish `h2` using `D.sp.cm.deg2`.

Use linear arithmetic over natural numbers and integers.
-/
theorem exists_conj_ne (D : D7) : ∃ z, D.sp.cm.sig z ≠ z := by
  by_contra h
  push Not at h
  have hs : Function.Surjective (algebraMap D.host.F D.host.E) := fun z => (D.sp.cm.fixed z).1 (h z)
  have h1 : Module.finrank D.host.F D.host.E = 1 :=
    Algebra.finrank_eq_one_iff_bijective_algebraMap.2 ⟨(algebraMap D.host.F D.host.E).injective, hs⟩
  have h2 := D.sp.cm.deg2
  omega

/- English proof (translation)
Use `haveI : IsArtinianRing (Ainf D.host.F) := inferInstanceAs (IsArtinianRing (∀ v : InfinitePlace D.host.F, v.Completion))`. Use `haveI : IsArtinianRing (Ainf D.host.F ⊗[D.host.F] D.host.E) := IsArtinianRing.of_finite (Ainf D.host.F) _`. Use `haveI : IsTopologicalRing (Ainf D.host.F ⊗[D.host.F] D.host.E) := IsModuleTopology.isTopologicalRing (Ainf D.host.F) _`. Use `haveI := preconnected_infAdele D.host.F`. Establish `a1 : IsOpen {x : (∀ v : InfinitePlace D.host.F, v.Completion) | IsUnit x}` using `Units.isOpen`.

Establish `a2 : ∀ x : (∀ v : InfinitePlace D.host.F, v.Completion), IsUnit x → ContinuousAt Ring.inverse x`. Introduce and unpack `_ ⟨x, rfl⟩`. Conclude with `NormedRing.inverse_continuousAt x`. Establish `b1 : IsOpen {x : Ainf D.host.F | IsUnit x}` using `a1`. Establish `b2 : ∀ x : Ainf D.host.F, IsUnit x → ContinuousAt Ring.inverse x` using `a2`.

Take `⟨-, h2⟩` from `GlobalTheory.RealApprox.units_of_free (A := Ainf D.host.F) (R := Ainf D.host.F ⊗[D.host.F] D.host.E) (Algebra.TensorProduct.basis (Ainf D.host.F) (Module.finBasis D.host.F D.host.E)) b1 b2`. Take `⟨⟨θ, hθ⟩, H⟩` from `GlobalTheory.Member.infiniteAdele_bijective D`. Take `⟨-, hcj, hb⟩` from `H θ hθ`. Establish `hunit : ∀ z, (∀ τ, θ τ z ≠ 0) → IsUnit z` using `fun z hz => by`. Take `⟨w, hw⟩` from `hb.2 fun τ => (θ τ.1 z)⁻¹`.

Use `IsUnit.of_mul_eq_one w (hb.1 (funext fun τ => ?_))` and prove the remaining obligations. Use `congrFun hw τ` as an intermediate fact. Simplify using `only at this ⊢`. Rewrite using `[map_mul, this, map_one, mul_inv_cancel₀ (hz _)]`. Establish `hσι : ∀ x, sigR (Ainf D.host.F) D.sp.cm.sig (inclR (F` using `D.host.F) (Ainf D.host.F) x) = inclR (F := D.host.F) (Ainf D.host.F) ((D.sp.cm.sig : D.host.E →+* D.host.E) x) := fun x => by`.

Simplify using `[sigR, inclR]`. Establish `hsm : Continuous fun a : Ainf D.host.F => a • (1 : Ainf D.host.F ⊗[D.host.F] D.host.E)` using `Continuous.smul (f := fun a : Ainf D.host.F => a) (g := fun _ : Ainf D.host.F => (1 : Ainf D.host.F ⊗[D.host.F] D.host.E)) continuous_id continuous_const`. Use `preconnected_unitary (A := Ainf D.host.F) (inclR (F := D.host.F) (Ainf D.host.F)) (D.sp.cm.sig : D.host.E →+* D.host.E) (sigR (Ainf D.host.F) D.sp.cm.sig) hσι (fun x => star_star x) (exists_conj_ne D) (fun x => hb.1 (funext fun τ => ?_)) h2 (fun a => a • 1) hsm (fun a => ?_) 0 1 …` and prove the remaining obligations. Simplify using `only [hcj, Complex.conj_conj]`. Simplify using `[sigR, Algebra.TensorProduct.one_def, TensorProduct.smul_tmul']`.

Use extensionality with `i j`. Conclude with `(hσι _).trans (congrArg _ (congrFun (congrFun (GlobalTheory.AutFunCounterexample.gram_herm V) i) j))`. Use `(GlobalTheory.AutFunCounterexample.gram_det_ne V).isUnit.map (inclR (F := D.host.F) (Ainf D.host.F))` as an intermediate fact. Rewrite `this` using `[RingHom.map_det]`. Then use the resulting hypothesis. Establish `hJ : (V.gram.map τ).PosDef` using `GlobalTheory.DefiniteQuotient.posDef_of_signature (p := V.rank) (by`.

Use `hs τ` as an intermediate fact. Rewrite using `[hp τ] at this)` and apply the resulting hypothesis. Establish `e1 : (JR (F` using `D.host.F) (Ainf D.host.F) V.gram).map (θ τ) = V.gram.map τ := Matrix.ext fun _ _ => (hθ τ).1 _`. Conclude with `map_det_one_add_ne_zero _ (θ τ) (hcj τ) (e1 ▸ hJ) hS`.
-/
theorem preconnected_inf {D : D7} (V : HSp D) (hp : V.IsPosDef) (hs : V.SigOK) :
    PreconnectedSpace (HA (Ainf D.host.F) D.sp.cm.sig V.gram) := by
  classical
  haveI : IsArtinianRing (Ainf D.host.F) :=
    inferInstanceAs (IsArtinianRing (∀ v : InfinitePlace D.host.F, v.Completion))
  haveI : IsArtinianRing (Ainf D.host.F ⊗[D.host.F] D.host.E) := IsArtinianRing.of_finite (Ainf D.host.F) _
  haveI : IsTopologicalRing (Ainf D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (Ainf D.host.F) _
  haveI := preconnected_infAdele D.host.F
  have a1 : IsOpen {x : (∀ v : InfinitePlace D.host.F, v.Completion) | IsUnit x} := Units.isOpen
  have a2 : ∀ x : (∀ v : InfinitePlace D.host.F, v.Completion), IsUnit x → ContinuousAt Ring.inverse x := by
    rintro _ ⟨x, rfl⟩
    exact NormedRing.inverse_continuousAt x
  have b1 : IsOpen {x : Ainf D.host.F | IsUnit x} := a1
  have b2 : ∀ x : Ainf D.host.F, IsUnit x → ContinuousAt Ring.inverse x := a2
  obtain ⟨-, h2⟩ := GlobalTheory.RealApprox.units_of_free (A := Ainf D.host.F) (R := Ainf D.host.F ⊗[D.host.F] D.host.E)
    (Algebra.TensorProduct.basis (Ainf D.host.F) (Module.finBasis D.host.F D.host.E)) b1 b2
  obtain ⟨⟨θ, hθ⟩, H⟩ := GlobalTheory.Member.infiniteAdele_bijective D
  obtain ⟨-, hcj, hb⟩ := H θ hθ
  have hunit : ∀ z, (∀ τ, θ τ z ≠ 0) → IsUnit z := fun z hz => by
    obtain ⟨w, hw⟩ := hb.2 fun τ => (θ τ.1 z)⁻¹
    refine IsUnit.of_mul_eq_one w (hb.1 (funext fun τ => ?_))
    have := congrFun hw τ
    simp only at this ⊢
    rw [map_mul, this, map_one, mul_inv_cancel₀ (hz _)]
  have hσι : ∀ x, sigR (Ainf D.host.F) D.sp.cm.sig (inclR (F := D.host.F) (Ainf D.host.F) x) =
      inclR (F := D.host.F) (Ainf D.host.F) ((D.sp.cm.sig : D.host.E →+* D.host.E) x) := fun x => by
    simp [sigR, inclR]
  have hsm : Continuous fun a : Ainf D.host.F => a • (1 : Ainf D.host.F ⊗[D.host.F] D.host.E) :=
    Continuous.smul (f := fun a : Ainf D.host.F => a)
      (g := fun _ : Ainf D.host.F => (1 : Ainf D.host.F ⊗[D.host.F] D.host.E)) continuous_id continuous_const
  refine preconnected_unitary (A := Ainf D.host.F) (inclR (F := D.host.F) (Ainf D.host.F))
    (D.sp.cm.sig : D.host.E →+* D.host.E) (sigR (Ainf D.host.F) D.sp.cm.sig) hσι (fun x => star_star x)
    (exists_conj_ne D) (fun x => hb.1 (funext fun τ => ?_)) h2 (fun a => a • 1) hsm
    (fun a => ?_) 0 1 (zero_smul _ _) (one_smul _ _) (JR (Ainf D.host.F) V.gram) ?_ ?_ fun S hS => hunit _ fun τ => ?_
  · simp only [hcj, Complex.conj_conj]
  · simp [sigR, Algebra.TensorProduct.one_def, TensorProduct.smul_tmul']
  · ext i j
    exact (hσι _).trans (congrArg _ (congrFun (congrFun (GlobalTheory.AutFunCounterexample.gram_herm V) i) j))
  · have := (GlobalTheory.AutFunCounterexample.gram_det_ne V).isUnit.map (inclR (F := D.host.F) (Ainf D.host.F))
    rwa [RingHom.map_det] at this
  · have hJ : (V.gram.map τ).PosDef := GlobalTheory.DefiniteQuotient.posDef_of_signature (p := V.rank) (by
      have := hs τ
      rwa [hp τ] at this)
    have e1 : (JR (F := D.host.F) (Ainf D.host.F) V.gram).map (θ τ) = V.gram.map τ :=
      Matrix.ext fun _ _ => (hθ τ).1 _
    exact map_det_one_add_ne_zero _ (θ τ) (hcj τ) (e1 ▸ hJ) hS

/- English proof (translation)
Introduce `D V c hp hs ⟨hfin, _, hcont, hnt, hirr⟩`. Establish `h3 : ∀ u ∈ GinfC V, ∀ N ∈ nhds u, ∃ γ ∈ GQ V, ∃ k ∈ GfC V, γ * k ∈ N ∧ γ * k ∈ GinfC V`. Introduce `u hu N hN`. Take `⟨U, hUN, hU, huU⟩` from `mem_nhds_iff.1 hN`. Take `⟨γ, hγ, k, hk, h1, h2⟩` from `GlobalTheory.RealApprox.weak_approx_real V u hu U hU huU`.

Conclude with `⟨γ, hγ, k, hk, hUN h1, h2⟩`. Use `⟨?_, fun U hU => hirr U fun h => ?_, h3⟩` and prove the remaining obligations. Use `haveI := preconnected_inf V hp hs haveI : IsTopologicalRing (Ainf D.host.F ⊗[D.host.F] D.host.E) := IsModuleTopology.isTopologicalRing (Ainf D.host.F) _ haveI : IsTopologicalGroup (HA (Ainf D.host.F) D.sp.cm.sig V.gram) := inferInstanceAs (IsTopologicalGroup (HR (Ainf D.host.F) D …`. Take `⟨e, he⟩` from `GlobalTheory.Mem.VolSplit.exists_adelic_split D.host.F D.host.E D.sp.cm.sig V.rank V.gram`. Establish `hGi : ∀ h : GA D V, (e h).2 = 1 → h ∈ GinfC V` using `fun h H => MonoidHom.mem_ker.2 (Units.ext ((he h).1.symm.trans (by rw [H]; rfl)))`.

Establish `hGf : ∀ h : GA D V, h ∈ GfC V ↔ (e h).1 = 1` using `fun h => ⟨fun H => Subtype.ext (Units.ext ((he h).2.trans (congrArg Units.val (MonoidHom.mem_ker.1 H)))), fun H => MonoidHom.mem_ker.2 (Units.ext ((he h).2.symm.trans (by rw [H]; rfl)))⟩`. Set `φ : GQ V →* HA (Ainf D.host.F) D.sp.cm.sig V.gram` to `(MonoidHom.fst _ _).comp (e.toMulEquiv.toMonoidHom.comp (GQ V).subtype)`. Establish `hφ : ∀ γ : GQ V, φ γ = (e γ.1).1` using `fun _ => rfl`. Establish `hd : DenseRange φ`. Use `dense_iff_inter_open.2 ?_` and prove the remaining obligations.

Introduce and unpack `O hO ⟨x, hx⟩`. Take `⟨γ, hγ, k, hk, h1, -⟩` from `h3 (e.symm (x, 1)) (hGi _ (by rw [e.apply_symm_apply])) {g | (e g).1 ∈ O} ((hO.preimage (continuous_fst.comp e.continuous)).mem_nhds (by`. Express the relevant statement in the definitionally equal form `(e (e.symm (x, 1))).1 ∈ O`. Rewrite using `[e.apply_symm_apply]))` and apply the resulting hypothesis. Use `⟨_, ?_, ⟨γ, hγ⟩, rfl⟩` and prove the remaining obligations.

Rewrite `h1` using `[Set.mem_setOf_eq, map_mul, Prod.fst_mul, (hGf k).1 hk, mul_one]`. Then use the resulting hypothesis. Establish `htr : Continuous fun h : GA D V => LinearMap.trace ℂ c.W (c.ρ h)`. Set `b` to `Module.finBasis ℂ c.W`. Simplify using `only [LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply]`. Conclude with `continuous_finset_sum _ fun i _ => (b.coord i).continuous_of_finiteDimensional.comp (hcont (b i))`.

Establish `hc : Continuous fun x : HA (Ainf D.host.F) D.sp.cm.sig V.gram => e.symm (x, 1)` using `e.symm.continuous.comp (continuous_id.prodMk continuous_const)`. Establish `key` using `closure_preimage_eq_top φ hd {x | LinearMap.trace ℂ c.W (c.ρ (e.symm (x, 1))) ≠ 0} (isOpen_ne_fun (htr.comp hc) continuous_const) (by`. Express the relevant statement in the definitionally equal form `LinearMap.trace ℂ c.W (c.ρ (e.symm 1)) ≠ 0`. Rewrite using `[map_one, map_one, LinearMap.trace_one]`. Conclude with `(Module.finrank_pos (R := ℂ) (M := c.W)).ne')` after adjusting the coercions.

Rewrite using `[← key]`. Use `congr 1`. Use extensionality with `γ`. Establish `e1 : c.ρ γ = c.ρ (e.symm (φ γ, 1))`. Establish `hk : (γ : GA D V)⁻¹ * e.symm (φ γ, 1) ∈ GfC V` using `(hGf _).2 (by`.

Rewrite using `[map_mul, map_inv, e.apply_symm_apply, Prod.fst_mul, Prod.fst_inv, hφ, inv_mul_cancel])`. Rewrite using `[← mul_inv_cancel_left (γ : GA D V) (e.symm (φ γ, 1)), map_mul, hfin _ hk, mul_one]`. Rewrite using `[Set.mem_setOf_eq, e1]`. Both sides reduce to the same expression. Introduce and unpack `_ ⟨x, hx, rfl⟩`.

Take `⟨a, ha, k, hk, rfl⟩` from `(GlobalTheory.UnitarySplit.real_finite_split D V).1 h`. Rewrite using `[map_mul, hfin k hk, mul_one]`. Assume the negation of the conclusion as `hn`. Take `⟨γ, hγ, k', hk', h1, -⟩` from `h3 a ha {g | c.ρ g x ∉ U} ((U.closed_of_finiteDimensional.isOpen_compl.preimage (hcont x)).mem_nhds hn)`. Rewrite `h1` using `[Set.mem_setOf_eq, map_mul, hfin k' hk', mul_one]`.

Conclude with `h1 (hU ⟨γ, hγ⟩ ⟨x, hx, rfl⟩)`.
-/
theorem rational_points_generate : ∀ (D : D7) (V : HSp D) (c : CoefA V), V.IsPosDef → V.SigOK → c.Is → Subgroup.closure {γ : GQ V | LinearMap.trace ℂ c.W (c.ρ γ) ≠ 0} = ⊤ ∧ (∀ U : Submodule ℂ c.W, (∀ γ : GQ V, U.map (c.ρ γ) ≤ U) → U = ⊥ ∨ U = ⊤) ∧ ∀ u ∈ GinfC V, ∀ N ∈ nhds u, ∃ γ ∈ GQ V, ∃ k ∈ GfC V, γ * k ∈ N ∧ γ * k ∈ GinfC V := by
  intro D V c hp hs ⟨hfin, _, hcont, hnt, hirr⟩
  have h3 : ∀ u ∈ GinfC V, ∀ N ∈ nhds u, ∃ γ ∈ GQ V, ∃ k ∈ GfC V, γ * k ∈ N ∧ γ * k ∈ GinfC V := by
    intro u hu N hN
    obtain ⟨U, hUN, hU, huU⟩ := mem_nhds_iff.1 hN
    obtain ⟨γ, hγ, k, hk, h1, h2⟩ := GlobalTheory.RealApprox.weak_approx_real V u hu U hU huU
    exact ⟨γ, hγ, k, hk, hUN h1, h2⟩
  refine ⟨?_, fun U hU => hirr U fun h => ?_, h3⟩
  · haveI := preconnected_inf V hp hs
    haveI : IsTopologicalRing (Ainf D.host.F ⊗[D.host.F] D.host.E) :=
      IsModuleTopology.isTopologicalRing (Ainf D.host.F) _
    haveI : IsTopologicalGroup (HA (Ainf D.host.F) D.sp.cm.sig V.gram) :=
      inferInstanceAs (IsTopologicalGroup (HR (Ainf D.host.F) D.sp.cm.sig V.gram))
    obtain ⟨e, he⟩ := GlobalTheory.Mem.VolSplit.exists_adelic_split D.host.F D.host.E D.sp.cm.sig V.rank V.gram
    have hGi : ∀ h : GA D V, (e h).2 = 1 → h ∈ GinfC V := fun h H =>
      MonoidHom.mem_ker.2 (Units.ext ((he h).1.symm.trans (by rw [H]; rfl)))
    have hGf : ∀ h : GA D V, h ∈ GfC V ↔ (e h).1 = 1 := fun h =>
      ⟨fun H => Subtype.ext (Units.ext ((he h).2.trans (congrArg Units.val (MonoidHom.mem_ker.1 H)))),
        fun H => MonoidHom.mem_ker.2 (Units.ext ((he h).2.symm.trans (by rw [H]; rfl)))⟩
    let φ : GQ V →* HA (Ainf D.host.F) D.sp.cm.sig V.gram :=
      (MonoidHom.fst _ _).comp (e.toMulEquiv.toMonoidHom.comp (GQ V).subtype)
    have hφ : ∀ γ : GQ V, φ γ = (e γ.1).1 := fun _ => rfl
    have hd : DenseRange φ := by
      refine dense_iff_inter_open.2 ?_
      rintro O hO ⟨x, hx⟩
      obtain ⟨γ, hγ, k, hk, h1, -⟩ := h3 (e.symm (x, 1)) (hGi _ (by rw [e.apply_symm_apply])) {g | (e g).1 ∈ O}
        ((hO.preimage (continuous_fst.comp e.continuous)).mem_nhds (by
          change (e (e.symm (x, 1))).1 ∈ O
          rwa [e.apply_symm_apply]))
      refine ⟨_, ?_, ⟨γ, hγ⟩, rfl⟩
      rwa [Set.mem_setOf_eq, map_mul, Prod.fst_mul, (hGf k).1 hk, mul_one] at h1
    have htr : Continuous fun h : GA D V => LinearMap.trace ℂ c.W (c.ρ h) := by
      let b := Module.finBasis ℂ c.W
      simp only [LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply]
      exact continuous_finset_sum _ fun i _ => (b.coord i).continuous_of_finiteDimensional.comp (hcont (b i))
    have hc : Continuous fun x : HA (Ainf D.host.F) D.sp.cm.sig V.gram => e.symm (x, 1) :=
      e.symm.continuous.comp (continuous_id.prodMk continuous_const)
    have key := closure_preimage_eq_top φ hd {x | LinearMap.trace ℂ c.W (c.ρ (e.symm (x, 1))) ≠ 0}
      (isOpen_ne_fun (htr.comp hc) continuous_const) (by
        change LinearMap.trace ℂ c.W (c.ρ (e.symm 1)) ≠ 0
        rw [map_one, map_one, LinearMap.trace_one]
        exact_mod_cast (Module.finrank_pos (R := ℂ) (M := c.W)).ne')
    rw [← key]
    congr 1
    ext γ
    have e1 : c.ρ γ = c.ρ (e.symm (φ γ, 1)) := by
      have hk : (γ : GA D V)⁻¹ * e.symm (φ γ, 1) ∈ GfC V := (hGf _).2 (by
        rw [map_mul, map_inv, e.apply_symm_apply, Prod.fst_mul, Prod.fst_inv, hφ, inv_mul_cancel])
      rw [← mul_inv_cancel_left (γ : GA D V) (e.symm (φ γ, 1)), map_mul, hfin _ hk, mul_one]
    rw [Set.mem_setOf_eq, e1]
    rfl
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨a, ha, k, hk, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D V).1 h
    rw [map_mul, hfin k hk, mul_one]
    by_contra hn
    obtain ⟨γ, hγ, k', hk', h1, -⟩ := h3 a ha {g | c.ρ g x ∉ U}
      ((U.closed_of_finiteDimensional.isOpen_compl.preimage (hcont x)).mem_nhds hn)
    rw [Set.mem_setOf_eq, map_mul, hfin k' hk', mul_one] at h1
    exact h1 (hU ⟨γ, hγ⟩ ⟨x, hx, rfl⟩)

end GlobalTheory.RatGen

end
