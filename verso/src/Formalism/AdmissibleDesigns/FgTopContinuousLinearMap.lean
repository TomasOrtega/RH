import Formalism.WachLatticeTwists.RealDisplaySplitting.GaloisTheoremThirdForms

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

namespace Formalism.MainNotions.N.KLat

open Matrix
open Formalism.NG Formalism.RepresentationBoundsCohomology.LOC Formalism.RepresentationBoundsCohomology.FIN Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology ReciprocityTheory.Gal
open ReciprocityTheory.ChartRestriction.T2 (PadicCoeff FracTop IsFGTop)

/- English proof (translation)
Use `haveI := hO.ring`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Establish `hne : (Ideal.span {a} : Ideal O) ≠ ⊥` using `by rwa [Ne, Ideal.span_singleton_eq_bot]`. Take `⟨k, hk⟩` from `IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hne hϖ`. Establish `hm : IsLocalRing.maximalIdeal O = Ideal.span {ϖ}` using `(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ`.

Establish `h` using `(isAdic_iff.1 hO.adic).1 k`. Rewrite `h` using `[hm, Ideal.span_singleton_pow]`. Rewrite using `[hk]`. Conclude with `h`.
-/
theorem padic_isOpen_span {ℓ : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
    (hO : PadicCoeff ℓ O) {a : O} (ha : a ≠ 0) : IsOpen ((Ideal.span {a} : Ideal O) : Set O) := by
  haveI := hO.ring
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hne : (Ideal.span {a} : Ideal O) ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
  obtain ⟨k, hk⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hne hϖ
  have hm : IsLocalRing.maximalIdeal O = Ideal.span {ϖ} := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  have h := (isAdic_iff.1 hO.adic).1 k
  rw [hm, Ideal.span_singleton_pow] at h
  rw [hk]
  exact h

/- English proof (translation)
Use `haveI := hO.compact`. Use `haveI := hR.t2`. Use `haveI := hR.csmul`. Use `haveI := hR.fg`. Take `⟨k, π, hπ⟩` from `Module.Finite.exists_fin' O M`.

Establish `hπc : Continuous π` using `LinearMap.continuous_on_pi π`. Establish `hq : Topology.IsQuotientMap π` using `hπc.isClosedMap.isQuotientMap hπc hπ`. Rewrite using `[hq.continuous_iff]`. Conclude with `LinearMap.continuous_on_pi (f.comp π)`.
-/
theorem fgTop_continuous_linearMap {ℓ : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] {M N : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M] [ContinuousAdd M]
    [AddCommGroup N] [Module O N] [TopologicalSpace N] [ContinuousAdd N] [ContinuousSMul O N]
    (hR : IsFGTop O M) (hO : PadicCoeff ℓ O) (f : M →ₗ[O] N) : Continuous f := by
  haveI := hO.compact
  haveI := hR.t2
  haveI := hR.csmul
  haveI := hR.fg
  obtain ⟨k, π, hπ⟩ := Module.Finite.exists_fin' O M
  have hπc : Continuous π := LinearMap.continuous_on_pi π
  have hq : Topology.IsQuotientMap π := hπc.isClosedMap.isQuotientMap hπc hπ
  rw [hq.continuous_iff]
  exact LinearMap.continuous_on_pi (f.comp π)

section Gen

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {n : Type} [Fintype n] [DecidableEq n]

def matK (A : Matrix n n O) : Matrix n n (FractionRing O) := A.map (algebraMap O (FractionRing O))

/- English proof (translation)
Conclude with `Matrix.map_mul`.
-/
theorem matK_mul (A B : Matrix n n O) : matK (A * B) = matK A * matK B := by
  exact Matrix.map_mul

/- English proof (translation)
Conclude with `Matrix.map_one _ (map_zero _) (map_one _)`.
-/
theorem matK_one : matK (1 : Matrix n n O) = 1 := by
  exact Matrix.map_one _ (map_zero _) (map_one _)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem matK_transpose (A : Matrix n n O) : matK Aᵀ = (matK A)ᵀ := rfl

/- English proof (translation)
Simplify using `only [matK, Matrix.mulVec, dotProduct, Matrix.map_apply, Algebra.smul_def]`.
-/
theorem matK_mulVec (A : Matrix n n O) (v : n → FractionRing O) (a : n) :
    (matK A *ᵥ v) a = ∑ j, A a j • v j := by
  simp only [matK, Matrix.mulVec, dotProduct, Matrix.map_apply, Algebra.smul_def]

/- English proof (translation)
Use function extensionality and compare the values at `a`. Simplify using `only [matK, Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]`.
-/
theorem matK_mulVec_alg (A : Matrix n n O) (y : n → O) :
    matK A *ᵥ (fun a => algebraMap O (FractionRing O) (y a)) =
      fun a => algebraMap O (FractionRing O) ((A *ᵥ y) a) := by
  funext a
  simp only [matK, Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]

variable {Γ : Type} [Group Γ]

def repV (M : Γ →* Matrix n n O) : Representation O Γ (n → FractionRing O) where
  toFun g := (Matrix.mulVecLin (matK (M g))).restrictScalars O
  map_one' := by
    refine LinearMap.ext fun v => ?_
    simp [matK_one]
  map_mul' g h := by
    refine LinearMap.ext fun v => ?_
    simp [matK_mul, Matrix.mulVec_mulVec]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem repV_apply (M : Γ →* Matrix n n O) (g : Γ) (v : n → FractionRing O) :
    repV M g v = matK (M g) *ᵥ v := rfl

def repV' (ε : Γ →* Oˣ) (M : Γ →* Matrix n n O) : Representation O Γ (n → FractionRing O) where
  toFun g := ((ε g : Oˣ) : O) • (Matrix.mulVecLin (matK (M g⁻¹)ᵀ)).restrictScalars O
  map_one' := by
    refine LinearMap.ext fun v => ?_
    simp [matK_one]
  map_mul' g h := by
    refine LinearMap.ext fun v => ?_
    simp only [map_mul, Units.val_mul, LinearMap.smul_apply,
      LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply, Module.End.mul_apply, Matrix.mulVec_smul, smul_smul]
    rw [_root_.mul_inv_rev, map_mul, Matrix.transpose_mul, matK_mul, ← Matrix.mulVec_mulVec]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem repV'_apply (ε : Γ →* Oˣ) (M : Γ →* Matrix n n O) (g : Γ) (v : n → FractionRing O) :
    repV' ε M g v = ((ε g : Oˣ) : O) • (matK (M g⁻¹)ᵀ *ᵥ v) := rfl

def repL' (ε : Γ →* Oˣ) (M : Γ →* Matrix n n O) : Representation O Γ (n → O) where
  toFun g := ((ε g : Oˣ) : O) • Matrix.mulVecLin (M g⁻¹)ᵀ
  map_one' := by
    refine LinearMap.ext fun v => ?_
    simp
  map_mul' g h := by
    refine LinearMap.ext fun v => ?_
    simp only [map_mul, Units.val_mul, LinearMap.smul_apply,
      Matrix.mulVecLin_apply, Module.End.mul_apply, Matrix.mulVec_smul, smul_smul]
    rw [_root_.mul_inv_rev, map_mul, Matrix.transpose_mul, ← Matrix.mulVec_mulVec]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem repL'_apply (ε : Γ →* Oˣ) (M : Γ →* Matrix n n O) (g : Γ) (v : n → O) :
    repL' ε M g v = ((ε g : Oˣ) : O) • ((M g⁻¹)ᵀ *ᵥ v) := rfl

def pairStd : (n → FractionRing O) →ₗ[O] (n → FractionRing O) →ₗ[O] FractionRing O :=
  LinearMap.mk₂ O (fun x y => x ⬝ᵥ y) (fun x x' y => add_dotProduct x x' y)
    (fun c x y => smul_dotProduct c x y) (fun x y y' => dotProduct_add x y y')
    (fun c x y => dotProduct_smul c x y)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pairStd_apply (x y : n → FractionRing O) : pairStd x y = x ⬝ᵥ y := rfl

def latT : Submodule O (n → FractionRing O) :=
  Submodule.pi Set.univ (fun _ => (1 : Submodule O (FractionRing O)))

/- English proof (translation)
Simplify using `only [latT, Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.mem_one]`. Prove the components needed by the constructor for the conclusion. Introduce `h choose y hy using h`. Conclude with `⟨y, funext fun a => (hy a).symm⟩`. Introduce and unpack `⟨y, rfl⟩ a`.

Conclude with `⟨y a, rfl⟩`.
-/
theorem mem_latT (x : n → FractionRing O) :
    x ∈ (latT : Submodule O (n → FractionRing O)) ↔ ∃ y : n → O, x = fun a => algebraMap O _ (y a) := by
  simp only [latT, Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.mem_one]
  constructor
  · intro h
    choose y hy using h
    exact ⟨y, funext fun a => (hy a).symm⟩
  · rintro ⟨y, rfl⟩ a
    exact ⟨y a, rfl⟩

/- English proof (translation)
Introduce `g x hx`. Take `⟨y, rfl⟩` from `(mem_latT x).1 hx`. Use `(mem_latT _).2 ⟨M g *ᵥ y, ?_⟩` and prove the remaining obligations. Rewrite using `[repV_apply, matK_mulVec_alg]`.
-/
theorem latT_stable (M : Γ →* Matrix n n O) : StableUnder (repV M) (latT : Submodule O (n → FractionRing O)) := by
  intro g x hx
  obtain ⟨y, rfl⟩ := (mem_latT x).1 hx
  refine (mem_latT _).2 ⟨M g *ᵥ y, ?_⟩
  rw [repV_apply, matK_mulVec_alg]

/- English proof (translation)
Rewrite using `[← matK_mul, ← map_mul, inv_mul_cancel, map_one, matK_one]`.
-/
theorem matK_inv_mul (M : Γ →* Matrix n n O) (g : Γ) : matK (M g⁻¹) * matK (M g) = 1 := by
  rw [← matK_mul, ← map_mul, inv_mul_cancel, map_one, matK_one]

/- English proof (translation)
Introduce `g x f`. Rewrite using `[pairStd_apply, pairStd_apply, repV_apply, repV'_apply, dotProduct_smul, matK_transpose, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, Matrix.mulVec_mulVec, matK_inv_mul, Matrix.one_mulVec]`.
-/
theorem eq_pairStd (ε : Γ →* Oˣ) (M : Γ →* Matrix n n O) : EquivPair ε (repV M) (repV' ε M) pairStd := by
  intro g x f
  rw [pairStd_apply, pairStd_apply, repV_apply, repV'_apply, dotProduct_smul, matK_transpose,
    Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, Matrix.mulVec_mulVec, matK_inv_mul, Matrix.one_mulVec]

section Top
variable [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
  [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)] [TopologicalSpace Γ]

/- English proof (translation)
Use `show Continuous fun p : Γ × (n → FractionRing O) => repV' ε M p.1 p.2`. Use `continuous_pi fun a => ?_` and prove the remaining obligations. Simplify using `only [repV'_apply, Pi.smul_apply, matK_mulVec]`. Use `(hε.comp continuous_fst).smul ?_` and prove the remaining obligations. Use `continuous_finset_sum _ fun j _ => ?_` and prove the remaining obligations.

Conclude with `((hM a j).comp continuous_fst).smul ((continuous_apply j).comp continuous_snd)`.
-/
theorem contAction_repV' (ε : Γ →* Oˣ) (M : Γ →* Matrix n n O)
    (hε : Continuous fun g => ((ε g : Oˣ) : O)) (hM : ∀ a b, Continuous fun g => M g⁻¹ b a) :
    ContAction (repV' ε M) := by
  show Continuous fun p : Γ × (n → FractionRing O) => repV' ε M p.1 p.2
  refine continuous_pi fun a => ?_
  simp only [repV'_apply, Pi.smul_apply, matK_mulVec]
  refine (hε.comp continuous_fst).smul ?_
  refine continuous_finset_sum _ fun j _ => ?_
  exact ((hM a j).comp continuous_fst).smul ((continuous_apply j).comp continuous_snd)

/- English proof (translation)
Use `show Continuous fun p : Γ × (n → FractionRing O) => repV M p.1 p.2`. Use `continuous_pi fun a => ?_` and prove the remaining obligations. Simplify using `only [repV_apply, matK_mulVec]`. Conclude with `continuous_finset_sum _ fun j _ => ((hM a j).comp continuous_fst).smul ((continuous_apply j).comp continuous_snd)`.
-/
theorem contAction_repV (M : Γ →* Matrix n n O) (hM : ∀ a b, Continuous fun g => M g a b) :
    ContAction (repV M) := by
  show Continuous fun p : Γ × (n → FractionRing O) => repV M p.1 p.2
  refine continuous_pi fun a => ?_
  simp only [repV_apply, matK_mulVec]
  exact continuous_finset_sum _ fun j _ =>
    ((hM a j).comp continuous_fst).smul ((continuous_apply j).comp continuous_snd)

/- English proof (translation)
Simplify using `only [pairStd_apply, dotProduct]`. Conclude with `continuous_finset_sum _ fun i _ => ((continuous_apply i).comp continuous_fst).mul ((continuous_apply i).comp continuous_snd)`.
-/
theorem cont_pairStd [ContinuousMul (FractionRing O)] :
    Continuous fun p : (n → FractionRing O) × (n → FractionRing O) => pairStd p.1 p.2 := by
  simp only [pairStd_apply, dotProduct]
  exact continuous_finset_sum _ fun i _ =>
    ((continuous_apply i).comp continuous_fst).mul ((continuous_apply i).comp continuous_snd)

def datStd (hK : ContinuousMul (FractionRing O)) (ε : Γ →* Oˣ) (M : Γ →* Matrix n n O)
    (hε : Continuous fun g => ((ε g : Oˣ) : O)) (hM : ∀ a b, Continuous fun g => M g⁻¹ b a) :
    LatData O Γ (n → FractionRing O) (n → FractionRing O) where
  ε := ε
  ρT := repV M
  ρT' := repV' ε M
  bT := pairStd
  T := latT
  stT := latT_stable M
  eqT := eq_pairStd ε M
  contT' := contAction_repV' ε M hε hM
  contbT := haveI := hK; cont_pairStd
  inv := 0
  invF := 0

end Top

end Gen

section Iso

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {n : Type} [Fintype n] [DecidableEq n]

def vMap : (n → O) →ₗ[O] dualLat (pairStd (O := O) (n := n)) latT where
  toFun y := ⟨fun a => algebraMap O (FractionRing O) (y a), by
    intro x hx
    obtain ⟨z, rfl⟩ := (mem_latT x).1 hx
    refine Submodule.mem_one.2 ⟨∑ a, z a * y a, ?_⟩
    simp [pairStd_apply, dotProduct, map_sum, map_mul]⟩
  map_add' y y' := Subtype.ext (funext fun a => by simp)
  map_smul' c y := Subtype.ext (funext fun a => by simp [Algebra.smul_def])

/- English proof (translation)
Use `(mem_latT _).2 ⟨fun j => if a = j then 1 else 0, funext fun j => ?_⟩` and prove the remaining obligations. Apply the tactic sequence `by_cases h : a = j <;> simp [h]`.
-/
theorem unit_mem_latT (a : n) :
    (fun j => if a = j then (1 : FractionRing O) else 0) ∈ (latT : Submodule O (n → FractionRing O)) := by
  refine (mem_latT _).2 ⟨fun j => if a = j then 1 else 0, funext fun j => ?_⟩
  by_cases h : a = j <;> simp [h]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `y y' h`. Use function extensionality and compare the values at `a`. Establish `h'` using `congrFun (congrArg Subtype.val h) a`. Conclude with `IsFractionRing.injective O (FractionRing O) h'`.

Introduce and unpack `⟨f, hf⟩`. Establish `h : ∀ a, ∃ y : O, algebraMap O (FractionRing O) y = f a`. Introduce `a`. Establish `h1` using `hf _ (unit_mem_latT a)`. Rewrite `h1` using `[pairStd_apply]`.

Simplify `h1` using `[dotProduct, Submodule.mem_one]`. Use `choose y hy using h`. Conclude with `⟨y, Subtype.ext (funext fun a => hy a)⟩`.
-/
theorem vMap_bij : Function.Bijective (vMap (O := O) (n := n)) := by
  constructor
  · intro y y' h
    funext a
    have h' := congrFun (congrArg Subtype.val h) a
    exact IsFractionRing.injective O (FractionRing O) h'
  · rintro ⟨f, hf⟩
    have h : ∀ a, ∃ y : O, algebraMap O (FractionRing O) y = f a := by
      intro a
      have h1 := hf _ (unit_mem_latT a)
      rw [pairStd_apply] at h1
      simpa [dotProduct, Submodule.mem_one] using h1
    choose y hy using h
    exact ⟨y, Subtype.ext (funext fun a => hy a)⟩

def vStd : (n → O) ≃ₗ[O] dualLat (pairStd (O := O) (n := n)) latT :=
  LinearEquiv.ofBijective vMap vMap_bij

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem vStd_apply (y : n → O) (a : n) :
    ((vStd y : dualLat (pairStd (O := O) (n := n)) latT) : n → FractionRing O) a = algebraMap O _ (y a) := rfl

def uStd : (n → KO O) ≃ₗ[O] (n → FractionRing O) ⧸ (latT : Submodule O (n → FractionRing O)) :=
  (Submodule.quotientPi (fun _ : n => (1 : Submodule O (FractionRing O)))).symm

/- English proof (translation)
Apply `(uStd (O := O) (n := n)).symm.injective` to reduce the goal to its premises. Rewrite using `[LinearEquiv.symm_apply_apply]`. Use function extensionality and compare the values at `a`. Use `first`. Consider the case `rfl`.

Consider the case `exact (Submodule.quotientPi_apply _ _ _).symm`.
-/
theorem uStd_mk (x : n → FractionRing O) :
    uStd (fun a => toKO O (x a)) = Submodule.Quotient.mk x := by
  apply (uStd (O := O) (n := n)).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  funext a
  first
    | rfl
    | exact (Submodule.quotientPi_apply _ _ _).symm

def gamStd : (n → O) →ₗ[O] (n → KO O) →ₗ[O] KO O :=
  LinearMap.mk₂ O (fun t m => ∑ a, t a • m a)
    (fun t t' m => by simp [add_smul, Finset.sum_add_distrib])
    (fun c t m => by simp [Finset.smul_sum, mul_smul])
    (fun t m m' => by simp [smul_add, Finset.sum_add_distrib])
    (fun c t m => by simp [Finset.smul_sum, smul_comm c])

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem gamStd_apply (t : n → O) (m : n → KO O) : gamStd t m = ∑ a, t a • m a := rfl

/- English proof (translation)
Take `⟨x, rfl⟩ : ∃ x : n → FractionRing O, (fun a => toKO O (x a)) = m` from `⟨fun a => (Submodule.Quotient.mk_surjective _ (m a)).choose,`. Use function extensionality and compare the values at `fun a => (Submodule.Quotient.mk_surjective _ (m a)).choose_spec⟩`. Rewrite using `[uStd_mk, gamStd_apply]`. Simplify using `only [pairKO, Submodule.liftQ_apply, LinearMap.compr₂_apply, LinearMap.compl₂_apply, Submodule.subtype_apply, pairStd_apply, dotProduct, vStd_apply]`. Rewrite using `[map_sum]`.

Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[← map_smul, Algebra.smul_def, mul_comm]`.
-/
theorem gamStd_eq (t : n → O) (m : n → KO O) :
    gamStd t m = pairKO (pairStd (O := O) (n := n)) (latT (O := O) (n := n)) (uStd m) (vStd t) := by
  obtain ⟨x, rfl⟩ : ∃ x : n → FractionRing O, (fun a => toKO O (x a)) = m :=
    ⟨fun a => (Submodule.Quotient.mk_surjective _ (m a)).choose,
      funext fun a => (Submodule.Quotient.mk_surjective _ (m a)).choose_spec⟩
  rw [uStd_mk, gamStd_apply]
  simp only [pairKO, Submodule.liftQ_apply, LinearMap.compr₂_apply, LinearMap.compl₂_apply,
    Submodule.subtype_apply, pairStd_apply, dotProduct, vStd_apply]
  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← map_smul, Algebra.smul_def, mul_comm]

end Iso

section RL

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
  [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
  {n : Type} [Fintype n] [DecidableEq n] {Γ : Type} [Group Γ] [TopologicalSpace Γ]

/- English proof (translation)
Use `haveI := hO.t2`. Use `IsTopologicalAddGroup.t2Space_of_zero_sep fun z hz => ?_` and prove the remaining obligations. Distinguish the cases in `h : z ∈ Set.range (algebraMap O (FractionRing O))`. Take `⟨w, rfl⟩` from `h`. Establish `hw : w ≠ 0`.

Introduce and unpack `rfl`. Conclude with `hz (map_zero _)`. Take `⟨U1, U2, hU1, _, h0, hw', hd⟩` from `t2_separation hw.symm`. Use `⟨algebraMap O _ '' U1, (hF.emb.isOpenMap U1 hU1).mem_nhds ⟨0, h0, map_zero _⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨v, hv, hvw⟩`.

Establish `hvw' : v = w` using `IsFractionRing.injective O (FractionRing O) hvw`. Substitute `hvw'` using the available equality. Conclude with `Set.disjoint_left.1 hd hv hw'`. Conclude with `⟨_, hF.emb.isOpen_range.mem_nhds ⟨0, map_zero _⟩, h⟩`.
-/
theorem t2Space_fractionRing_of_padicCoeff (ℓ : ℕ) (hO : PadicCoeff ℓ O) (hF : FracTop O) : T2Space (FractionRing O) := by
  haveI := hO.t2
  refine IsTopologicalAddGroup.t2Space_of_zero_sep fun z hz => ?_
  by_cases h : z ∈ Set.range (algebraMap O (FractionRing O))
  · obtain ⟨w, rfl⟩ := h
    have hw : w ≠ 0 := by
      rintro rfl
      exact hz (map_zero _)
    obtain ⟨U1, U2, hU1, _, h0, hw', hd⟩ := t2_separation hw.symm
    refine ⟨algebraMap O _ '' U1, (hF.emb.isOpenMap U1 hU1).mem_nhds ⟨0, h0, map_zero _⟩, ?_⟩
    rintro ⟨v, hv, hvw⟩
    have hvw' : v = w := IsFractionRing.injective O (FractionRing O) hvw
    subst hvw'
    exact Set.disjoint_left.1 hd hv hw'
  · exact ⟨_, hF.emb.isOpen_range.mem_nhds ⟨0, map_zero _⟩, h⟩

/- English proof (translation)
Use `haveI := hO.ring`. Establish `hpre : algebraMap O (FractionRing O) ⁻¹' U ∈ nhds (0 : O)` using `hF.emb.continuous.continuousAt.preimage_mem_nhds (by rwa [map_zero])`. Take `⟨k, hk⟩` from `(isAdic_iff.1 hO.adic).2 _ hpre`. Establish `hm : IsLocalRing.maximalIdeal O = Ideal.span {ϖ}` using `(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ`. Use `⟨k, ?_⟩` and prove the remaining obligations.

Rewrite using `[Set.image_subset_iff, ← Ideal.span_singleton_pow, ← hm]`. Conclude with `hk`.
-/
theorem frac_nhds {ℓ : ℕ} (hO : PadicCoeff ℓ O) (hF : FracTop O) {ϖ : O} (hϖ : Irreducible ϖ)
    {U : Set (FractionRing O)} (hU : U ∈ nhds (0 : FractionRing O)) :
    ∃ k : ℕ, algebraMap O (FractionRing O) '' ((Ideal.span {ϖ ^ k} : Ideal O) : Set O) ⊆ U := by
  haveI := hO.ring
  have hpre : algebraMap O (FractionRing O) ⁻¹' U ∈ nhds (0 : O) :=
    hF.emb.continuous.continuousAt.preimage_mem_nhds (by rwa [map_zero])
  obtain ⟨k, hk⟩ := (isAdic_iff.1 hO.adic).2 _ hpre
  have hm : IsLocalRing.maximalIdeal O = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  refine ⟨k, ?_⟩
  rw [Set.image_subset_iff, ← Ideal.span_singleton_pow, ← hm]
  exact hk

/- English proof (translation)
Conclude with `(hF.emb.isOpenMap _ (padic_isOpen_span hO ha)).mem_nhds ⟨0, (Ideal.span {a}).zero_mem, map_zero _⟩`.
-/
theorem frac_open {ℓ : ℕ} (hO : PadicCoeff ℓ O) (hF : FracTop O) {a : O} (ha : a ≠ 0) :
    algebraMap O (FractionRing O) '' ((Ideal.span {a} : Ideal O) : Set O) ∈ nhds (0 : FractionRing O) := by
  exact (hF.emb.isOpenMap _ (padic_isOpen_span hO ha)).mem_nhds ⟨0, (Ideal.span {a}).zero_mem, map_zero _⟩

/- English proof (translation)
Use `haveI := hO.ring`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Establish `hϖ0 : ϖ ≠ 0` using `hϖ.ne_zero`. Establish `key : ∀ x₀ : FractionRing O, Filter.Tendsto (fun x => x₀ * x) (nhds 0) (nhds 0)`. Introduce `x₀`.

Take `⟨⟨p, q⟩, hpq⟩` from `IsLocalization.surj (nonZeroDivisors O) x₀`. Establish `hpq' : x₀ * algebraMap O (FractionRing O) q = algebraMap O (FractionRing O) p` using `hpq`. Establish `hq0 : (q : O) ≠ 0` using `nonZeroDivisors.ne_zero q.2`. Use `Filter.tendsto_def.2 fun U hU => ?_` and prove the remaining obligations. Take `⟨k, hk⟩` from `frac_nhds hO hF hϖ (by simpa using hU)`.

Use `Filter.mem_of_superset (frac_open hO hF (mul_ne_zero hq0 (pow_ne_zero k hϖ0))) ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.1 hy`. Rewrite using `[Set.mem_preimage]`. Use `hk ⟨p * c * ϖ ^ k, Ideal.mem_span_singleton'.2 ⟨p * c, rfl⟩, ?_⟩` and prove the remaining obligations.

Simplify using `only [map_mul]`. Rewrite using `[← hpq']`. Expand and normalize the polynomial expressions, which then agree. Establish `hmul : Filter.Tendsto (Function.uncurry ((· * ·) : FractionRing O → FractionRing O → FractionRing O)) (nhds 0 ×ˢ nhds 0) (nhds 0)`. Use `Filter.tendsto_def.2 fun U hU => ?_` and prove the remaining obligations.

Take `⟨k, hk⟩` from `frac_nhds hO hF hϖ hU`. Establish `hV` using `frac_open hO hF (pow_ne_zero k hϖ0)`. Use `Filter.mem_of_superset (Filter.prod_mem_prod hV hV) ?_` and prove the remaining obligations. Introduce and unpack `⟨_, _⟩ ⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩⟩`. Rewrite using `[Set.mem_preimage]`.

Conclude with `hk ⟨a * b, Ideal.mul_mem_right b _ ha, map_mul _ _ _⟩`. Conclude with `IsTopologicalRing.of_addGroup_of_nhds_zero hmul key (fun x₀ => Filter.Tendsto.congr (fun x => mul_comm x₀ x) (key x₀))`.
-/
theorem frac_topRing {ℓ : ℕ} (hO : PadicCoeff ℓ O) (hF : FracTop O) : IsTopologicalRing (FractionRing O) := by
  haveI := hO.ring
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  have key : ∀ x₀ : FractionRing O, Filter.Tendsto (fun x => x₀ * x) (nhds 0) (nhds 0) := by
    intro x₀
    obtain ⟨⟨p, q⟩, hpq⟩ := IsLocalization.surj (nonZeroDivisors O) x₀
    have hpq' : x₀ * algebraMap O (FractionRing O) q = algebraMap O (FractionRing O) p := hpq
    have hq0 : (q : O) ≠ 0 := nonZeroDivisors.ne_zero q.2
    refine Filter.tendsto_def.2 fun U hU => ?_
    obtain ⟨k, hk⟩ := frac_nhds hO hF hϖ (by simpa using hU)
    refine Filter.mem_of_superset (frac_open hO hF (mul_ne_zero hq0 (pow_ne_zero k hϖ0))) ?_
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
    rw [Set.mem_preimage]
    refine hk ⟨p * c * ϖ ^ k, Ideal.mem_span_singleton'.2 ⟨p * c, rfl⟩, ?_⟩
    simp only [map_mul]
    rw [← hpq']
    ring
  have hmul : Filter.Tendsto (Function.uncurry ((· * ·) : FractionRing O → FractionRing O → FractionRing O))
      (nhds 0 ×ˢ nhds 0) (nhds 0) := by
    refine Filter.tendsto_def.2 fun U hU => ?_
    obtain ⟨k, hk⟩ := frac_nhds hO hF hϖ hU
    have hV := frac_open hO hF (pow_ne_zero k hϖ0)
    refine Filter.mem_of_superset (Filter.prod_mem_prod hV hV) ?_
    rintro ⟨_, _⟩ ⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩⟩
    rw [Set.mem_preimage]
    exact hk ⟨a * b, Ideal.mul_mem_right b _ ha, map_mul _ _ _⟩
  exact IsTopologicalRing.of_addGroup_of_nhds_zero hmul key
    (fun x₀ => Filter.Tendsto.congr (fun x => mul_comm x₀ x) (key x₀))

/- English proof (translation)
Use `haveI := frac_topRing hO hF`. Use `infer_instance`.
-/
theorem frac_contMul {ℓ : ℕ} (hO : PadicCoeff ℓ O) (hF : FracTop O) : ContinuousMul (FractionRing O) := by
  haveI := frac_topRing hO hF
  infer_instance

/- English proof (translation)
Establish `h : (latT : Submodule O (n → FractionRing O)) = Submodule.map (LinearMap.pi fun a => (Algebra.linearMap O (FractionRing O)).comp (LinearMap.proj a)) ⊤`. Use extensionality with `x`. Rewrite using `[mem_latT, Submodule.map_top, LinearMap.mem_range]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩`.

Conclude with `⟨y, rfl⟩`. Introduce and unpack `⟨y, rfl⟩`. Conclude with `⟨y, rfl⟩`. Rewrite using `[h]`. Conclude with `Module.Finite.fg_top.map _`.
-/
theorem latT_fg : (latT : Submodule O (n → FractionRing O)).FG := by
  have h : (latT : Submodule O (n → FractionRing O)) = Submodule.map
      (LinearMap.pi fun a => (Algebra.linearMap O (FractionRing O)).comp (LinearMap.proj a)) ⊤ := by
    ext x
    rw [mem_latT, Submodule.map_top, LinearMap.mem_range]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, rfl⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, rfl⟩
  rw [h]
  exact Module.Finite.fg_top.map _

/- English proof (translation)
Rewrite using `[eq_top_iff]`. Introduce and unpack `v -`. Establish `hv : v = ∑ a, v a • (fun j => if a = j then (1 : FractionRing O) else 0)`. Use function extensionality and compare the values at `j`. Simplify using `[Finset.sum_apply]`.

Rewrite using `[hv]`. Conclude with `Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span (unit_mem_latT a))`.
-/
theorem latT_span :
    Submodule.span (FractionRing O) ((latT : Submodule O (n → FractionRing O)) : Set (n → FractionRing O)) = ⊤ := by
  rw [eq_top_iff]
  rintro v -
  have hv : v = ∑ a, v a • (fun j => if a = j then (1 : FractionRing O) else 0) := by
    funext j
    simp [Finset.sum_apply]
  rw [hv]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span (unit_mem_latT a))

/- English proof (translation)
Introduce `ψ`. Use `⟨fun a => ψ (fun j => if a = j then 1 else 0), fun x => ?_, fun f hf => ?_⟩` and prove the remaining obligations. Rewrite using `[pairStd_apply, LinearMap.pi_apply_eq_sum_univ ψ x]`. Simplify using `[dotProduct, smul_eq_mul]`. Use function extensionality and compare the values at `a`.

Establish `h` using `hf (fun j => if a = j then 1 else 0)`. Rewrite `h` using `[pairStd_apply]`. Simplify `h` using `[dotProduct]`.
-/
theorem perf_pairStd : PerfectRight (pairStd (O := O) (n := n)) := by
  intro ψ
  refine ⟨fun a => ψ (fun j => if a = j then 1 else 0), fun x => ?_, fun f hf => ?_⟩
  · rw [pairStd_apply, LinearMap.pi_apply_eq_sum_univ ψ x]
    simp [dotProduct, smul_eq_mul]
  · funext a
    have h := hf (fun j => if a = j then 1 else 0)
    rw [pairStd_apply] at h
    simpa [dotProduct] using h

/- English proof (translation)
Establish `h : ((latT : Submodule O (n → FractionRing O)) : Set (n → FractionRing O)) = Set.univ.pi fun _ => Set.range (algebraMap O (FractionRing O))`. Use extensionality with `x`. Simplify using `only [SetLike.mem_coe, mem_latT, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_range]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩ a`.

Conclude with `⟨y a, rfl⟩`. Introduce `h choose y hy using h`. Conclude with `⟨y, funext fun a => (hy a).symm⟩`. Rewrite using `[h]`. Conclude with `isOpen_set_pi Set.finite_univ fun a _ => hF.emb.isOpen_range`.
-/
theorem latT_open (hF : FracTop O) :
    IsOpen ((latT : Submodule O (n → FractionRing O)) : Set (n → FractionRing O)) := by
  have h : ((latT : Submodule O (n → FractionRing O)) : Set (n → FractionRing O)) =
      Set.univ.pi fun _ => Set.range (algebraMap O (FractionRing O)) := by
    ext x
    simp only [SetLike.mem_coe, mem_latT, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_range]
    constructor
    · rintro ⟨y, rfl⟩ a
      exact ⟨y a, rfl⟩
    · intro h
      choose y hy using h
      exact ⟨y, funext fun a => (hy a).symm⟩
  rw [h]
  exact isOpen_set_pi Set.finite_univ fun a _ => hF.emb.isOpen_range

/- English proof (translation)
Assemble the required witnesses or components as `⟨latT_fg, latT_span⟩ perf := perf_pairStd contT := contAction_repV M hM' openT := latT_open hF t2 := by haveI := t2Space_fractionRing_of_padicCoeff ℓ hO hF; infer_instance t2' := by haveI := t2Space_fractionRing_of_padicCoeff ℓ hO hF; infer_instance cs := by haveI := hK; infer_in …`.
-/
theorem realLat_datStd (ℓ : ℕ) (hO : PadicCoeff ℓ O) (hF : FracTop O) (hK : ContinuousMul (FractionRing O))
    (ε : Γ →* Oˣ) (M : Γ →* Matrix n n O) (hε : Continuous fun g => ((ε g : Oˣ) : O))
    (hM : ∀ a b, Continuous fun g => M g⁻¹ b a) (hM' : ∀ a b, Continuous fun g => M g a b) :
    RealLat (datStd hK ε M hε hM) where
  lat := ⟨latT_fg, latT_span⟩
  perf := perf_pairStd
  contT := contAction_repV M hM'
  openT := latT_open hF
  t2 := by haveI := t2Space_fractionRing_of_padicCoeff ℓ hO hF; infer_instance
  t2' := by haveI := t2Space_fractionRing_of_padicCoeff ℓ hO hF; infer_instance
  cs := by haveI := hK; infer_instance
  cs' := by haveI := hK; infer_instance

end RL

section Cont

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]

/- English proof (translation)
Use `haveI := hO.ring`. Establish `hB : ∀ U ∈ nhds (0 : O), ∃ n : ℕ, ((Ideal.span {(ℓ : O) ^ n} : Ideal O) : Set O) ⊆ U`. Introduce `U hU`. Take `⟨k, hk⟩` from `(isAdic_iff.1 hO.adic).2 U hU`. Conclude with `⟨k, fun x hx => hk ((Ideal.span_singleton_le_iff_mem _).2 (Ideal.pow_mem_pow hO.p_mem k) hx)⟩`.

Establish `hA : ∀ n : ℕ, ∃ W : Set (Ω ≃ₐ[Ek] Ω), IsOpen W ∧ (1 : Ω ≃ₐ[Ek] Ω) ∈ W ∧ ∀ h ∈ W, ((ε h : Oˣ) : O) - 1 ∈ Ideal.span {(ℓ : O) ^ n}`. Introduce `n`. Establish `hN : 0 < ℓ ^ n` using `pow_pos hℓ.out.pos n`. Use `haveI : NeZero ((ℓ ^ n : ℕ) : Ω) := ⟨Nat.cast_ne_zero.2 hN.ne'⟩`. Take `⟨ζ, hζ⟩` from `IsAlgClosed.exists_root (Polynomial.cyclotomic (ℓ ^ n) Ω) (Polynomial.degree_cyclotomic_pos _ Ω hN).ne'`.

Establish `hprim : IsPrimitiveRoot ζ (ℓ ^ n)` using `Polynomial.isRoot_cyclotomic_iff.1 hζ`. Establish `hint : IsIntegral Ek ζ` using `IsIntegral.of_pow hN (by rw [hprim.pow_eq_one]; exact isIntegral_one)`. Use `haveI : FiniteDimensional Ek (IntermediateField.adjoin Ek {ζ}) := IntermediateField.adjoin.finiteDimensional hint`. Use `⟨((IntermediateField.adjoin Ek {ζ}).fixingSubgroup : Set (Ω ≃ₐ[Ek] Ω)), IntermediateField.fixingSubgroup_isOpen _, (IntermediateField.adjoin Ek {ζ}).fixingSubgroup.one_mem, fun h hh => ?_⟩` and prove the remaining obligations. Establish `hfix : h ζ = ζ` using `by first`.

Consider the case `exact ((IntermediateField.mem_fixingSubgroup_iff _ _).1 hh) ζ (IntermediateField.mem_adjoin_simple_self Ek ζ)`. Consider the case `exact (IntermediateField.mem_fixingSubgroup_iff _).1 hh ζ (IntermediateField.mem_adjoin_simple_self Ek ζ)`. Consider the case `exact hh ⟨ζ, IntermediateField.mem_adjoin_simple_self Ek ζ⟩`. Take `⟨a, ha1, ha2⟩` from `hc h n ζ hprim.pow_eq_one`. Rewrite `ha1` using `[hfix]`.

Establish `hz : ζ ≠ 0` using `hprim.ne_zero hN.ne'`. Establish `hdvd : ((ℓ ^ n : ℕ) : ℤ) ∣ (a : ℤ) - 1`. Rewrite using `[← hprim.zpow_eq_one_iff_dvd, zpow_sub₀ hz, zpow_natCast, zpow_one, ← ha1, div_self hz]`. Take `⟨m, hm⟩` from `hdvd`. Establish `hm'` using `congrArg (Int.cast : ℤ → O) hm`.

Move the coercions through the operations in `at hm'`. Establish `he : ((ε h : Oˣ) : O) - 1 = (((ε h : Oˣ) : O) - a) + (ℓ : O) ^ n * (m : O)`. Take the linear combination `hm'`. Rewrite using `[he]`. Conclude with `Ideal.add_mem _ ha2 (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))`.

Rewrite using `[continuous_iff_continuousAt]`. Introduce `g₀`. Use `Filter.tendsto_def.2 fun V hV => ?_` and prove the remaining obligations. Establish `hV' : (fun x => ((ε g₀ : Oˣ) : O) + x) ⁻¹' V ∈ nhds (0 : O)` using `(continuous_const.add continuous_id).continuousAt.preimage_mem_nhds (by simpa using hV)`. Take `⟨n, hn⟩` from `hB _ hV'`.

Take `⟨W, hWo, hW1, hW⟩` from `hA n`. Establish `hWn : (fun g => g₀⁻¹ * g) ⁻¹' W ∈ nhds g₀` using `(continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds (by simpa using hWo.mem_nhds hW1)`. Use `Filter.mem_of_superset hWn fun g hg => ?_` and prove the remaining obligations. Establish `h1` using `hW _ hg`. Establish `hg' : g = g₀ * (g₀⁻¹ * g)` using `by group`.

Establish `he : ((ε g : Oˣ) : O) = ((ε g₀ : Oˣ) : O) + ((ε g₀ : Oˣ) : O) * (((ε (g₀⁻¹ * g) : Oˣ) : O) - 1)` using `by conv_lhs => rw [hg']`. Rewrite using `[map_mul, Units.val_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Set.mem_preimage, he]`. Conclude with `hn (Ideal.mul_mem_left _ _ h1)`.
-/
theorem eps_cont (ℓ : ℕ) [hℓ : Fact ℓ.Prime] (hO : PadicCoeff ℓ O) {Ek Ω : Type} [Field Ek] [Field Ω] [Algebra Ek Ω]
    [CharZero Ω] [IsAlgClosed Ω] (ε : (Ω ≃ₐ[Ek] Ω) →* Oˣ) (hc : IsCycG ℓ ε) :
    Continuous fun g => ((ε g : Oˣ) : O) := by
  haveI := hO.ring
  have hB : ∀ U ∈ nhds (0 : O), ∃ n : ℕ, ((Ideal.span {(ℓ : O) ^ n} : Ideal O) : Set O) ⊆ U := by
    intro U hU
    obtain ⟨k, hk⟩ := (isAdic_iff.1 hO.adic).2 U hU
    exact ⟨k, fun x hx => hk ((Ideal.span_singleton_le_iff_mem _).2 (Ideal.pow_mem_pow hO.p_mem k) hx)⟩
  have hA : ∀ n : ℕ, ∃ W : Set (Ω ≃ₐ[Ek] Ω), IsOpen W ∧ (1 : Ω ≃ₐ[Ek] Ω) ∈ W ∧
      ∀ h ∈ W, ((ε h : Oˣ) : O) - 1 ∈ Ideal.span {(ℓ : O) ^ n} := by
    intro n
    have hN : 0 < ℓ ^ n := pow_pos hℓ.out.pos n
    haveI : NeZero ((ℓ ^ n : ℕ) : Ω) := ⟨Nat.cast_ne_zero.2 hN.ne'⟩
    obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic (ℓ ^ n) Ω)
      (Polynomial.degree_cyclotomic_pos _ Ω hN).ne'
    have hprim : IsPrimitiveRoot ζ (ℓ ^ n) := Polynomial.isRoot_cyclotomic_iff.1 hζ
    have hint : IsIntegral Ek ζ := IsIntegral.of_pow hN (by rw [hprim.pow_eq_one]; exact isIntegral_one)
    haveI : FiniteDimensional Ek (IntermediateField.adjoin Ek {ζ}) :=
      IntermediateField.adjoin.finiteDimensional hint
    refine ⟨((IntermediateField.adjoin Ek {ζ}).fixingSubgroup : Set (Ω ≃ₐ[Ek] Ω)),
      IntermediateField.fixingSubgroup_isOpen _, (IntermediateField.adjoin Ek {ζ}).fixingSubgroup.one_mem,
      fun h hh => ?_⟩
    have hfix : h ζ = ζ := by
      first
        | exact ((IntermediateField.mem_fixingSubgroup_iff _ _).1 hh) ζ (IntermediateField.mem_adjoin_simple_self Ek ζ)
        | exact (IntermediateField.mem_fixingSubgroup_iff _).1 hh ζ (IntermediateField.mem_adjoin_simple_self Ek ζ)
        | exact hh ⟨ζ, IntermediateField.mem_adjoin_simple_self Ek ζ⟩
    obtain ⟨a, ha1, ha2⟩ := hc h n ζ hprim.pow_eq_one
    rw [hfix] at ha1
    have hz : ζ ≠ 0 := hprim.ne_zero hN.ne'
    have hdvd : ((ℓ ^ n : ℕ) : ℤ) ∣ (a : ℤ) - 1 := by
      rw [← hprim.zpow_eq_one_iff_dvd, zpow_sub₀ hz, zpow_natCast, zpow_one, ← ha1, div_self hz]
    obtain ⟨m, hm⟩ := hdvd
    have hm' := congrArg (Int.cast : ℤ → O) hm
    push_cast at hm'
    have he : ((ε h : Oˣ) : O) - 1 = (((ε h : Oˣ) : O) - a) + (ℓ : O) ^ n * (m : O) := by
      linear_combination hm'
    rw [he]
    exact Ideal.add_mem _ ha2 (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
  rw [continuous_iff_continuousAt]
  intro g₀
  refine Filter.tendsto_def.2 fun V hV => ?_
  have hV' : (fun x => ((ε g₀ : Oˣ) : O) + x) ⁻¹' V ∈ nhds (0 : O) :=
    (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds (by simpa using hV)
  obtain ⟨n, hn⟩ := hB _ hV'
  obtain ⟨W, hWo, hW1, hW⟩ := hA n
  have hWn : (fun g => g₀⁻¹ * g) ⁻¹' W ∈ nhds g₀ :=
    (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds (by simpa using hWo.mem_nhds hW1)
  refine Filter.mem_of_superset hWn fun g hg => ?_
  have h1 := hW _ hg
  have hg' : g = g₀ * (g₀⁻¹ * g) := by group
  have he : ((ε g : Oˣ) : O) = ((ε g₀ : Oˣ) : O) + ((ε g₀ : Oˣ) : O) * (((ε (g₀⁻¹ * g) : Oˣ) : O) - 1) := by
    conv_lhs => rw [hg']
    rw [map_mul, Units.val_mul]
    ring
  rw [Set.mem_preimage, he]
  exact hn (Ideal.mul_mem_left _ _ h1)

end Cont

section H1K

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {Γ : Type} [Group Γ] [TopologicalSpace Γ] {V : Type} [AddCommGroup V] [Module O V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [TopologicalSpace O] [ContinuousSMul O V] [Module (FractionRing O) V] [IsScalarTower O (FractionRing O) V]
  (ρ : Representation O Γ V) (hcs : ContinuousConstSMul (FractionRing O) V)
  (hρ : ∀ g (c : FractionRing O) v, ρ g (c • v) = c • ρ g v)

def cocyclesFractionSubspace : Submodule (FractionRing O) (Γ → V) where
  carrier := {f | f ∈ Z1 ρ}
  zero_mem' := (Z1 ρ).zero_mem
  add_mem' ha hb := (Z1 ρ).add_mem ha hb
  smul_mem' c f hf := by
    have := hcs
    refine ⟨hf.1.const_smul c, fun g h => ?_⟩
    simp only [Pi.smul_apply, hf.2 g h, smul_add, hρ]

def zsm (c : FractionRing O) : Z1 ρ →ₗ[O] Z1 ρ where
  toFun z := ⟨c • (z : Γ → V), (cocyclesFractionSubspace ρ hcs hρ).smul_mem c z.2⟩
  map_add' z z' := Subtype.ext (smul_add c _ _)
  map_smul' o z := Subtype.ext (by
    funext g
    show c • (o • (z : Γ → V) g) = o • (c • (z : Γ → V) g)
    rw [← algebraMap_smul (FractionRing O) o ((z : Γ → V) g),
      ← algebraMap_smul (FractionRing O) o (c • (z : Γ → V) g), smul_smul, smul_smul, mul_comm])

/- English proof (translation)
Introduce `z hz`. Simplify using `only [Submodule.mem_comap, Submodule.coe_subtype] at hz ⊢`. Take `⟨v, hv⟩` from `hz`. Use `⟨c • v, ?_⟩` and prove the remaining obligations. Rewrite using `[show ((zsm ρ hcs hρ c z : Z1 ρ) : Γ → V) = c • (z : Γ → V) from rfl, ← hv]`.

Use function extensionality and compare the values at `g`. Simplify using `[d0, hρ, smul_sub]`.
-/
theorem zsm_B (c : FractionRing O) :
    (B1 ρ).comap (Z1 ρ).subtype ≤ ((B1 ρ).comap (Z1 ρ).subtype).comap (zsm ρ hcs hρ c) := by
  intro z hz
  simp only [Submodule.mem_comap, Submodule.coe_subtype] at hz ⊢
  obtain ⟨v, hv⟩ := hz
  refine ⟨c • v, ?_⟩
  rw [show ((zsm ρ hcs hρ c z : Z1 ρ) : Γ → V) = c • (z : Γ → V) from rfl, ← hv]
  funext g
  simp [d0, hρ, smul_sub]

def smulH1FractionField : SMul (FractionRing O) (H1 ρ) :=
  ⟨fun c => Submodule.mapQ _ _ (zsm ρ hcs hρ c) (zsm_B ρ hcs hρ c)⟩

def cocyclesToH1 : cocyclesFractionSubspace ρ hcs hρ →+ H1 ρ where
  toFun z := Submodule.Quotient.mk ⟨z.1, z.2⟩
  map_zero' := rfl
  map_add' _ _ := rfl

def moduleH1FractionField : Module (FractionRing O) (H1 ρ) :=
  letI := smulH1FractionField ρ hcs hρ
  Function.Surjective.module (FractionRing O) (cocyclesToH1 ρ hcs hρ)
    (by
      intro x
      induction x using Submodule.Quotient.induction_on with
      | H z => exact ⟨⟨z.1, z.2⟩, rfl⟩)
    (fun _ _ => rfl)

/- English proof (translation)
Use `letI := moduleH1FractionField ρ hcs hρ`. Use `⟨fun o c x => ?_⟩` and prove the remaining obligations. Proceed by induction on `x using Submodule.Quotient.induction_on with`. Consider the case `H z`. Express the relevant statement in the definitionally equal form `Submodule.mapQ _ _ (zsm ρ hcs hρ (o • c)) (zsm_B ρ hcs hρ (o • c)) (Submodule.Quotient.mk z) = o • Submodule.mapQ _ _ (zsm ρ hcs hρ c) (zsm_B ρ hcs hρ c) (Submodule.Quotient.mk z)`.

Rewrite using `[Submodule.mapQ_apply, Submodule.mapQ_apply, ← Submodule.Quotient.mk_smul]`. Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `g`. Conclude with `smul_assoc o c ((z : Γ → V) g)`.
-/
theorem isScalarTower_H1 :
    @IsScalarTower O (FractionRing O) (H1 ρ) _ (moduleH1FractionField ρ hcs hρ).toSMul _ := by
  letI := moduleH1FractionField ρ hcs hρ
  refine ⟨fun o c x => ?_⟩
  induction x using Submodule.Quotient.induction_on with
  | H z =>
    change Submodule.mapQ _ _ (zsm ρ hcs hρ (o • c)) (zsm_B ρ hcs hρ (o • c)) (Submodule.Quotient.mk z) =
      o • Submodule.mapQ _ _ (zsm ρ hcs hρ c) (zsm_B ρ hcs hρ c) (Submodule.Quotient.mk z)
    rw [Submodule.mapQ_apply, Submodule.mapQ_apply, ← Submodule.Quotient.mk_smul]
    congr 1
    apply Subtype.ext
    funext g
    exact smul_assoc o c ((z : Γ → V) g)

end H1K

section Spec

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
  [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
  {X' d : Type} [Fintype d] [DecidableEq d] {R' : Subalgebra O (X' → Matrix d d (FractionRing O))}
  {Tc : Type} [CommRing Tc] [Algebra Tc R']
  {Ek Ω : Type} [Field Ek] [Field Ω] [Algebra Ek Ω]
  (r : (Ω ≃ₐ[Ek] Ω) →* R') (χ : (Ω ≃ₐ[Ek] Ω) →* Tcˣ) {t : ℕ} (bl : d → Fin (t + 1))
  (ρk : ∀ k : Fin (t + 1), R' →ₐ[O] Matrix {a // bl a = k} {a // bl a = k} O)
  (ε : (Ω ≃ₐ[Ek] Ω) →* Oˣ) (Aw : ℕ → ValuationSubring Ω)

def uHom : (Ω ≃ₐ[Ek] Ω) →* R' where
  toFun := uElt r χ
  map_one' := uElt_one r χ
  map_mul' := uElt_mul r χ

def M0 : (Ω ≃ₐ[Ek] Ω) →* Matrix {a // bl a = 0} {a // bl a = 0} O :=
  (ρk 0).toRingHom.toMonoidHom.comp (uHom r χ)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem block_zero_apply (g : Ω ≃ₐ[Ek] Ω) : M0 r χ bl ρk g = ρk 0 (uElt r χ g) := rfl

def Mw (w : ℕ) : decs Ek Aw w →* Matrix {a // bl a = 0} {a // bl a = 0} O :=
  (M0 r χ bl ρk).comp (decs Ek Aw w).subtype

def epsW (w : ℕ) : decs Ek Aw w →* Oˣ := ε.comp (decs Ek Aw w).subtype

def rho2 : Representation O (Ω ≃ₐ[Ek] Ω) ({a // bl a = 0} → O) := repL' ε (M0 r χ bl ρk)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem rho2_apply (g : Ω ≃ₐ[Ek] Ω) (y : {a // bl a = 0} → O) :
    rho2 r χ bl ρk ε g y = ((ε g : Oˣ) : O) • ((ρk 0 (uElt r χ g⁻¹))ᵀ *ᵥ y) := rfl

abbrev VT (_w : ℕ) : Type := {a // bl a = 0} → FractionRing O

def Dat (hK : ContinuousMul (FractionRing O)) (hε : Continuous fun g => ((ε g : Oˣ) : O))
    (hM : ∀ a b, Continuous fun g => M0 r χ bl ρk g a b) (w : ℕ) :
    LatData O (decs Ek Aw w) (VT (O := O) bl w) (VT (O := O) bl w) :=
  datStd (Γ := decs Ek Aw w) hK (epsW ε Aw w) (Mw r χ bl ρk Aw w)
    (hε.comp continuous_subtype_val)
    (fun a b => (hM b a).comp (continuous_subtype_val.comp continuous_inv))

def blkEquiv : blockRestrictedRepresentationType bl ρk 0 ≃ₗ[O] ({a // bl a = 0} → KO O) where
  toFun m := m
  invFun m := m
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

variable (hK : ContinuousMul (FractionRing O)) (hε : Continuous fun g => ((ε g : Oˣ) : O))
    (hM : ∀ a b, Continuous fun g => M0 r χ bl ρk g a b)

def uD (w : ℕ) : blockRestrictedRepresentationType bl ρk 0 ≃ₗ[O] (VT (O := O) bl w ⧸ (Dat r χ bl ρk ε Aw hK hε hM w).T) :=
  (blkEquiv bl ρk).trans uStd

def vD (w : ℕ) : ({a // bl a = 0} → O) ≃ₗ[O] (Dat r χ bl ρk ε Aw hK hε hM w).T' := vStd

def gam : ({a // bl a = 0} → O) →ₗ[O] blockRestrictedRepresentationType bl ρk 0 →ₗ[O] KO O :=
  gamStd.compl₂ (blkEquiv bl ρk).toLinearMap

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem gam_apply (y : {a // bl a = 0} → O) (m : blockRestrictedRepresentationType bl ρk 0) :
    gam bl ρk y m = ∑ a, y a • blkEquiv bl ρk m a := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem dat_eps (w : ℕ) (g : decs Ek Aw w) : (Dat r χ bl ρk ε Aw hK hε hM w).ε g = ε g := rfl

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `a`. Express the relevant statement in the definitionally equal form `algebraMap O (FractionRing O) (rho2 r χ bl ρk ε (g : Ω ≃ₐ[Ek] Ω) y a) = (repV' (epsW ε Aw w) (Mw r χ bl ρk Aw w) g (fun b => algebraMap O (FractionRing O) (y b))) a`. Rewrite using `[repV'_apply, matK_mulVec_alg, rho2_apply]`. Simplify using `only [Pi.smul_apply, smul_eq_mul, Algebra.smul_def, map_mul]`.

Apply the tactic sequence `try rfl`.
-/
theorem vD_equiv (w : ℕ) (g : decs Ek Aw w) (y : {a // bl a = 0} → O) :
    vD r χ bl ρk ε Aw hK hε hM w (rho2 r χ bl ρk ε g y) =
      (Dat r χ bl ρk ε Aw hK hε hM w).ρTl' g (vD r χ bl ρk ε Aw hK hε hM w y) := by
  apply Subtype.ext
  funext a
  change algebraMap O (FractionRing O) (rho2 r χ bl ρk ε (g : Ω ≃ₐ[Ek] Ω) y a) =
    (repV' (epsW ε Aw w) (Mw r χ bl ρk Aw w) g (fun b => algebraMap O (FractionRing O) (y b))) a
  rw [repV'_apply, matK_mulVec_alg, rho2_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Algebra.smul_def, map_mul]
  try rfl

/- English proof (translation)
Conclude with `gamStd_eq y (blkEquiv bl ρk m)`.
-/
theorem gam_eq (w : ℕ) (y : {a // bl a = 0} → O) (m : blockRestrictedRepresentationType bl ρk 0) :
    gam bl ρk y m = pairKO (Dat r χ bl ρk ε Aw hK hε hM w).bT (Dat r χ bl ρk ε Aw hK hε hM w).T
      (uD r χ bl ρk ε Aw hK hε hM w m) (vD r χ bl ρk ε Aw hK hε hM w y) := by
  exact gamStd_eq y (blkEquiv bl ρk m)

/- English proof (translation)
Substitute `hx` using the available equality. Simplify using `[matK_mulVec]`. Both sides reduce to the same expression.
-/
private theorem smul_apply_eq_toKO_matK_mulVec {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {X' d : Type} [Fintype d] [DecidableEq d] {R' : Subalgebra O (X' → Matrix d d (FractionRing O))}
    {t : ℕ} (bl : d → Fin (t + 1)) (ρk : ∀ k : Fin (t + 1), R' →ₐ[O] Matrix {a // bl a = k} {a // bl a = k} O)
    (u : R') (m : blockRestrictedRepresentationType bl ρk 0) (a : {a // bl a = 0}) (x : {a // bl a = 0} → FractionRing O)
    (hx : (fun a => toKO O (x a)) = m) :
    (u • m) a = toKO O ((matK (ρk 0 u) *ᵥ x) a) := by
  subst hx
  simp [matK_mulVec]
  rfl

/- English proof (translation)
Use `choose x hx using fun a => Submodule.Quotient.mk_surjective _ (m a)`. Establish `hxm : (fun a => toKO O (x a)) = m` using `funext hx`. Establish `hL : (fun a => toKO O ((matK (ρk 0 (uElt r χ (g : Ω ≃ₐ[Ek] Ω))) *ᵥ x) a)) = resRep (uRep O (M` using `blockRestrictedRepresentationType bl ρk 0) r χ) (decs Ek Aw w) g m := by`. Use function extensionality and compare the values at `a`. Conclude with `(smul_apply_eq_toKO_matK_mulVec bl ρk _ m a x hxm).symm`.

Establish `e1 : uD r χ bl ρk ε Aw hK hε hM w (fun a => toKO O (x a)) = Submodule.Quotient.mk x` using `uStd_mk x`. Rewrite using `[← hL, ← hxm, e1]`. Conclude with `uStd_mk (matK (ρk 0 (uElt r χ (g : Ω ≃ₐ[Ek] Ω))) *ᵥ x)`.
-/
theorem huD [∀ k, SMulCommClass R' O (blockRestrictedRepresentationType bl ρk k)] (w : ℕ) (g : decs Ek Aw w) (m : blockRestrictedRepresentationType bl ρk 0) :
    uD r χ bl ρk ε Aw hK hε hM w (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk 0) r χ) (decs Ek Aw w) g m) =
      (Dat r χ bl ρk ε Aw hK hε hM w).ρA g (uD r χ bl ρk ε Aw hK hε hM w m) := by
  choose x hx using fun a => Submodule.Quotient.mk_surjective _ (m a)
  have hxm : (fun a => toKO O (x a)) = m := funext hx
  have hL : (fun a => toKO O ((matK (ρk 0 (uElt r χ (g : Ω ≃ₐ[Ek] Ω))) *ᵥ x) a)) =
      resRep (uRep O (M := blockRestrictedRepresentationType bl ρk 0) r χ) (decs Ek Aw w) g m := by
    funext a
    exact (smul_apply_eq_toKO_matK_mulVec bl ρk _ m a x hxm).symm
  have e1 : uD r χ bl ρk ε Aw hK hε hM w (fun a => toKO O (x a)) = Submodule.Quotient.mk x := uStd_mk x
  rw [← hL, ← hxm, e1]
  exact uStd_mk (matK (ρk 0 (uElt r χ (g : Ω ≃ₐ[Ek] Ω))) *ᵥ x)

end Spec

section Cont2

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
variable [TopologicalSpace (FractionRing O)] [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
  {X' d : Type} [Fintype d] [DecidableEq d] {R' : Subalgebra O (X' → Matrix d d (FractionRing O))}
  [TopologicalSpace R'] [IsTopologicalAddGroup R']
  {Tc : Type} [CommRing Tc] [Algebra Tc R']
  {Ek Ω : Type} [Field Ek] [Field Ω] [Algebra Ek Ω]
  (r : (Ω ≃ₐ[Ek] Ω) →* R') (χ : (Ω ≃ₐ[Ek] Ω) →* Tcˣ) {t : ℕ} (bl : d → Fin (t + 1))
  (ρk : ∀ k : Fin (t + 1), R' →ₐ[O] Matrix {a // bl a = k} {a // bl a = k} O)

/- English proof (translation)
Use `haveI := hO.ring`. Set `f : R' →ₗ[O] O` to `{ toFun := fun x => ρk 0 x a b map_add' := fun x y => by simp map_smul' := fun c x => by simp }`. Establish `hf : Continuous f` using `fgTop_continuous_linearMap hR hO f`. Conclude with `hf.comp hu`.
-/
theorem block_zero_continuous {ℓ : ℕ} (hO : PadicCoeff ℓ O) (hR : IsFGTop O R') (hu : Continuous fun g => uElt r χ g)
    (a b : {a // bl a = 0}) : Continuous fun g => M0 r χ bl ρk g a b := by
  haveI := hO.ring
  let f : R' →ₗ[O] O :=
    { toFun := fun x => ρk 0 x a b
      map_add' := fun x y => by simp
      map_smul' := fun c x => by simp }
  have hf : Continuous f := fgTop_continuous_linearMap hR hO f
  exact hf.comp hu

end Cont2

section Clauses

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
  [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
  {X' d : Type} [Fintype d] [DecidableEq d] {R' : Subalgebra O (X' → Matrix d d (FractionRing O))}
  {Tc : Type} [CommRing Tc] [Algebra Tc R']
  {Ek Ω : Type} [Field Ek] [Field Ω] [Algebra Ek Ω]
  (r : (Ω ≃ₐ[Ek] Ω) →* R') (χ : (Ω ≃ₐ[Ek] Ω) →* Tcˣ) {t : ℕ} (bl : d → Fin (t + 1))
  (ρk : ∀ k : Fin (t + 1), R' →ₐ[O] Matrix {a // bl a = k} {a // bl a = k} O)
  (ε : (Ω ≃ₐ[Ek] Ω) →* Oˣ) (Aw : ℕ → ValuationSubring Ω)
  (hK : ContinuousMul (FractionRing O)) (hε : Continuous fun g => ((ε g : Oˣ) : O))
  (hM : ∀ a b, Continuous fun g => M0 r χ bl ρk g a b)

/- English proof (translation)
Conclude with `realLat_datStd ℓ hO hF hK (epsW ε Aw w) (Mw r χ bl ρk Aw w) _ _ (fun a b => (hM a b).comp continuous_subtype_val)`.
-/
theorem realLat_Dat (ℓ : ℕ) (hO : PadicCoeff ℓ O) (hF : FracTop O) (w : ℕ) :
    RealLat (Dat r χ bl ρk ε Aw hK hε hM w) := by
  exact realLat_datStd ℓ hO hF hK (epsW ε Aw w) (Mw r χ bl ρk Aw w) _ _
    (fun a b => (hM a b).comp continuous_subtype_val)

/- English proof (translation)
Conclude with `⟨fun g => rfl, realLat_Dat r χ bl ρk ε Aw hK hε hM ℓ hO hF w, fun g y => vD_equiv r χ bl ρk ε Aw hK hε hM w g y, fun y m => gam_eq r χ bl ρk ε Aw hK hε hM w y m⟩`.
-/
theorem rowLat (ℓ : ℕ) (hO : PadicCoeff ℓ O) (hF : FracTop O) (w : ℕ) :
    (∀ g : decs Ek Aw w, (Dat r χ bl ρk ε Aw hK hε hM w).ε g = ε g) ∧
    RealLat (Dat r χ bl ρk ε Aw hK hε hM w) ∧
    (∀ (g : decs Ek Aw w) (y : {a // bl a = 0} → O),
      vD r χ bl ρk ε Aw hK hε hM w (rho2 r χ bl ρk ε g y) =
        (Dat r χ bl ρk ε Aw hK hε hM w).ρTl' g (vD r χ bl ρk ε Aw hK hε hM w y)) ∧
    (∀ (y : {a // bl a = 0} → O) (m : blockRestrictedRepresentationType bl ρk 0),
      gam bl ρk y m = pairKO (Dat r χ bl ρk ε Aw hK hε hM w).bT (Dat r χ bl ρk ε Aw hK hε hM w).T
        (uD r χ bl ρk ε Aw hK hε hM w m) (vD r χ bl ρk ε Aw hK hε hM w y)) := by
  exact ⟨fun g => rfl, realLat_Dat r χ bl ρk ε Aw hK hε hM ℓ hO hF w,
    fun g y => vD_equiv r χ bl ρk ε Aw hK hε hM w g y, fun y m => gam_eq r χ bl ρk ε Aw hK hε hM w y m⟩

/- English proof (translation)
Use `continuous_induced_rng.2 ?_` and prove the remaining obligations. Conclude with `continuous_pi fun a => hF.emb.continuous.comp ((continuous_apply a).comp hπ)`.
-/
theorem hpD {T₁ : Type} [AddCommGroup T₁] [Module O T₁] [TopologicalSpace T₁]
    (π : T₁ →ₗ[O] ({a // bl a = 0} → O)) (hπ : Continuous π) (hF : FracTop O) (w : ℕ) :
    Continuous fun x => vD r χ bl ρk ε Aw hK hε hM w (π x) := by
  refine continuous_induced_rng.2 ?_
  exact continuous_pi fun a => hF.emb.continuous.comp ((continuous_apply a).comp hπ)

/- English proof (translation)
Establish `h : π (resRep ρ₁ (decs Ek Aw w) g x) = rho2 r χ bl ρk ε g (π x)` using `hπe g x`. Rewrite using `[h]`. Conclude with `vD_equiv r χ bl ρk ε Aw hK hε hM w g (π x)`.
-/
theorem heD {T₁ : Type} [AddCommGroup T₁] [Module O T₁] (ρ₁ : Representation O (Ω ≃ₐ[Ek] Ω) T₁)
    (π : T₁ →ₗ[O] ({a // bl a = 0} → O)) (hπe : ∀ g x, π (ρ₁ g x) = rho2 r χ bl ρk ε g (π x))
    (w : ℕ) (g : decs Ek Aw w) (x : T₁) :
    vD r χ bl ρk ε Aw hK hε hM w (π (resRep ρ₁ (decs Ek Aw w) g x)) =
      (Dat r χ bl ρk ε Aw hK hε hM w).ρTl' g (vD r χ bl ρk ε Aw hK hε hM w (π x)) := by
  have h : π (resRep ρ₁ (decs Ek Aw w) g x) = rho2 r χ bl ρk ε g (π x) := hπe g x
  rw [h]
  exact vD_equiv r χ bl ρk ε Aw hK hε hM w g (π x)

/- English proof (translation)
Use `haveI := h`. Use `infer_instance`.
-/
theorem csK (h : ContinuousMul (FractionRing O)) :
    ContinuousConstSMul (FractionRing O) ({a // bl a = 0} → FractionRing O) := by
  haveI := h
  infer_instance

def modT (w : ℕ) : Module (FractionRing O) (H1 (Dat r χ bl ρk ε Aw hK hε hM w).ρT) :=
  moduleH1FractionField _ (csK bl hK) (fun g c v => Matrix.mulVec_smul _ c v)

/- English proof (translation)
Conclude with `isScalarTower_H1 _ _ _`.
-/
theorem towerT (w : ℕ) :
    @IsScalarTower O (FractionRing O) (H1 (Dat r χ bl ρk ε Aw hK hε hM w).ρT) _
      (modT r χ bl ρk ε Aw hK hε hM w).toSMul _ := by
  exact isScalarTower_H1 _ _ _

/- English proof (translation)
Rewrite using `[repV'_apply, repV'_apply, Matrix.mulVec_smul, smul_comm]`.
-/
theorem repV'_smul {Γ : Type} [Group Γ] {n : Type} [Fintype n] [DecidableEq n] (ε' : Γ →* Oˣ)
    (M : Γ →* Matrix n n O) (g : Γ) (c : FractionRing O) (v : n → FractionRing O) :
    repV' ε' M g (c • v) = c • repV' ε' M g v := by
  rw [repV'_apply, repV'_apply, Matrix.mulVec_smul, smul_comm]

def modT' (w : ℕ) : Module (FractionRing O) (H1 (Dat r χ bl ρk ε Aw hK hε hM w).ρT') :=
  moduleH1FractionField _ (csK bl hK) (repV'_smul _ _)

/- English proof (translation)
Conclude with `isScalarTower_H1 _ _ _`.
-/
theorem towerT' (w : ℕ) :
    @IsScalarTower O (FractionRing O) (H1 (Dat r χ bl ρk ε Aw hK hε hM w).ρT') _
      (modT' r χ bl ρk ε Aw hK hε hM w).toSMul _ := by
  exact isScalarTower_H1 _ _ _

end Clauses

section Inputs

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
  {Ek Ω : Type} [Field Ek] [NumberField Ek] [Field Ω] [Algebra Ek Ω] [IsAlgClosure Ek Ω]

/- English proof (translation)
Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed Ek`. Use `haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap Ek Ω).injective`. Conclude with `eps_cont ℓ hO ε hc`.
-/
theorem eps_cont_nf (ℓ : ℕ) [Fact ℓ.Prime] (hO : PadicCoeff ℓ O) (ε : (Ω ≃ₐ[Ek] Ω) →* Oˣ) (hc : IsCycG ℓ ε) :
    Continuous fun g => ((ε g : Oˣ) : O) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed Ek
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap Ek Ω).injective
  exact eps_cont ℓ hO ε hc

end Inputs

end Formalism.MainNotions.N.KLat
