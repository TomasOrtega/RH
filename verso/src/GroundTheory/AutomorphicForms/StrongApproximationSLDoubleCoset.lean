import Mathlib
import GroundTheory.AutomorphicForms.StrongApproximationSLDense
import GroundTheory.GlobalFields.ClassFieldConsequences.RayClass
import GroundTheory.GlobalFields.IdeleGroups.ClassGroup

open NumberField IsDedekindDomain Topology Filter Set Matrix
open scoped RestrictedProduct

namespace GroundTheory.Automorphic

noncomputable section

namespace AdelicGLn

variable (K : Type*) [Field K] [NumberField K] (n : ℕ)

def rationalFiniteGL : Subgroup (FiniteAdelicGL K n) :=
  (finiteDiagonal K n).range

def detClassSubgroup (U : Subgroup (FiniteAdelicGL K n)) :
    Subgroup (FiniteAdeleRing (𝓞 K) K)ˣ :=
  (FiniteAdeleRing.unitEmbedding (𝓞 K) K).range ⊔
    U.map (Matrix.GeneralLinearGroup.det : FiniteAdelicGL K n →* (FiniteAdeleRing (𝓞 K) K)ˣ)

abbrev DetClassGroup (U : Subgroup (FiniteAdelicGL K n)) : Type _ :=
  (FiniteAdeleRing (𝓞 K) K)ˣ ⧸ detClassSubgroup K n U

abbrev DoubleCosetSpace (U : Subgroup (FiniteAdelicGL K n)) : Type _ :=
  DoubleCoset.Quotient (rationalFiniteGL K n : Set (FiniteAdelicGL K n))
    (U : Set (FiniteAdelicGL K n))

variable {K n}

def detDoubleCoset (U : Subgroup (FiniteAdelicGL K n)) :
    DoubleCosetSpace K n U → DetClassGroup K n U :=
  Quotient.lift (fun g => (QuotientGroup.mk (Matrix.GeneralLinearGroup.det g) : DetClassGroup K n U))
    (by
      intro a b hab
      obtain ⟨_, ⟨γ, rfl⟩, u, hu, rfl⟩ := DoubleCoset.rel_iff.1 hab
      refine (QuotientGroup.eq.2 ?_)
      have : (Matrix.GeneralLinearGroup.det a)⁻¹ *
          Matrix.GeneralLinearGroup.det (finiteDiagonal K n γ * a * u) =
          FiniteAdeleRing.unitEmbedding (𝓞 K) K (Matrix.GeneralLinearGroup.det γ) *
            Matrix.GeneralLinearGroup.det u := by
        rw [map_mul, map_mul, det_finiteDiagonal, mul_comm _ (Matrix.GeneralLinearGroup.det a),
          mul_assoc, inv_mul_cancel_left]
      rw [this]
      exact mul_mem (Subgroup.mem_sup_left ⟨_, rfl⟩) (Subgroup.mem_sup_right ⟨u, hu, rfl⟩))

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem detDoubleCoset_mk (U : Subgroup (FiniteAdelicGL K n)) (g : FiniteAdelicGL K n) :
    detDoubleCoset U (DoubleCoset.mk _ _ g) = QuotientGroup.mk (Matrix.GeneralLinearGroup.det g) :=
  rfl

/- English proof (translation)
Use `Units.ext ?_` and prove the remaining obligations. Rewrite using `[Matrix.GeneralLinearGroup.val_det_apply, coe_diagonalGL, det_diagonal, Units.coe_prod]`.
-/
theorem det_diagonalGL {R : Type*} [CommRing R] (d : Fin n → Rˣ) :
    Matrix.GeneralLinearGroup.det (diagonalGL d) = ∏ k, d k := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, coe_diagonalGL, det_diagonal, Units.coe_prod]

/- English proof (translation)
Rewrite using `[det_diagonalGL, Finset.prod_pi_mulSingle', if_pos (Finset.mem_univ _)]`.
-/
theorem det_diagonalGL_mulSingle {R : Type*} [CommRing R] (hn : 0 < n) (a : Rˣ) :
    Matrix.GeneralLinearGroup.det (diagonalGL (Pi.mulSingle (⟨0, hn⟩ : Fin n) a)) = a := by
  rw [det_diagonalGL, Finset.prod_pi_mulSingle', if_pos (Finset.mem_univ _)]

/- English proof (translation)
Take `⟨_, ⟨κ, rfl⟩, _, ⟨u₀, hu₀, rfl⟩, hκ⟩` from `Subgroup.mem_sup.1 h`. Use `set δ : GL (Fin n) K := diagonalGL (Pi.mulSingle (⟨0, hn⟩ : Fin n) κ)`. Use `set g₁ : FiniteAdelicGL K n := finiteDiagonal K n δ * g * u₀`. Establish `hg₁ : Matrix.GeneralLinearGroup.det g₁ = Matrix.GeneralLinearGroup.det g'`. Simplify using `only [g₁, map_mul, det_finiteDiagonal, δ, det_diagonalGL_mulSingle hn]`.

Rewrite using `[mul_comm _ (Matrix.GeneralLinearGroup.det g), mul_assoc, hκ, mul_inv_cancel_left]`. Use `set x : FiniteAdelicGL K n := g' * g₁⁻¹`. Establish `hx : Matrix.GeneralLinearGroup.det x = 1`. Rewrite using `[map_mul, map_inv, ← hg₁, mul_inv_cancel]`. Establish `hcont : Continuous fun h : FiniteAdelicGL K n => g₁⁻¹ * h⁻¹ * x * g₁` using `((continuous_const.mul continuous_inv).mul continuous_const).mul continuous_const`.

Establish `hx1 : g₁⁻¹ * x⁻¹ * x * g₁ = 1` using `by group`. Establish `hO : (fun h : FiniteAdelicGL K n => g₁⁻¹ * h⁻¹ * x * g₁) ⁻¹' (U : Set (FiniteAdelicGL K n)) ∈ 𝓝 x` using `hcont.continuousAt.preimage_mem_nhds (hU.mem_nhds (by rw [hx1]; exact U.one_mem))`. Take `⟨γ, -, hγ⟩` from `exists_finiteDiagonal_mem_nhds K n hx hO`. Use `⟨γ * δ, u₀ * (g₁⁻¹ * (finiteDiagonal K n γ)⁻¹ * x * g₁), mul_mem hu₀ hγ, ?_⟩` and prove the remaining obligations. Simplify using `only [x, g₁, map_mul]`.

Use `group`.
-/
theorem exists_eq_finiteDiagonal_mul_mul (hn : 0 < n) {U : Subgroup (FiniteAdelicGL K n)}
    (hU : IsOpen (U : Set (FiniteAdelicGL K n))) {g g' : FiniteAdelicGL K n}
    (h : (Matrix.GeneralLinearGroup.det g)⁻¹ * Matrix.GeneralLinearGroup.det g' ∈
      detClassSubgroup K n U) :
    ∃ γ : GL (Fin n) K, ∃ u ∈ U, g' = finiteDiagonal K n γ * g * u := by
  obtain ⟨_, ⟨κ, rfl⟩, _, ⟨u₀, hu₀, rfl⟩, hκ⟩ := Subgroup.mem_sup.1 h
  set δ : GL (Fin n) K := diagonalGL (Pi.mulSingle (⟨0, hn⟩ : Fin n) κ)
  set g₁ : FiniteAdelicGL K n := finiteDiagonal K n δ * g * u₀
  have hg₁ : Matrix.GeneralLinearGroup.det g₁ = Matrix.GeneralLinearGroup.det g' := by
    simp only [g₁, map_mul, det_finiteDiagonal, δ, det_diagonalGL_mulSingle hn]
    rw [mul_comm _ (Matrix.GeneralLinearGroup.det g), mul_assoc, hκ, mul_inv_cancel_left]
  set x : FiniteAdelicGL K n := g' * g₁⁻¹
  have hx : Matrix.GeneralLinearGroup.det x = 1 := by
    rw [map_mul, map_inv, ← hg₁, mul_inv_cancel]
  have hcont : Continuous fun h : FiniteAdelicGL K n => g₁⁻¹ * h⁻¹ * x * g₁ :=
    ((continuous_const.mul continuous_inv).mul continuous_const).mul continuous_const
  have hx1 : g₁⁻¹ * x⁻¹ * x * g₁ = 1 := by group
  have hO : (fun h : FiniteAdelicGL K n => g₁⁻¹ * h⁻¹ * x * g₁) ⁻¹' (U : Set (FiniteAdelicGL K n)) ∈
      𝓝 x :=
    hcont.continuousAt.preimage_mem_nhds (hU.mem_nhds (by rw [hx1]; exact U.one_mem))
  obtain ⟨γ, -, hγ⟩ := exists_finiteDiagonal_mem_nhds K n hx hO
  refine ⟨γ * δ, u₀ * (g₁⁻¹ * (finiteDiagonal K n γ)⁻¹ * x * g₁), mul_mem hu₀ hγ, ?_⟩
  simp only [x, g₁, map_mul]
  group

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `p q hpq`. Rewrite `hpq`, the goal using `[← DoubleCoset.out_eq' (rationalFiniteGL K n) U p, ← DoubleCoset.out_eq' (rationalFiniteGL K n) U q]`. Rewrite `hpq` using `[detDoubleCoset_mk, detDoubleCoset_mk, QuotientGroup.eq]`. Take `⟨γ, u, hu, heq⟩` from `exists_eq_finiteDiagonal_mul_mul hn hU hpq`.

Conclude with `(DoubleCoset.eq _ _ _ _).2 ⟨finiteDiagonal K n γ, ⟨γ, rfl⟩, u, hu, heq⟩`. Introduce `q`. Take `⟨a, rfl⟩` from `QuotientGroup.mk_surjective q`. Conclude with `⟨DoubleCoset.mk _ _ (diagonalGL (Pi.mulSingle (⟨0, hn⟩ : Fin n) a)), by`. Rewrite using `[detDoubleCoset_mk, det_diagonalGL_mulSingle hn]⟩`.
-/
theorem detDoubleCoset_bijective (hn : 0 < n) {U : Subgroup (FiniteAdelicGL K n)}
    (hU : IsOpen (U : Set (FiniteAdelicGL K n))) : Function.Bijective (detDoubleCoset U) := by
  constructor
  · intro p q hpq
    rw [← DoubleCoset.out_eq' (rationalFiniteGL K n) U p,
      ← DoubleCoset.out_eq' (rationalFiniteGL K n) U q] at hpq ⊢
    rw [detDoubleCoset_mk, detDoubleCoset_mk, QuotientGroup.eq] at hpq
    obtain ⟨γ, u, hu, heq⟩ := exists_eq_finiteDiagonal_mul_mul hn hU hpq
    exact (DoubleCoset.eq _ _ _ _).2 ⟨finiteDiagonal K n γ, ⟨γ, rfl⟩, u, hu, heq⟩
  · intro q
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨DoubleCoset.mk _ _ (diagonalGL (Pi.mulSingle (⟨0, hn⟩ : Fin n) a)), by
      rw [detDoubleCoset_mk, det_diagonalGL_mulSingle hn]⟩

def doubleCosetEquiv (hn : 0 < n) {U : Subgroup (FiniteAdelicGL K n)}
    (hU : IsOpen (U : Set (FiniteAdelicGL K n))) : DoubleCosetSpace K n U ≃ DetClassGroup K n U :=
  Equiv.ofBijective _ (detDoubleCoset_bijective hn hU)

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem doubleCosetEquiv_mk (hn : 0 < n) {U : Subgroup (FiniteAdelicGL K n)}
    (hU : IsOpen (U : Set (FiniteAdelicGL K n))) (g : FiniteAdelicGL K n) :
    doubleCosetEquiv hn hU (DoubleCoset.mk _ _ g) =
      QuotientGroup.mk (Matrix.GeneralLinearGroup.det g) :=
  rfl

open GroundTheory.Global GroundTheory.Global.IdeleGroup

variable (K)

/- English proof (translation)
The claim follows from `Units.ext rfl`.
-/
theorem toFinite_diagonal (a : Kˣ) :
    toFinite K (IdeleGroup.diagonal K a) = FiniteAdeleRing.unitEmbedding (𝓞 K) K a :=
  Units.ext rfl

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce `x hx`. Take `⟨_, ⟨a, rfl⟩, l, hl, hal⟩` from `Subgroup.mem_sup.1 (Subgroup.mem_comap.1 hx)`. Use `Subgroup.mem_sup.2 ⟨IdeleGroup.diagonal K a, ⟨a, rfl⟩, (IdeleGroup.diagonal K a)⁻¹ * x, ?_, mul_inv_cancel_left _ _⟩` and prove the remaining obligations. Rewrite using `[Subgroup.mem_comap, map_mul, map_inv, toFinite_diagonal, ← hal, inv_mul_cancel_left]`.

Conclude with `hl`. Use `sup_le ?_ (Subgroup.comap_mono le_sup_right)` and prove the remaining obligations. Introduce and unpack `_ ⟨a, rfl⟩`. Rewrite using `[Subgroup.mem_comap, toFinite_diagonal]`. Conclude with `Subgroup.mem_sup_left ⟨a, rfl⟩`.
-/
theorem comap_toFinite_sup (L : Subgroup (FiniteAdeleRing (𝓞 K) K)ˣ) :
    ((FiniteAdeleRing.unitEmbedding (𝓞 K) K).range ⊔ L).comap (toFinite K) =
      (IdeleGroup.diagonal K).range ⊔ L.comap (toFinite K) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨_, ⟨a, rfl⟩, l, hl, hal⟩ := Subgroup.mem_sup.1 (Subgroup.mem_comap.1 hx)
    refine Subgroup.mem_sup.2 ⟨IdeleGroup.diagonal K a, ⟨a, rfl⟩, (IdeleGroup.diagonal K a)⁻¹ * x,
      ?_, mul_inv_cancel_left _ _⟩
    rw [Subgroup.mem_comap, map_mul, map_inv, toFinite_diagonal, ← hal, inv_mul_cancel_left]
    exact hl
  · refine sup_le ?_ (Subgroup.comap_mono le_sup_right)
    rintro _ ⟨a, rfl⟩
    rw [Subgroup.mem_comap, toFinite_diagonal]
    exact Subgroup.mem_sup_left ⟨a, rfl⟩

def toFiniteQuotient (L : Subgroup (FiniteAdeleRing (𝓞 K) K)ˣ) :
    IdeleGroup K →* (FiniteAdeleRing (𝓞 K) K)ˣ ⧸ ((FiniteAdeleRing.unitEmbedding (𝓞 K) K).range ⊔ L) :=
  (QuotientGroup.mk' _).comp (toFinite K)

/- English proof (translation)
The claim follows from `(QuotientGroup.mk'_surjective _).comp fun x => ⟨ofFinite x, toFinite_ofFinite x⟩`.
-/
theorem toFiniteQuotient_surjective (L : Subgroup (FiniteAdeleRing (𝓞 K) K)ˣ) :
    Function.Surjective (toFiniteQuotient K L) :=
  (QuotientGroup.mk'_surjective _).comp fun x => ⟨ofFinite x, toFinite_ofFinite x⟩

/- English proof (translation)
Rewrite using `[toFiniteQuotient, ← MonoidHom.comap_ker, QuotientGroup.ker_mk', comap_toFinite_sup]`.
-/
theorem ker_toFiniteQuotient (L : Subgroup (FiniteAdeleRing (𝓞 K) K)ˣ) :
    (toFiniteQuotient K L).ker = (IdeleGroup.diagonal K).range ⊔ L.comap (toFinite K) := by
  rw [toFiniteQuotient, ← MonoidHom.comap_ker, QuotientGroup.ker_mk', comap_toFinite_sup]

def finiteQuotientEquiv (L : Subgroup (FiniteAdeleRing (𝓞 K) K)ˣ) :
    (FiniteAdeleRing (𝓞 K) K)ˣ ⧸ ((FiniteAdeleRing.unitEmbedding (𝓞 K) K).range ⊔ L) ≃*
      IdeleGroup K ⧸ ((IdeleGroup.diagonal K).range ⊔ L.comap (toFinite K)) :=
  ((QuotientGroup.quotientMulEquivOfEq (ker_toFiniteQuotient K L).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (toFiniteQuotient_surjective K L))).symm

@[simp]
/- English proof (translation)
Rewrite using `[finiteQuotientEquiv, MulEquiv.symm_apply_eq]`. Express the relevant statement in the definitionally equal form `_ = QuotientGroup.mk (toFinite K (ofFinite a))`. Rewrite using `[toFinite_ofFinite]`.
-/
theorem finiteQuotientEquiv_mk (L : Subgroup (FiniteAdeleRing (𝓞 K) K)ˣ)
    (a : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    finiteQuotientEquiv K L (QuotientGroup.mk a) = QuotientGroup.mk (ofFinite a) := by
  rw [finiteQuotientEquiv, MulEquiv.symm_apply_eq]
  change _ = QuotientGroup.mk (toFinite K (ofFinite a))
  rw [toFinite_ofFinite]

/- English proof (translation)
The claim follows from `eq_top_iff.2 fun _ _ w hw => absurd hw (Set.notMem_empty w)`.
-/
theorem positiveAt_empty : positiveAt (∅ : Set {w : InfinitePlace K // w.IsReal}) = ⊤ :=
  eq_top_iff.2 fun _ _ w hw => absurd hw (Set.notMem_empty w)

def finiteModulus (𝔪 : Ideal (𝓞 K)) (h𝔪 : 𝔪 ≠ ⊥) : Modulus K :=
  ⟨𝔪, h𝔪, ∅⟩

def finiteQuotientEquivRayClassGroup (𝔪 : Ideal (𝓞 K)) (h𝔪 : 𝔪 ≠ ⊥) :
    (FiniteAdeleRing (𝓞 K) K)ˣ ⧸ ((FiniteAdeleRing.unitEmbedding (𝓞 K) K).range ⊔ idealLevel 𝔪) ≃*
      (finiteModulus K 𝔪 h𝔪).RayClassGroup :=
  (finiteQuotientEquiv K (idealLevel 𝔪)).trans (QuotientGroup.quotientMulEquivOfEq (by
    rw [Modulus.rayGroup, Modulus.congruenceSubgroup, finiteModulus, positiveAt_empty, inf_top_eq]))

def finiteQuotientEquivClassGroup :
    (FiniteAdeleRing (𝓞 K) K)ˣ ⧸ ((FiniteAdeleRing.unitEmbedding (𝓞 K) K).range ⊔ finiteLevel 0) ≃*
      ClassGroup (𝓞 K) :=
  (finiteQuotientEquiv K (finiteLevel 0)).trans
    ((QuotientGroup.quotientMulEquivOfEq (by
      congr 1
      ext x
      exact (mem_standardOpenSubgroup_iff_toFinite_mem x).symm)).trans
      IdeleGroup.quotientEquivClassGroup)

variable {K}

def doubleCosetEquivRayClassGroup (hn : 0 < n) {U : Subgroup (FiniteAdelicGL K n)}
    (hU : IsOpen (U : Set (FiniteAdelicGL K n))) (𝔪 : Ideal (𝓞 K)) (h𝔪 : 𝔪 ≠ ⊥)
    (hdet : U.map (Matrix.GeneralLinearGroup.det : FiniteAdelicGL K n →* (FiniteAdeleRing (𝓞 K) K)ˣ) =
      idealLevel 𝔪) :
    DoubleCosetSpace K n U ≃ (finiteModulus K 𝔪 h𝔪).RayClassGroup :=
  (doubleCosetEquiv hn hU).trans
    ((QuotientGroup.quotientMulEquivOfEq (by rw [detClassSubgroup, hdet])).toEquiv.trans
      (finiteQuotientEquivRayClassGroup K 𝔪 h𝔪).toEquiv)

/- English proof (translation)
Establish `: M = T.subtype.mapMatrix (Matrix.of fun a b => (⟨M a b, hM a b⟩ : T))`. Use extensionality with `a b`. Both sides reduce to the same expression. Rewrite using `[this, ← RingHom.map_det]`. Conclude with `SetLike.coe_mem _`.
-/
theorem det_mem_of_forall_mem {R : Type*} [CommRing R] (T : Subring R) {M : Matrix (Fin n) (Fin n) R}
    (hM : ∀ a b, M a b ∈ T) : M.det ∈ T := by
  have : M = T.subtype.mapMatrix (Matrix.of fun a b => (⟨M a b, hM a b⟩ : T)) := by
    ext a b
    rfl
  rw [this, ← RingHom.map_det]
  exact SetLike.coe_mem _

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨g, hg, rfl⟩`. Rewrite `hg` using `[SetLike.mem_coe, mem_integralFiniteGL_iff]`. Establish `h1` using `det_mem_of_forall_mem (GroundTheory.Global.integralFiniteAdeles (𝓞 K) K) hg.1`. Establish `h2` using `det_mem_of_forall_mem (GroundTheory.Global.integralFiniteAdeles (𝓞 K) K) hg.2`.

Rewrite `h1`, `h2` using `[← Matrix.GeneralLinearGroup.val_det_apply]`. Rewrite using `[mem_finiteLevel]`. Introduce `v`. Rewrite using `[Pi.zero_apply, unitsLevel_zero, Submonoid.mem_units_iff]`. Use `⟨h1 v, ?_⟩` and prove the remaining obligations.

Establish `: ((finiteComponent v (Matrix.GeneralLinearGroup.det g))⁻¹ : (v.adicCompletion K)ˣ) = finiteComponent v (Matrix.GeneralLinearGroup.det g⁻¹)`. Rewrite using `[map_inv, map_inv]`. Rewrite using `[this]`. Conclude with `h2 v`. Introduce `a ha`.

Rewrite `ha` using `[mem_finiteLevel]`. Establish `hv : ∀ v, (a : FiniteAdeleRing (𝓞 K) K) v ∈ v.adicCompletionIntegers K ∧ ((a⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v ∈ v.adicCompletionIntegers K`. Introduce `v`. Use `ha v` as an intermediate fact. Rewrite `this` using `[Pi.zero_apply, unitsLevel_zero, Submonoid.mem_units_iff]`.

Use `⟨this.1, ?_⟩` and prove the remaining obligations. Establish `h` using `this.2`. Rewrite `h` using `[← map_inv]`. Then use the resulting hypothesis. Use `⟨diagonalGL (Pi.mulSingle (⟨0, hn⟩ : Fin n) a), ?_, det_diagonalGL_mulSingle hn a⟩` and prove the remaining obligations. Rewrite using `[SetLike.mem_coe, mem_integralFiniteGL_iff, ← map_inv]`.

Establish `key : ∀ b : (FiniteAdeleRing (𝓞 K) K)ˣ, (∀ v, (b : FiniteAdeleRing (𝓞 K) K) v ∈ v.adicCompletionIntegers K) → ∀ i j, ((diagonalGL (Pi.mulSingle (⟨0, hn⟩ : Fin n) b) : FiniteAdelicGL K n) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 K) K)) i j ∈ GroundTheory.Global.integralFiniteA …`. Introduce `b hb i j`. Rewrite using `[coe_diagonalGL, Matrix.diagonal_apply]`. Use `split_ifs with hij`. Rewrite using `[Pi.mulSingle_apply] split_ifs`.

Conclude with `hb`. Conclude with `one_mem _`. Conclude with `zero_mem _`. Use `⟨key a fun v => (hv v).1, ?_⟩` and prove the remaining obligations. Rewrite using `[← Pi.mulSingle_inv]`.

Conclude with `key a⁻¹ fun v => (hv v).2`.
-/
theorem map_det_integralFiniteGL (hn : 0 < n) :
    (integralFiniteGL K n).map
        (Matrix.GeneralLinearGroup.det : FiniteAdelicGL K n →* (FiniteAdeleRing (𝓞 K) K)ˣ) =
      finiteLevel 0 := by
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    rw [SetLike.mem_coe, mem_integralFiniteGL_iff] at hg
    have h1 := det_mem_of_forall_mem (GroundTheory.Global.integralFiniteAdeles (𝓞 K) K) hg.1
    have h2 := det_mem_of_forall_mem (GroundTheory.Global.integralFiniteAdeles (𝓞 K) K) hg.2
    rw [← Matrix.GeneralLinearGroup.val_det_apply] at h1 h2
    rw [mem_finiteLevel]
    intro v
    rw [Pi.zero_apply, unitsLevel_zero, Submonoid.mem_units_iff]
    refine ⟨h1 v, ?_⟩
    have : ((finiteComponent v (Matrix.GeneralLinearGroup.det g))⁻¹ : (v.adicCompletion K)ˣ) =
        finiteComponent v (Matrix.GeneralLinearGroup.det g⁻¹) := by
      rw [map_inv, map_inv]
    rw [this]
    exact h2 v
  · intro a ha
    rw [mem_finiteLevel] at ha
    have hv : ∀ v, (a : FiniteAdeleRing (𝓞 K) K) v ∈ v.adicCompletionIntegers K ∧
        ((a⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v ∈
          v.adicCompletionIntegers K := by
      intro v
      have := ha v
      rw [Pi.zero_apply, unitsLevel_zero, Submonoid.mem_units_iff] at this
      refine ⟨this.1, ?_⟩
      have h := this.2
      rwa [← map_inv] at h
    refine ⟨diagonalGL (Pi.mulSingle (⟨0, hn⟩ : Fin n) a), ?_, det_diagonalGL_mulSingle hn a⟩
    rw [SetLike.mem_coe, mem_integralFiniteGL_iff, ← map_inv]
    have key : ∀ b : (FiniteAdeleRing (𝓞 K) K)ˣ,
        (∀ v, (b : FiniteAdeleRing (𝓞 K) K) v ∈ v.adicCompletionIntegers K) →
        ∀ i j, ((diagonalGL (Pi.mulSingle (⟨0, hn⟩ : Fin n) b) : FiniteAdelicGL K n) :
          Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 K) K)) i j ∈
            GroundTheory.Global.integralFiniteAdeles (𝓞 K) K := by
      intro b hb i j
      rw [coe_diagonalGL, Matrix.diagonal_apply]
      split_ifs with hij
      · rw [Pi.mulSingle_apply]
        split_ifs
        · exact hb
        · exact one_mem _
      · exact zero_mem _
    refine ⟨key a fun v => (hv v).1, ?_⟩
    rw [← Pi.mulSingle_inv]
    exact key a⁻¹ fun v => (hv v).2

def doubleCosetEquivClassGroup (hn : 0 < n) :
    DoubleCosetSpace K n (integralFiniteGL K n) ≃ ClassGroup (𝓞 K) :=
  (doubleCosetEquiv hn (isOpen_integralFiniteGL K n)).trans
    ((QuotientGroup.quotientMulEquivOfEq (by rw [detClassSubgroup, map_det_integralFiniteGL hn])).toEquiv.trans
      (finiteQuotientEquivClassGroup K).toEquiv)

end AdelicGLn

end

end GroundTheory.Automorphic
