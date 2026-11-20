import Mathlib
import GroundTheory.GlobalFields.LocalFieldAtPlace
import GroundTheory.GlobalFields.Adele.Topology
import GroundTheory.GlobalFields.Adele.Discrete
import GroundTheory.GlobalFields.Adele.Compact
import GroundTheory.AutomorphicForms.GLnLocal
import GroundTheory.AutomorphicForms.LocallyProfinite
import GroundTheory.AutomorphicForms.RestrictedProductMatrix

open NumberField IsDedekindDomain Topology Filter Set
open scoped NumberField.AdeleRing RestrictedProduct

namespace GroundTheory.Automorphic

noncomputable section

instance locallyCompactSpace_matrix {m R : Type*} [Finite m] [TopologicalSpace R]
    [LocallyCompactSpace R] : LocallyCompactSpace (Matrix m m R) :=
  inferInstanceAs (LocallyCompactSpace (m → m → R))

namespace AdelicGLn

variable (K : Type*) [Field K] [NumberField K] (n : ℕ)

abbrev AdelicMatrix : Type _ := Matrix (Fin n) (Fin n) 𝔸[K]

abbrev AdelicGL : Type _ := GL (Fin n) 𝔸[K]

abbrev InfiniteAdelicGL : Type _ := GL (Fin n) (InfiniteAdeleRing K)

abbrev FiniteAdelicGL : Type _ := GL (Fin n) (FiniteAdeleRing (𝓞 K) K)

/- English proof (translation)
The claim follows from `inferInstance`.
-/
theorem isTopologicalGroup : IsTopologicalGroup (AdelicGL K n) :=
  inferInstance

/- English proof (translation)
The claim follows from `inferInstance`.
-/
theorem t2Space : T2Space (AdelicGL K n) :=
  inferInstance

/- English proof (translation)
The claim follows from `inferInstance`.
-/
theorem locallyCompactSpace : LocallyCompactSpace (AdelicGL K n) :=
  inferInstance

def det : AdelicGL K n →* (𝔸[K])ˣ :=
  Matrix.GeneralLinearGroup.det

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_det (g : AdelicGL K n) : (det K n g : 𝔸[K]) = (g : AdelicMatrix K n).det :=
  rfl

/- English proof (translation)
Use `Units.continuous_iff.2 ⟨Continuous.matrix_det (Units.continuous_val (M := AdelicMatrix K n)), ?_⟩` and prove the remaining obligations. Establish `: (fun g : AdelicGL K n => (((det K n g)⁻¹ : (𝔸[K])ˣ) : 𝔸[K])) = fun g => ((g⁻¹ : AdelicGL K n) : AdelicMatrix K n).det`. Use function extensionality and compare the values at `g`. Rewrite using `[← map_inv]`. Both sides reduce to the same expression.

Rewrite using `[this]`. Conclude with `Continuous.matrix_det (Units.continuous_coe_inv (M := AdelicMatrix K n))`.
-/
theorem continuous_det : Continuous (det K n) := by
  refine Units.continuous_iff.2 ⟨Continuous.matrix_det (Units.continuous_val (M := AdelicMatrix K n)),
    ?_⟩
  have : (fun g : AdelicGL K n => (((det K n g)⁻¹ : (𝔸[K])ˣ) : 𝔸[K])) =
      fun g => ((g⁻¹ : AdelicGL K n) : AdelicMatrix K n).det := by
    funext g
    rw [← map_inv]
    rfl
  rw [this]
  exact Continuous.matrix_det (Units.continuous_coe_inv (M := AdelicMatrix K n))

def prodEquiv : AdelicGL K n ≃ₜ* InfiniteAdelicGL K n × FiniteAdelicGL K n :=
  glProdEquiv (Fin n) (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)

@[simp]
/- English proof (translation)
The claim follows from `rfl @[simp]`.
-/
theorem prodEquiv_apply_fst (g : AdelicGL K n) (a b : Fin n) :
    (prodEquiv K n g).1 a b = (g a b).1 :=
  rfl

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem prodEquiv_apply_snd (g : AdelicGL K n) (a b : Fin n) :
    (prodEquiv K n g).2 a b = (g a b).2 :=
  rfl

def infiniteEquiv : InfiniteAdelicGL K n ≃ₜ* Π w : InfinitePlace K, GL (Fin n) w.Completion :=
  glPiEquiv (Fin n) fun w : InfinitePlace K => w.Completion

omit [NumberField K] in
@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem infiniteEquiv_apply (g : InfiniteAdelicGL K n) (w : InfinitePlace K) (a b : Fin n) :
    infiniteEquiv K n g w a b = g a b w :=
  rfl

/- English proof (translation)
Rewrite using `[GLnLocal.mem_integralMatrices]`. Simplify using `only [GroundTheory.Global.mem_valuationInteger_iff]`.
-/
theorem mem_integralMatrices_adicCompletion (v : HeightOneSpectrum (𝓞 K))
    (M : Matrix (Fin n) (Fin n) (v.adicCompletion K)) :
    M ∈ GLnLocal.integralMatrices (v.adicCompletion K) n ↔
      ∀ a b, M a b ∈ v.adicCompletionIntegers K := by
  rw [GLnLocal.mem_integralMatrices]
  simp only [GroundTheory.Global.mem_valuationInteger_iff]

def finiteRestrictedEquiv :
    FiniteAdelicGL K n ≃ₜ* Πʳ v : HeightOneSpectrum (𝓞 K),
      [GL (Fin n) (v.adicCompletion K), GLnLocal.integralGL (v.adicCompletion K) n] :=
  (RestrictedProduct.matrixUnitsEquiv (Fin n)
    (R := fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
    (B := fun v => v.adicCompletionIntegers K)
    (C := fun v => GLnLocal.integralMatrices (v.adicCompletion K) n)
    (mem_integralMatrices_adicCompletion K n)
    (fun v => Valued.isOpen_valuationSubring (v.adicCompletion K))).trans
    (RestrictedProduct.congrSetsMul fun v => by
      rw [GLnLocal.integralGL_eq_units]
      rfl)

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem finiteRestrictedEquiv_apply (g : FiniteAdelicGL K n) (v : HeightOneSpectrum (𝓞 K))
    (a b : Fin n) :
    (finiteRestrictedEquiv K n g v : GL (Fin n) (v.adicCompletion K)) a b = g a b v :=
  rfl

def restrictedProductEquiv :
    AdelicGL K n ≃ₜ* (Π w : InfinitePlace K, GL (Fin n) w.Completion) ×
      Πʳ v : HeightOneSpectrum (𝓞 K),
        [GL (Fin n) (v.adicCompletion K), GLnLocal.integralGL (v.adicCompletion K) n] :=
  (prodEquiv K n).trans
    { toMulEquiv := MulEquiv.prodCongr (infiniteEquiv K n).toMulEquiv
        (finiteRestrictedEquiv K n).toMulEquiv
      continuous_toFun := ((infiniteEquiv K n).continuous.comp continuous_fst).prodMk
        ((finiteRestrictedEquiv K n).continuous.comp continuous_snd)
      continuous_invFun := ((infiniteEquiv K n).symm.continuous.comp continuous_fst).prodMk
        ((finiteRestrictedEquiv K n).symm.continuous.comp continuous_snd) }

@[simp]
/- English proof (translation)
The claim follows from `rfl @[simp]`.
-/
theorem restrictedProductEquiv_apply_fst (g : AdelicGL K n) (w : InfinitePlace K) (a b : Fin n) :
    (restrictedProductEquiv K n g).1 w a b = (g a b).1 w :=
  rfl

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem restrictedProductEquiv_apply_snd (g : AdelicGL K n) (v : HeightOneSpectrum (𝓞 K))
    (a b : Fin n) :
    ((restrictedProductEquiv K n g).2 v : GL (Fin n) (v.adicCompletion K)) a b = (g a b).2 v :=
  rfl

/- English proof (translation)
The claim follows from `((restrictedProductEquiv K n g).2).2`.
-/
theorem eventually_mem_integralGL (g : AdelicGL K n) :
    ∀ᶠ v in cofinite, (restrictedProductEquiv K n g).2 v ∈
      GLnLocal.integralGL (v.adicCompletion K) n :=
  ((restrictedProductEquiv K n g).2).2

def integralFiniteMatrices : Subring (Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 K) K)) :=
  (RingHom.mapMatrix (GroundTheory.Global.integralFiniteAdeles (𝓞 K) K).subtype).range

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨N, rfl⟩ a b`. Conclude with `(N a b).2`. Introduce `h`. Conclude with `⟨Matrix.of fun a b => ⟨M a b, h a b⟩, rfl⟩`.
-/
theorem mem_integralFiniteMatrices {M : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 K) K)} :
    M ∈ integralFiniteMatrices K n ↔
      ∀ a b, M a b ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 K) K := by
  constructor
  · rintro ⟨N, rfl⟩ a b
    exact (N a b).2
  · intro h
    exact ⟨Matrix.of fun a b => ⟨M a b, h a b⟩, rfl⟩

def integralFiniteGL : Subgroup (FiniteAdelicGL K n) :=
  (integralFiniteMatrices K n).toSubmonoid.units

/- English proof (translation)
Rewrite using `[integralFiniteGL, Submonoid.mem_units_iff, Subring.mem_toSubmonoid, Subring.mem_toSubmonoid, mem_integralFiniteMatrices, mem_integralFiniteMatrices]`.
-/
theorem mem_integralFiniteGL_iff {g : FiniteAdelicGL K n} :
    g ∈ integralFiniteGL K n ↔
      (∀ a b, g a b ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 K) K) ∧
        ∀ a b, (g⁻¹ : FiniteAdelicGL K n) a b ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 K) K := by
  rw [integralFiniteGL, Submonoid.mem_units_iff, Subring.mem_toSubmonoid,
    Subring.mem_toSubmonoid, mem_integralFiniteMatrices, mem_integralFiniteMatrices]

/- English proof (translation)
Establish `hinv : ∀ v a b, ((finiteRestrictedEquiv K n g v)⁻¹ : GL (Fin n) (v.adicCompletion K)) a b = (g⁻¹ : FiniteAdelicGL K n) a b v` using `fun v a b => by`. Rewrite using `[← RestrictedProduct.inv_apply, ← map_inv]`. Both sides reduce to the same expression. Simplify using `only [mem_integralFiniteGL_iff, GLnLocal.mem_integralGL_iff, hinv, finiteRestrictedEquiv_apply, GroundTheory.Global.mem_valuationInteger_iff, GroundTheory.Global.mem_integralFiniteAdeles]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨h1, h2⟩ v`. Conclude with `⟨fun a b => h1 a b v, fun a b => h2 a b v⟩`. Introduce `h`. Conclude with `⟨fun a b v => (h v).1 a b, fun a b v => (h v).2 a b⟩`.
-/
theorem mem_integralFiniteGL_iff_forall {g : FiniteAdelicGL K n} :
    g ∈ integralFiniteGL K n ↔
      ∀ v, finiteRestrictedEquiv K n g v ∈ GLnLocal.integralGL (v.adicCompletion K) n := by
  have hinv : ∀ v a b, ((finiteRestrictedEquiv K n g v)⁻¹ : GL (Fin n) (v.adicCompletion K)) a b =
      (g⁻¹ : FiniteAdelicGL K n) a b v := fun v a b => by
    rw [← RestrictedProduct.inv_apply, ← map_inv]
    rfl
  simp only [mem_integralFiniteGL_iff, GLnLocal.mem_integralGL_iff, hinv,
    finiteRestrictedEquiv_apply, GroundTheory.Global.mem_valuationInteger_iff,
    GroundTheory.Global.mem_integralFiniteAdeles]
  constructor
  · rintro ⟨h1, h2⟩ v
    exact ⟨fun a b => h1 a b v, fun a b => h2 a b v⟩
  · intro h
    exact ⟨fun a b v => (h v).1 a b, fun a b v => (h v).2 a b⟩

/- English proof (translation)
Establish `: (integralFiniteMatrices K n : Set (Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 K) K))) = ⋂ a, ⋂ b, (fun M : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 K) K) => M a b) ⁻¹' (GroundTheory.Global.integralFiniteAdeles (𝓞 K) K)`. Use extensionality with `M`. Simplify using `[mem_integralFiniteMatrices]`. Rewrite using `[this]`. Conclude with `isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b => GroundTheory.Global.isOpen_integralFiniteAdeles.preimage (continuous_apply_apply a b)`.
-/
theorem isOpen_integralFiniteMatrices :
    IsOpen (integralFiniteMatrices K n : Set (Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 K) K))) := by
  have : (integralFiniteMatrices K n : Set (Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 K) K))) =
      ⋂ a, ⋂ b, (fun M : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 K) K) => M a b) ⁻¹'
        (GroundTheory.Global.integralFiniteAdeles (𝓞 K) K) := by
    ext M
    simp [mem_integralFiniteMatrices]
  rw [this]
  exact isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b =>
    GroundTheory.Global.isOpen_integralFiniteAdeles.preimage (continuous_apply_apply a b)

/- English proof (translation)
Establish `: (integralFiniteMatrices K n : Set (Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 K) K))) = Set.pi univ fun _ => Set.pi univ fun _ => (GroundTheory.Global.integralFiniteAdeles (𝓞 K) K : Set (FiniteAdeleRing (𝓞 K) K))`. Conclude with `Set.ext fun M => ⟨fun h a _ b _ => (mem_integralFiniteMatrices K n).1 h a b, fun h => (mem_integralFiniteMatrices K n).2 fun a b => h a (mem_univ a) b (mem_univ b)⟩`. Rewrite using `[this]`. Conclude with `isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => GroundTheory.Global.isCompact_integralFiniteAdeles K`.
-/
theorem isCompact_integralFiniteMatrices :
    IsCompact (integralFiniteMatrices K n :
      Set (Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 K) K))) := by
  have : (integralFiniteMatrices K n : Set (Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 K) K))) =
      Set.pi univ fun _ => Set.pi univ fun _ =>
        (GroundTheory.Global.integralFiniteAdeles (𝓞 K) K : Set (FiniteAdeleRing (𝓞 K) K)) := by
    exact Set.ext fun M =>
      ⟨fun h a _ b _ => (mem_integralFiniteMatrices K n).1 h a b,
        fun h => (mem_integralFiniteMatrices K n).2 fun a b => h a (mem_univ a) b (mem_univ b)⟩
  rw [this]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
    GroundTheory.Global.isCompact_integralFiniteAdeles K

/- English proof (translation)
The claim follows from `Submonoid.isOpen_units (isOpen_integralFiniteMatrices K n)`.
-/
theorem isOpen_integralFiniteGL : IsOpen (integralFiniteGL K n : Set (FiniteAdelicGL K n)) :=
  Submonoid.isOpen_units (isOpen_integralFiniteMatrices K n)

/- English proof (translation)
Establish `h` using `(isCompact_integralFiniteMatrices K n).prod (MulOpposite.opHomeomorph.symm.isCompact_preimage.2 (isCompact_integralFiniteMatrices K n))`. Use `Units.isClosedEmbedding_embedProduct.isCompact_preimage h using 1` and compare the differences between its conclusion and the goal. Use extensionality with `u`. Simplify using `only [SetLike.mem_coe, integralFiniteGL, Submonoid.mem_units_iff, Set.mem_preimage, Set.mem_prod, Units.embedProduct_apply, Subring.mem_toSubmonoid]`. Conclude with `Iff.rfl`.
-/
theorem isCompact_integralFiniteGL :
    IsCompact (integralFiniteGL K n : Set (FiniteAdelicGL K n)) := by
  have h := (isCompact_integralFiniteMatrices K n).prod
    (MulOpposite.opHomeomorph.symm.isCompact_preimage.2 (isCompact_integralFiniteMatrices K n))
  convert Units.isClosedEmbedding_embedProduct.isCompact_preimage h using 1
  ext u
  simp only [SetLike.mem_coe, integralFiniteGL, Submonoid.mem_units_iff, Set.mem_preimage,
    Set.mem_prod, Units.embedProduct_apply, Subring.mem_toSubmonoid]
  exact Iff.rfl

def integralFiniteOpenSubgroup : OpenSubgroup (FiniteAdelicGL K n) where
  toSubgroup := integralFiniteGL K n
  isOpen' := isOpen_integralFiniteGL K n

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun s _ hs => Set.subsingleton_of_image hinj s (isTotallyDisconnected_of_totallyDisconnectedSpace _ _ (Set.subset_univ _) (hs.image f hf.continuousOn))⟩`.
-/
theorem totallyDisconnectedSpace_of_injective {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [TotallyDisconnectedSpace Y] {f : X → Y} (hf : Continuous f)
    (hinj : Function.Injective f) : TotallyDisconnectedSpace X :=
  ⟨fun s _ hs => Set.subsingleton_of_image hinj s
    (isTotallyDisconnected_of_totallyDisconnectedSpace _ _ (Set.subset_univ _)
      (hs.image f hf.continuousOn))⟩

instance totallyDisconnectedSpace_finite : TotallyDisconnectedSpace (FiniteAdelicGL K n) :=
  totallyDisconnectedSpace_of_injective
    (f := fun g v => finiteRestrictedEquiv K n g v)
    (continuous_pi fun v =>
      (_root_.RestrictedProduct.continuous_eval v).comp (finiteRestrictedEquiv K n).continuous)
    fun _ _ hgh => (finiteRestrictedEquiv K n).injective
      (Subtype.ext (funext fun v => congrFun hgh v))

/- English proof (translation)
The claim follows from `hasBasis_nhds_one_compactOpenSubgroup`.
-/
theorem finite_hasBasis_nhds_one :
    (𝓝 (1 : FiniteAdelicGL K n)).HasBasis
      (fun H : OpenSubgroup (FiniteAdelicGL K n) => IsCompact (H : Set (FiniteAdelicGL K n)))
      fun H => (H : Set (FiniteAdelicGL K n)) :=
  hasBasis_nhds_one_compactOpenSubgroup

def diagonal : GL (Fin n) K →* AdelicGL K n :=
  Units.map (algebraMap K 𝔸[K]).mapMatrix.toMonoidHom

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem diagonal_apply (γ : GL (Fin n) K) (a b : Fin n) :
    diagonal K n γ a b = algebraMap K 𝔸[K] (γ a b) :=
  rfl

/- English proof (translation)
Introduce `_ _ h` and use `Units.ext <| Matrix.ext fun a b => NumberField.AdeleRing.algebraMap_injective (𝓞 K) K (congrArg (fun g : AdelicGL K n => g a b) h)`.
-/
theorem diagonal_injective : Function.Injective (diagonal K n) := fun _ _ h =>
  Units.ext <| Matrix.ext fun a b =>
    NumberField.AdeleRing.algebraMap_injective (𝓞 K) K (congrArg (fun g : AdelicGL K n => g a b) h)

def rationalGL : Subgroup (AdelicGL K n) :=
  (diagonal K n).range

/- English proof (translation)
Use `GroundTheory.Global.discreteTopology_principalSubgroup K` as an intermediate fact. Take `⟨V, hVo, hV⟩` from `isOpen_induced_iff.1 (isOpen_discrete ({0} : Set (NumberField.AdeleRing.principalSubgroup (𝓞 K) K)))`. Use `⟨V, hVo, ?_, fun k hk => ?_⟩` and prove the remaining obligations. Establish `: (0 : NumberField.AdeleRing.principalSubgroup (𝓞 K) K) ∈ Subtype.val ⁻¹' V`. Rewrite using `[hV]`.

Both sides reduce to the same expression. Conclude with `this`. Establish `: (⟨algebraMap K 𝔸[K] k, ⟨k, rfl⟩⟩ : NumberField.AdeleRing.principalSubgroup (𝓞 K) K) ∈ Subtype.val ⁻¹' V` using `hk`. Rewrite `this` using `[hV, Set.mem_singleton_iff, Subtype.ext_iff]`. Conclude with `NumberField.AdeleRing.algebraMap_injective (𝓞 K) K (this.trans (map_zero _).symm)`.
-/
theorem exists_isOpen_inter_eq_zero :
    ∃ V : Set 𝔸[K], IsOpen V ∧ (0 : 𝔸[K]) ∈ V ∧ ∀ k : K, algebraMap K 𝔸[K] k ∈ V → k = 0 := by
  have := GroundTheory.Global.discreteTopology_principalSubgroup K
  obtain ⟨V, hVo, hV⟩ := isOpen_induced_iff.1
    (isOpen_discrete ({0} : Set (NumberField.AdeleRing.principalSubgroup (𝓞 K) K)))
  refine ⟨V, hVo, ?_, fun k hk => ?_⟩
  · have : (0 : NumberField.AdeleRing.principalSubgroup (𝓞 K) K) ∈ Subtype.val ⁻¹' V := by
      rw [hV]; rfl
    exact this
  · have : (⟨algebraMap K 𝔸[K] k, ⟨k, rfl⟩⟩ : NumberField.AdeleRing.principalSubgroup (𝓞 K) K) ∈
        Subtype.val ⁻¹' V := hk
    rw [hV, Set.mem_singleton_iff, Subtype.ext_iff] at this
    exact NumberField.AdeleRing.algebraMap_injective (𝓞 K) K (this.trans (map_zero _).symm)

/- English proof (translation)
Take `⟨V, hVo, hV0, hV⟩` from `exists_isOpen_inter_eq_zero K`. Set `W : Set (AdelicGL K n)` to `⋂ a, ⋂ b, (fun g : AdelicGL K n => (g : AdelicMatrix K n) a b - (1 : AdelicMatrix K n) a b) ⁻¹' V`. Establish `hWo : IsOpen W` using `isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b => hVo.preimage ((Continuous.matrix_elem (Units.continuous_val (M := AdelicMatrix K n)) a b).sub continuous_const)`. Use `discreteTopology_of_isOpen_singleton_one (isOpen_induced_iff.2 ⟨W, hWo, ?_⟩)` and prove the remaining obligations. Use extensionality with `⟨g, γ, rfl⟩`.

Simplify using `only [W, Set.mem_preimage, Set.mem_iInter, Set.mem_singleton_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `hγ : γ = 1`. Establish `hsub : ((diagonal K n γ : AdelicGL K n) : AdelicMatrix K n) - 1 = (algebraMap K 𝔸[K]).mapMatrix ((γ : Matrix (Fin n) (Fin n) K) - 1)`.

Rewrite using `[map_sub, map_one]`. Both sides reduce to the same expression. Use `Units.ext <| Matrix.ext fun a b => ?_` and prove the remaining obligations. Establish `h1` using `h a b`. Rewrite `h1` using `[← Matrix.sub_apply, hsub]`.

Establish `h2` using `hV _ h1`. Rewrite `h2` using `[Matrix.sub_apply, sub_eq_zero]`. Conclude with `h2`. Substitute `hγ` using the available equality. Conclude with `Subtype.ext (map_one _)`.

Introduce `h a b`. Establish `: (diagonal K n γ : AdelicGL K n) = 1` using `congrArg Subtype.val h`. Rewrite using `[this, Units.val_one, sub_self]`. Conclude with `hV0`.
-/
theorem discreteTopology_rationalGL : DiscreteTopology (rationalGL K n) := by
  obtain ⟨V, hVo, hV0, hV⟩ := exists_isOpen_inter_eq_zero K
  let W : Set (AdelicGL K n) :=
    ⋂ a, ⋂ b, (fun g : AdelicGL K n => (g : AdelicMatrix K n) a b - (1 : AdelicMatrix K n) a b) ⁻¹' V
  have hWo : IsOpen W := isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b =>
    hVo.preimage
      ((Continuous.matrix_elem (Units.continuous_val (M := AdelicMatrix K n)) a b).sub
        continuous_const)
  refine discreteTopology_of_isOpen_singleton_one (isOpen_induced_iff.2 ⟨W, hWo, ?_⟩)
  ext ⟨g, γ, rfl⟩
  simp only [W, Set.mem_preimage, Set.mem_iInter, Set.mem_singleton_iff]
  constructor
  · intro h
    have hγ : γ = 1 := by
      have hsub : ((diagonal K n γ : AdelicGL K n) : AdelicMatrix K n) - 1 =
          (algebraMap K 𝔸[K]).mapMatrix ((γ : Matrix (Fin n) (Fin n) K) - 1) := by
        rw [map_sub, map_one]
        rfl
      refine Units.ext <| Matrix.ext fun a b => ?_
      have h1 := h a b
      rw [← Matrix.sub_apply, hsub] at h1
      have h2 := hV _ h1
      rw [Matrix.sub_apply, sub_eq_zero] at h2
      exact h2
    subst hγ
    exact Subtype.ext (map_one _)
  · intro h a b
    have : (diagonal K n γ : AdelicGL K n) = 1 := congrArg Subtype.val h
    rw [this, Units.val_one, sub_self]
    exact hV0

/- English proof (translation)
The claim follows from `have := discreteTopology_rationalGL K n Subgroup.isClosed_of_discrete`.
-/
theorem isClosed_rationalGL : IsClosed (rationalGL K n : Set (AdelicGL K n)) :=
  have := discreteTopology_rationalGL K n
  Subgroup.isClosed_of_discrete

end AdelicGLn

end

end GroundTheory.Automorphic
