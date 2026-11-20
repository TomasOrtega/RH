import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SignatureConjugationInvariant
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChainWideTwistTransport

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace GlobalTheory.WittLow

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Lin

variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {h : V →ₗ⋆[K] V →ₗ[K] K}

/- English proof (translation)
Establish `h0 : (LinearMap.range h).dualCoannihilator = ⊥`. Rewrite using `[eq_bot_iff]`. Introduce `v hv`. Rewrite `hv` using `[Submodule.mem_dualCoannihilator]`. Conclude with `hnd.2 v fun x => hv _ ⟨x, rfl⟩`.

Establish `h1` using `Subspace.dualCoannihilator_dualAnnihilator_eq (W := LinearMap.range h)`. Rewrite `h1` using `[h0, Submodule.dualAnnihilator_bot]`. Establish `: f ∈ LinearMap.range h` using `by rw [← h1]; trivial`. Conclude with `this`.
-/
theorem exists_repr (hnd : h.Nondegenerate) (f : V →ₗ[K] K) : ∃ w, h w = f := by
  have h0 : (LinearMap.range h).dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_dualCoannihilator] at hv
    exact hnd.2 v fun x => hv _ ⟨x, rfl⟩
  have h1 := Subspace.dualCoannihilator_dualAnnihilator_eq (W := LinearMap.range h)
  rw [h0, Submodule.dualAnnihilator_bot] at h1
  have : f ∈ LinearMap.range h := by rw [← h1]; trivial
  exact this

/- English proof (translation)
Assume the negation of the conclusion as `hn`. Take `⟨f, hf, hI⟩` from `Submodule.exists_dual_map_eq_bot_of_notMem hn inferInstance`. Take `⟨w, rfl⟩` from `exists_repr hnd f`. Use `hf (hv w fun y hy => ?_)` and prove the remaining obligations. Establish `: h w y = 0`.

Establish `: h w y ∈ I.map (h w)` using `⟨y, hy, rfl⟩`. Rewrite `this` using `[hI]`. Then use the resulting hypothesis. Rewrite using `[← hs.eq w y, this, map_zero]`.
-/
theorem mem_of_orth (hs : h.IsSymm) (hnd : h.Nondegenerate) (I : Submodule K V) (v : V)
    (hv : ∀ x, (∀ y ∈ I, h y x = 0) → h x v = 0) : v ∈ I := by
  by_contra hn
  obtain ⟨f, hf, hI⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hn inferInstance
  obtain ⟨w, rfl⟩ := exists_repr hnd f
  refine hf (hv w fun y hy => ?_)
  have : h w y = 0 := by
    have : h w y ∈ I.map (h w) := ⟨y, hy, rfl⟩
    rwa [hI] at this
  rw [← hs.eq w y, this, map_zero]

/- English proof (translation)
Establish `hsurj : LinearMap.range (LinearMap.pi fun j => h (e j)) = ⊤`. Rewrite using `[eq_top_iff]`. Introduce `c _`. Take `⟨f, hf⟩` from `LinearMap.exists_extend ((Module.Basis.span he).constr K fun j => star (c j))`. Take `⟨w, rfl⟩` from `exists_repr hnd f`.

Use `⟨w, funext fun j => ?_⟩` and prove the remaining obligations. Establish `h1` using `LinearMap.congr_fun hf (Module.Basis.span he j)`. Rewrite `h1` using `[Module.Basis.constr_basis, LinearMap.comp_apply, Submodule.subtype_apply, Module.Basis.span_apply]`. Rewrite using `[LinearMap.pi_apply, ← hs.eq w (e j), h1]`. Conclude with `star_star _`.

Use `LinearMap.finrank_range_add_finrank_ker (LinearMap.pi fun j => h (e j))` as an intermediate fact. Rewrite `this` using `[hsurj, finrank_top]`. Simplify using `using this`.
-/
theorem finrank_orth (hs : h.IsSymm) (hnd : h.Nondegenerate) {i : ℕ} (e : Fin i → V) (he : LinearIndependent K e) :
    i + Module.finrank K (LinearMap.ker (LinearMap.pi fun j => h (e j))) = Module.finrank K V := by
  have hsurj : LinearMap.range (LinearMap.pi fun j => h (e j)) = ⊤ := by
    rw [eq_top_iff]
    intro c _
    obtain ⟨f, hf⟩ := LinearMap.exists_extend ((Module.Basis.span he).constr K fun j => star (c j))
    obtain ⟨w, rfl⟩ := exists_repr hnd f
    refine ⟨w, funext fun j => ?_⟩
    have h1 := LinearMap.congr_fun hf (Module.Basis.span he j)
    rw [Module.Basis.constr_basis, LinearMap.comp_apply, Submodule.subtype_apply, Module.Basis.span_apply] at h1
    rw [LinearMap.pi_apply, ← hs.eq w (e j), h1]
    exact star_star _
  have := LinearMap.finrank_range_add_finrank_ker (LinearMap.pi fun j => h (e j))
  rw [hsurj, finrank_top] at this
  simpa using this

end Lin

section Lat

variable {E : Type} [Field E] [NumberField E] [StarRing E]

omit [NumberField E] in

/- English proof (translation)
Simplify using `[Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf]`.
-/
theorem mem_dual {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
    (h : V →ₗ⋆[E] V →ₗ[E] E) (L : Submodule (𝓞 E) V) (x : V) :
    x ∈ Formalism.HermitianLatticesTheory.dual h L ↔ ∀ y ∈ L, h y x ∈ (1 : Submodule (𝓞 E) E) := by
  simp [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf]

/- English proof (translation)
Establish `hs` using `V.herm`. Establish `hnd` using `V.nondeg`. Establish `hfg : V.L0.FG` using `V.standardTuple_isLattice.fg`. Establish `hsp : Submodule.span E (V.L0 : Set V.V) = ⊤` using `V.standardTuple_isLattice.span_eq_top`. Establish `hst1 : ∀ x : E, x ∈ (1 : Submodule (𝓞 E) E) → star x ∈ (1 : Submodule (𝓞 E) E)`.

Introduce `x hx`. Take `⟨r, rfl⟩` from `Submodule.mem_one.1 hx`. Conclude with `Submodule.mem_one.2 ⟨⟨_, hst _ r.2⟩, rfl⟩`. Establish `hL : ∀ x, x ∈ V.L0 ↔ ∀ y ∈ V.L0, V.hT y x ∈ (1 : Submodule (𝓞 E) E)` using `fun x => by`. Rewrite using `[← mem_dual, V.baseLattice_isUnimodular]`.

Use `set I : Submodule E V.V := Submodule.span E (Set.range e) with hI`. Use `set P : Submodule E V.V := LinearMap.ker (LinearMap.pi fun j => V.hT (e j)) with hPdef`. Establish `hP : ∀ x, x ∈ P ↔ ∀ y ∈ I, V.hT y x = 0`. Introduce `x`. Prove the components needed by the constructor for the conclusion.

Introduce `hx y hy`. Establish `: I ≤ LinearMap.ker (V.hT.flip x)`. Rewrite using `[hI, Submodule.span_le]`. Introduce and unpack `_ ⟨j, rfl⟩`. Conclude with `congrFun hx j`.

Conclude with `this hy`. Introduce `hx`. Conclude with `funext fun j => hx _ (Submodule.subset_span ⟨j, rfl⟩)`. Establish `hIP : I ≤ P`. Rewrite using `[hI, Submodule.span_le]`.

Introduce and unpack `_ ⟨j, rfl⟩`. Conclude with `funext fun a => hiso a j`. Establish `hPI : ∀ x ∈ P, ∀ y ∈ I, V.hT x y = 0` using `fun x hx y hy => by`. Rewrite using `[← hs.eq y x, (hP x).1 hx y hy, map_zero]`. Take `⟨σ, σI, σid, σL⟩` from `GlobalTheory.ColPeriodCompare.exists_proj V.L0 hfg hsp I`.

Take `⟨π, πP, πid, πL⟩` from `GlobalTheory.ColPeriodCompare.exists_proj V.L0 hfg hsp P`. Use `set W : Submodule E V.V := P ⊓ LinearMap.ker σ with hW`. Establish `hsub : ∀ z ∈ P, z - σ z ∈ W` using `fun z hz => ⟨P.sub_mem hz (hIP (σI z)), by`. Express the relevant statement in the definitionally equal form `σ (z - σ z) = 0`. Rewrite using `[map_sub, σid _ (σI z), sub_self]⟩`.

Establish `hsup : I ⊔ W = P`. Use `le_antisymm (sup_le hIP inf_le_left) fun z hz => ?_` and prove the remaining obligations. Rewrite using `[← add_sub_cancel (σ z) z]`. Conclude with `Submodule.add_mem_sup (σI z) (hsub z hz)`. Establish `hinf : I ⊓ W = ⊥`.

Rewrite using `[eq_bot_iff]`. Introduce and unpack `z ⟨h1, -, h2⟩`. Rewrite using `[Submodule.mem_bot, ← σid z h1]`. Conclude with `h2`. Establish `hrk : Module.finrank E W + 2 * i = V.rank`.

Establish `h1` using `Submodule.finrank_sup_add_finrank_inf_eq I W`. Establish `h2` using `finrank_orth hs hnd e he`. Establish `h3 : Module.finrank E I = i` using `by rw [hI, finrank_span_eq_card he, Fintype.card_fin]`. Rewrite `h1` using `[hsup, hinf, finrank_bot, h3]`. Rewrite `h2` using `[← hPdef, V.rank_eq]`.

Use linear arithmetic over natural numbers and integers. Establish `hWz : ∀ v ∈ W, ∀ z ∈ P, V.hT z v = V.hT (z - σ z) v` using `fun v hv z hz => by`. Rewrite using `[map_sub, LinearMap.sub_apply, (hP v).1 hv.1 _ (σI z), sub_zero]`. Establish `hrad : ∀ v : W, (∀ y : W, V.hT y v = 0) → v = 0`. Introduce `v hv`.

Establish `: (v : V.V) ∈ I` using `mem_of_orth hs hnd I v fun x hx => by`. Rewrite using `[hWz v v.2 x ((hP x).2 hx)]`. Conclude with `hv ⟨_, hsub x ((hP x).2 hx)⟩`. Establish `h2 : (v : V.V) ∈ I ⊓ W` using `⟨this, v.2⟩`. Rewrite `h2` using `[hinf]`.

Conclude with `Subtype.ext h2`. Establish `hden : ∀ v : V.V, ∃ d : 𝓞 E, d ≠ 0 ∧ d • v ∈ V.L0`. Introduce `v`. Establish `hv : v ∈ Submodule.span E (V.L0 : Set V.V)` using `by rw [hsp]; trivial`. Take `⟨d, hd⟩` from `multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 E)) E (V.L0 : Set V.V) v hv`.

Rewrite `hd` using `[Submodule.span_eq]`. Conclude with `⟨d, nonZeroDivisors.coe_ne_zero d, hd⟩`. Set `h' : W →ₗ⋆[E] W →ₗ[E] E` to `V.hT.domRestrict₁₂ W W`. Establish `hh : ∀ x y : W, h' x y = V.hT x y` using `fun _ _ => rfl`. Set `j : W →ₗ[𝓞 E] V.V` to `W.subtype.restrictScalars (𝓞 E)`.

Set `L' : Submodule (𝓞 E) W` to `V.L0.comap j`. Establish `hL' : ∀ x : W, x ∈ L' ↔ (x : V.V) ∈ V.L0` using `fun _ => Iff.rfl`. Establish `hlat : Submodule.IsLattice E L'`. Prove the components needed by the constructor for the conclusion. Use `Submodule.fg_of_fg_map_injective j Subtype.val_injective ?_` and prove the remaining obligations.

Establish `: IsNoetherian (𝓞 E) V.L0` using `isNoetherian_of_fg_of_noetherian _ hfg`. Establish `: IsNoetherian (𝓞 E) (L'.map j)` using `isNoetherian_of_le (Submodule.map_comap_le _ _)`. Conclude with `Module.Finite.iff_fg.mp inferInstance`. Rewrite using `[eq_top_iff]`. Introduce `v _`.

Take `⟨d, hd, hv⟩` from `hden v`. Establish `hd' : algebraMap (𝓞 E) E d ≠ 0` using `by simpa using hd`. Establish `: v = (algebraMap (𝓞 E) E d)⁻¹ • (d • v)`. Rewrite using `[← IsScalarTower.algebraMap_smul E d v, smul_smul, inv_mul_cancel₀ hd', one_smul]`. Rewrite using `[this]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span hv)`. Establish `hun : Formalism.HermitianLatticesTheory.IsUnimodular h' L'`. Use extensionality with `v`. Rewrite using `[mem_dual]`. Use `⟨fun hv => ?_, fun hv y hy => (hL _).1 hv _ hy⟩` and prove the remaining obligations.

Take `⟨w, hw⟩` from `exists_repr hnd (V.hT v ∘ₗ π)`. Establish `hw' : ∀ z, V.hT w z = V.hT v (π z)` using `fun z => LinearMap.congr_fun hw z`. Establish `hwL : w ∈ V.L0`. Rewrite using `[hL]`. Introduce `y hy`.

Rewrite using `[← hs.eq w y, hw', starRingEnd_apply, ← starRingEnd_apply, hs.eq, hWz v v.2 _ (πP y)]`. Conclude with `hv ⟨_, hsub _ (πP y)⟩ (V.L0.sub_mem (πL y hy) (σL _ (πL y hy)))`. Establish `hwv : w - v ∈ I` using `mem_of_orth hs hnd I _ fun x hx => by`. Rewrite using `[← hs.eq, map_sub, LinearMap.sub_apply, hw', πid x ((hP x).2 hx), sub_self, map_zero]`. Establish `h1` using `σid _ hwv`.

Rewrite `h1` using `[map_sub, show σ v = 0 from v.2.2, sub_zero]`. Rewrite using `[hL', show (v : V.V) = w - σ w by rw [h1]; abel]`. Conclude with `V.L0.sub_mem hwL (σL w hwL)`. Establish `hs' : h'.IsSymm` using `⟨fun x y => hs.eq _ _⟩`. Establish `hnd' : h'.Nondegenerate` using `⟨fun x hx => hrad x fun y => by`.

Rewrite using `[← hs.eq, ← hh, hx, map_zero], fun x hx => hrad x hx⟩`. Conclude with `⟨⟨W, h', hs', hnd', Module.finrank E W, rfl, Module.finBasis E W, fun _ => (0, 0), L', hlat, hun⟩, W.subtype, hrk, fun _ _ => rfl, fun x a => hPI _ x.2.1 _ (Submodule.subset_span ⟨a, rfl⟩)⟩`.
-/
theorem exists_lower (hst : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x)) (V : HSpace E) {i : ℕ} (e : Fin i → V.V)
    (he : LinearIndependent E e) (hiso : ∀ a b, V.hT (e a) (e b) = 0) :
    ∃ (V' : HSpace E) (ι : V'.V →ₗ[E] V.V), V'.rank + 2 * i = V.rank ∧ HSpace.IsIsomEmb V' V ι ∧
      ∀ x a, V.hT (ι x) (e a) = 0 := by
  have hs := V.herm
  have hnd := V.nondeg
  have hfg : V.L0.FG := V.standardTuple_isLattice.fg
  have hsp : Submodule.span E (V.L0 : Set V.V) = ⊤ := V.standardTuple_isLattice.span_eq_top
  have hst1 : ∀ x : E, x ∈ (1 : Submodule (𝓞 E) E) → star x ∈ (1 : Submodule (𝓞 E) E) := by
    intro x hx
    obtain ⟨r, rfl⟩ := Submodule.mem_one.1 hx
    exact Submodule.mem_one.2 ⟨⟨_, hst _ r.2⟩, rfl⟩
  have hL : ∀ x, x ∈ V.L0 ↔ ∀ y ∈ V.L0, V.hT y x ∈ (1 : Submodule (𝓞 E) E) := fun x => by
    rw [← mem_dual, V.baseLattice_isUnimodular]
  set I : Submodule E V.V := Submodule.span E (Set.range e) with hI
  set P : Submodule E V.V := LinearMap.ker (LinearMap.pi fun j => V.hT (e j)) with hPdef
  have hP : ∀ x, x ∈ P ↔ ∀ y ∈ I, V.hT y x = 0 := by
    intro x
    constructor
    · intro hx y hy
      have : I ≤ LinearMap.ker (V.hT.flip x) := by
        rw [hI, Submodule.span_le]
        rintro _ ⟨j, rfl⟩
        exact congrFun hx j
      exact this hy
    · intro hx
      exact funext fun j => hx _ (Submodule.subset_span ⟨j, rfl⟩)
  have hIP : I ≤ P := by
    rw [hI, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact funext fun a => hiso a j
  have hPI : ∀ x ∈ P, ∀ y ∈ I, V.hT x y = 0 := fun x hx y hy => by
    rw [← hs.eq y x, (hP x).1 hx y hy, map_zero]
  obtain ⟨σ, σI, σid, σL⟩ := GlobalTheory.ColPeriodCompare.exists_proj V.L0 hfg hsp I
  obtain ⟨π, πP, πid, πL⟩ := GlobalTheory.ColPeriodCompare.exists_proj V.L0 hfg hsp P
  set W : Submodule E V.V := P ⊓ LinearMap.ker σ with hW
  have hsub : ∀ z ∈ P, z - σ z ∈ W := fun z hz =>
    ⟨P.sub_mem hz (hIP (σI z)), by
      change σ (z - σ z) = 0
      rw [map_sub, σid _ (σI z), sub_self]⟩
  have hsup : I ⊔ W = P := by
    refine le_antisymm (sup_le hIP inf_le_left) fun z hz => ?_
    rw [← add_sub_cancel (σ z) z]
    exact Submodule.add_mem_sup (σI z) (hsub z hz)
  have hinf : I ⊓ W = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨h1, -, h2⟩
    rw [Submodule.mem_bot, ← σid z h1]
    exact h2
  have hrk : Module.finrank E W + 2 * i = V.rank := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq I W
    have h2 := finrank_orth hs hnd e he
    have h3 : Module.finrank E I = i := by rw [hI, finrank_span_eq_card he, Fintype.card_fin]
    rw [hsup, hinf, finrank_bot, h3] at h1
    rw [← hPdef, V.rank_eq] at h2
    omega

  have hWz : ∀ v ∈ W, ∀ z ∈ P, V.hT z v = V.hT (z - σ z) v := fun v hv z hz => by
    rw [map_sub, LinearMap.sub_apply, (hP v).1 hv.1 _ (σI z), sub_zero]
  have hrad : ∀ v : W, (∀ y : W, V.hT y v = 0) → v = 0 := by
    intro v hv
    have : (v : V.V) ∈ I := mem_of_orth hs hnd I v fun x hx => by
      rw [hWz v v.2 x ((hP x).2 hx)]
      exact hv ⟨_, hsub x ((hP x).2 hx)⟩
    have h2 : (v : V.V) ∈ I ⊓ W := ⟨this, v.2⟩
    rw [hinf] at h2
    exact Subtype.ext h2
  have hden : ∀ v : V.V, ∃ d : 𝓞 E, d ≠ 0 ∧ d • v ∈ V.L0 := by
    intro v
    have hv : v ∈ Submodule.span E (V.L0 : Set V.V) := by rw [hsp]; trivial
    obtain ⟨d, hd⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 E)) E (V.L0 : Set V.V) v hv
    rw [Submodule.span_eq] at hd
    exact ⟨d, nonZeroDivisors.coe_ne_zero d, hd⟩
  let h' : W →ₗ⋆[E] W →ₗ[E] E := V.hT.domRestrict₁₂ W W
  have hh : ∀ x y : W, h' x y = V.hT x y := fun _ _ => rfl
  let j : W →ₗ[𝓞 E] V.V := W.subtype.restrictScalars (𝓞 E)
  let L' : Submodule (𝓞 E) W := V.L0.comap j
  have hL' : ∀ x : W, x ∈ L' ↔ (x : V.V) ∈ V.L0 := fun _ => Iff.rfl
  have hlat : Submodule.IsLattice E L' := by
    constructor
    · refine Submodule.fg_of_fg_map_injective j Subtype.val_injective ?_
      have : IsNoetherian (𝓞 E) V.L0 := isNoetherian_of_fg_of_noetherian _ hfg
      have : IsNoetherian (𝓞 E) (L'.map j) := isNoetherian_of_le (Submodule.map_comap_le _ _)
      exact Module.Finite.iff_fg.mp inferInstance
    · rw [eq_top_iff]
      intro v _
      obtain ⟨d, hd, hv⟩ := hden v
      have hd' : algebraMap (𝓞 E) E d ≠ 0 := by simpa using hd
      have : v = (algebraMap (𝓞 E) E d)⁻¹ • (d • v) := by
        rw [← IsScalarTower.algebraMap_smul E d v, smul_smul, inv_mul_cancel₀ hd', one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span hv)
  have hun : Formalism.HermitianLatticesTheory.IsUnimodular h' L' := by
    ext v
    rw [mem_dual]
    refine ⟨fun hv => ?_, fun hv y hy => (hL _).1 hv _ hy⟩
    obtain ⟨w, hw⟩ := exists_repr hnd (V.hT v ∘ₗ π)
    have hw' : ∀ z, V.hT w z = V.hT v (π z) := fun z => LinearMap.congr_fun hw z
    have hwL : w ∈ V.L0 := by
      rw [hL]
      intro y hy
      rw [← hs.eq w y, hw', starRingEnd_apply, ← starRingEnd_apply, hs.eq, hWz v v.2 _ (πP y)]
      exact hv ⟨_, hsub _ (πP y)⟩ (V.L0.sub_mem (πL y hy) (σL _ (πL y hy)))
    have hwv : w - v ∈ I := mem_of_orth hs hnd I _ fun x hx => by
      rw [← hs.eq, map_sub, LinearMap.sub_apply, hw', πid x ((hP x).2 hx), sub_self, map_zero]
    have h1 := σid _ hwv
    rw [map_sub, show σ v = 0 from v.2.2, sub_zero] at h1
    rw [hL', show (v : V.V) = w - σ w by rw [h1]; abel]
    exact V.L0.sub_mem hwL (σL w hwL)
  have hs' : h'.IsSymm := ⟨fun x y => hs.eq _ _⟩
  have hnd' : h'.Nondegenerate := ⟨fun x hx => hrad x fun y => by
    rw [← hs.eq, ← hh, hx, map_zero], fun x hx => hrad x hx⟩
  exact ⟨⟨W, h', hs', hnd', Module.finrank E W, rfl, Module.finBasis E W, fun _ => (0, 0), L', hlat, hun⟩, W.subtype,
    hrk, fun _ _ => rfl, fun x a => hPI _ x.2.1 _ (Submodule.subset_span ⟨a, rfl⟩)⟩

end Lat

variable {D : D7}

/- English proof (translation)
Establish `hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a)` using `D.sp.cm.cmUnram.2.1 τ`. Take `⟨p, q, h⟩` from `Formalism.UG.P.signature_exists _ (V.gram.map τ) (by`. Unfold `Formalism.UG.IsHerm Formalism.UG.cT`. Use extensionality with `a b`. Simplify using `only [Matrix.transpose_apply, Matrix.map_apply, HSpace.gram]`.

Rewrite using `[← hτ]`. Conclude with `congrArg τ (V.herm.eq _ _)) (by`. Rewrite using `[← RingHom.mapMatrix_apply, ← RingHom.map_det, isUnit_iff_ne_zero]`. Conclude with `(map_ne_zero _).2 (Formalism.L2.Theta.gram_det_ne V))`. Conclude with `⟨(p, q), h⟩`.
-/
theorem exists_sig (V : HSp D) (τ : D.host.E →+* ℂ) : ∃ s : ℕ × ℕ, Formalism.UG.HasSignature (V.gram.map τ) s.1 s.2 := by
  have hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a) := D.sp.cm.cmUnram.2.1 τ
  obtain ⟨p, q, h⟩ := Formalism.UG.P.signature_exists _ (V.gram.map τ) (by
    unfold Formalism.UG.IsHerm Formalism.UG.cT
    ext a b
    simp only [Matrix.transpose_apply, Matrix.map_apply, HSpace.gram]
    rw [← hτ]
    exact congrArg τ (V.herm.eq _ _)) (by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, isUnit_iff_ne_zero]
    exact (map_ne_zero _).2 (Formalism.L2.Theta.gram_det_ne V))
  exact ⟨(p, q), h⟩

/- English proof (translation)
Introduce and unpack `D V i ⟨C, hC⟩`. Take `⟨e, rfl⟩` from `GlobalTheory.BesselCompare.eMat_surj V C`. Establish `he : LinearIndependent D.host.E e` using `LinearIndependent.of_comp V.frame.equivFun.toLinearMap hC.1`. Establish `hiso : ∀ a b, V.hT (e a) (e b) = 0` using `fun a b => by`. Rewrite using `[← GlobalTheory.BesselCompare.cT_mul, hC.2]`.

Both sides reduce to the same expression. Take `⟨V', ι, h1, h2, h3⟩` from `exists_lower Examples₂.star_isIntegral V e he hiso`. Use `choose s hs using exists_sig (D := D) V'`. Use `⟨{ V' with sig := s }, ⟨h1, ι, h2, _, hC, ?_⟩, hs⟩` and prove the remaining obligations. Use `Matrix.ext fun a b => ?_` and prove the remaining obligations.

Rewrite using `[GlobalTheory.BesselCompare.frameMat_eq, GlobalTheory.BesselCompare.cT_mul]`. Conclude with `h3 _ _`.
-/
theorem wittLowEx : ∀ D : D7, WittLowEx D := by
  rintro D V i ⟨C, hC⟩
  obtain ⟨e, rfl⟩ := GlobalTheory.BesselCompare.eMat_surj V C
  have he : LinearIndependent D.host.E e :=
    LinearIndependent.of_comp V.frame.equivFun.toLinearMap hC.1
  have hiso : ∀ a b, V.hT (e a) (e b) = 0 := fun a b => by
    rw [← GlobalTheory.BesselCompare.cT_mul, hC.2]; rfl
  obtain ⟨V', ι, h1, h2, h3⟩ := exists_lower Examples₂.star_isIntegral V e he hiso
  choose s hs using exists_sig (D := D) V'
  refine ⟨{ V' with sig := s }, ⟨h1, ι, h2, _, hC, ?_⟩, hs⟩
  refine Matrix.ext fun a b => ?_
  rw [GlobalTheory.BesselCompare.frameMat_eq, GlobalTheory.BesselCompare.cT_mul]
  exact h3 _ _

end GlobalTheory.WittLow

end
