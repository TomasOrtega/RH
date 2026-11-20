import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachNCokernelKilledByPowerStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineExtensionIntegralCocycleAllPlacesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.T2SpaceLocLatV
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteClassesSubsetAdmissibleOfGoodO
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoboundaryIffIsCrys
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitVectorOfUnitFor
import Formalism.SharpRestriction.LevelLetterCocycles.FrobeniusPowUniformizerFactorisation
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

noncomputable section

namespace GlobalTheory.NL.ExtClassKs

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

/- English proof (translation)
Set `Yt : LocLat G Qp LL O` to `GlobalTheory.FiniteAdm.extLat hinj T zc`. Set `ι : LatHom T.L Yt.L` to `{ f := LinearMap.inl LL T.V LL equiv := fun g x => by`. Express the relevant statement in the definitionally equal form `((T.ρ g x, 0) : T.V × LL) = (T.ρ g x + (0 : LL) • (zc : G → T.V) g, 0)`. Simplify using the standard rewrite rules. Use `cont := by`.

Express the relevant statement in the definitionally equal form `Continuous fun x : T.V => ((x, 0) : T.V × LL)`. Conclude with `continuous_id.prodMk continuous_const`. Use `T_le := fun x hx => ⟨hx, 0, map_zero _⟩ }`. Use `haveI : ContinuousSMul LL Z.V := IsModuleTopology.toContinuousSMul LL Z.V`. Set `π : LatHom Yt.L Z.L` to `{ f := (LinearMap.toSpanSingleton LL Z.V (e₀ : Z.V)).comp (LinearMap.snd LL T.V LL) equiv := fun g x => by`.

Rewrite using `[htriv]`. Both sides reduce to the same expression. Use `cont := by`. Express the relevant statement in the definitionally equal form `Continuous fun x : T.V × LL => x.2 • (e₀ : Z.V)`. Conclude with `continuous_snd.smul continuous_const`.

Use `T_le := by`. Introduce and unpack `⟨v, a⟩ ⟨-, o, rfl⟩`. Express the relevant statement in the definitionally equal form `(algebraMap O LL o) • (e₀ : Z.V) ∈ Z.L.T`. Rewrite using `[algebraMap_smul]`. Conclude with `Z.L.T.smul_mem o e₀.2 }`.

Use `⟨Yt, ι, π, ⟨((0 : T.V), (1 : LL)), Submodule.zero_mem _, 1, map_one (algebraMap O LL)⟩, ⟨LinearMap.inl_injective, ?_, ?_, ?_, ?_⟩, one_smul LL (e₀ : Z.V), ?_, ?_⟩` and prove the remaining obligations. Introduce `w`. Establish `hw : w ∈ Submodule.span LL {(e₀ : Z.V)}`. Rewrite using `[← Submodule.span_span_of_tower O, ← hone, Z.L.span]`. Discharge the goal by the elementary cases of `trivial`.

Take `⟨a, rfl⟩` from `Submodule.mem_span_singleton.1 hw`. Conclude with `⟨((0 : T.V), a), rfl⟩`. Introduce `w hw`. Rewrite `hw` using `[hone]`. Take `⟨o, rfl⟩` from `Submodule.mem_span_singleton.1 hw`.

Conclude with `⟨((0 : T.V), algebraMap O LL o), ⟨Submodule.zero_mem _, o, rfl⟩, algebraMap_smul LL o (e₀ : Z.V)⟩`. Introduce and unpack `⟨w, a⟩`. Prove the components needed by the constructor for the conclusion. Introduce `h0`. Establish `ha : a = 0` using `(smul_eq_zero.1 (show a • (e₀ : Z.V) = 0 from h0)).resolve_right he₀`.

Conclude with `⟨w, Prod.ext rfl ha.symm⟩`. Introduce and unpack `⟨y, hy⟩`. Rewrite using `[← hy]`. Conclude with `zero_smul LL (e₀ : Z.V)`. Introduce `y hy`.

Conclude with `hy.1`. Express the relevant statement in the definitionally equal form `Module.finrank LL (T.V × LL) = _`. Rewrite using `[Module.finrank_prod, Module.finrank_self]`. Introduce `g`. Express the relevant statement in the definitionally equal form `(((zc : G → T.V) g, 0) : T.V × LL) = ((T.ρ g 0 + (1 : LL) • (zc : G → T.V) g - 0, 1 - 1) : T.V × LL)`.

Simplify using the standard rewrite rules.
-/
theorem exists_ext [IsTopologicalRing LL] (hinj : Function.Injective (algebraMap O LL))
    (T Z : LocLat G Qp LL O) (htriv : ∀ g x, Z.ρ g x = x) (e₀ : ↥Z.L.T) (he₀ : (e₀ : Z.V) ≠ 0)
    (hone : Z.L.T = Submodule.span O {(e₀ : Z.V)}) (zc : ↥(latticeCocycles T.L)) :
    ∃ (Y : LocLat G Qp LL O) (ι : LatHom T.L Y.L) (π : LatHom Y.L Z.L) (et : ↥Y.L.T),
      IsSESLat (Qp := Qp) ι π ∧ π.f et = e₀ ∧ Module.finrank LL Y.V = Module.finrank LL T.V + 1 ∧
        ∀ g, ι.f ((zc : G → T.V) g) = Y.ρ g et - et := by
  let Yt : LocLat G Qp LL O := GlobalTheory.FiniteAdm.extLat hinj T zc
  let ι : LatHom T.L Yt.L :=
    { f := LinearMap.inl LL T.V LL
      equiv := fun g x => by
        change ((T.ρ g x, 0) : T.V × LL) = (T.ρ g x + (0 : LL) • (zc : G → T.V) g, 0)
        simp
      cont := by
        change Continuous fun x : T.V => ((x, 0) : T.V × LL)
        exact continuous_id.prodMk continuous_const
      T_le := fun x hx => ⟨hx, 0, map_zero _⟩ }
  haveI : ContinuousSMul LL Z.V := IsModuleTopology.toContinuousSMul LL Z.V
  let π : LatHom Yt.L Z.L :=
    { f := (LinearMap.toSpanSingleton LL Z.V (e₀ : Z.V)).comp (LinearMap.snd LL T.V LL)
      equiv := fun g x => by
        rw [htriv]
        rfl
      cont := by
        change Continuous fun x : T.V × LL => x.2 • (e₀ : Z.V)
        exact continuous_snd.smul continuous_const
      T_le := by
        rintro ⟨v, a⟩ ⟨-, o, rfl⟩
        change (algebraMap O LL o) • (e₀ : Z.V) ∈ Z.L.T
        rw [algebraMap_smul]
        exact Z.L.T.smul_mem o e₀.2 }
  refine ⟨Yt, ι, π, ⟨((0 : T.V), (1 : LL)), Submodule.zero_mem _, 1, map_one (algebraMap O LL)⟩,
    ⟨LinearMap.inl_injective, ?_, ?_, ?_, ?_⟩, one_smul LL (e₀ : Z.V), ?_, ?_⟩
  · intro w
    have hw : w ∈ Submodule.span LL {(e₀ : Z.V)} := by
      rw [← Submodule.span_span_of_tower O, ← hone, Z.L.span]; trivial
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hw
    exact ⟨((0 : T.V), a), rfl⟩
  · intro w hw
    rw [hone] at hw
    obtain ⟨o, rfl⟩ := Submodule.mem_span_singleton.1 hw
    exact ⟨((0 : T.V), algebraMap O LL o), ⟨Submodule.zero_mem _, o, rfl⟩,
      algebraMap_smul LL o (e₀ : Z.V)⟩
  · rintro ⟨w, a⟩
    constructor
    · intro h0
      have ha : a = 0 := (smul_eq_zero.1 (show a • (e₀ : Z.V) = 0 from h0)).resolve_right he₀
      exact ⟨w, Prod.ext rfl ha.symm⟩
    · rintro ⟨y, hy⟩
      rw [← hy]
      exact zero_smul LL (e₀ : Z.V)
  · intro y hy
    exact hy.1
  · change Module.finrank LL (T.V × LL) = _
    rw [Module.finrank_prod, Module.finrank_self]
  · intro g
    change (((zc : G → T.V) g, 0) : T.V × LL) =
      ((T.ρ g 0 + (1 : LL) • (zc : G → T.V) g - 0, 1 - 1) : T.V × LL)
    simp

variable {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}

/- English proof (translation)
Take `⟨c₀, hc₀, rfl⟩` from `hκ`. Take `⟨xB, hxB⟩ : ∃ x : T.V ⊗[Qp] B, ∀ g : ↥W.GKs, (c₀ : ↥W.GKs → T.V) g ⊗ₜ[Qp] (1 : B) = actVB PD T.ρ (g : G) x - x` from `hc₀.2.2`. Establish `hmem : ∀ g, g ∈ W.GKs` using `fun g => by rw [hGKs]; exact Subgroup.mem_top g`. Establish `hz1 : (fun g => (c₀ : ↥W.GKs → T.V) ⟨g, hmem g⟩) ∈ latticeCocycles T.L` using `⟨⟨c₀.2.1.1.comp (Continuous.subtype_mk continuous_id hmem), fun g g' => c₀.2.1.2 ⟨g, hmem g⟩ ⟨g', hmem g'⟩⟩, fun g _ => c₀.2.2 ⟨g, hmem g⟩ (Set.mem_univ _)⟩`. Take `⟨e, e₀, hspan, hje, hN⟩` from `E.one_e`.

Establish `hone : W.one.L.T = Submodule.span O {(e₀ : W.one.V)}`. Establish `h1` using `congrArg (Submodule.map W.one.L.T.subtype) hspan`. Rewrite `h1` using `[Submodule.map_span, Submodule.map_top, Submodule.range_subtype, Set.image_singleton]`. Conclude with `h1.symm`. Establish `he₀ : (e₀ : W.one.V) ≠ 0`.

Introduce `h0`. Take `⟨e', he', hsp⟩` from `W.one_line`. Establish `: e' ∈ W.one.L.T` using `by rw [hsp]; exact Submodule.mem_span_singleton_self e'`. Rewrite `this` using `[hone, h0, Submodule.span_singleton_eq_bot.2 rfl]`. Conclude with `he' ((Submodule.mem_bot _).1 this)`.

Establish `hφe : W.φD W.one e = e`. Apply `E.jD_inj` to reduce the goal to its premises. Rewrite using `[E.jD_φ, hje]`. Simplify using `[TWmap]`. Establish `hγe : ∀ g, W.γD W.one g e = e`.

Introduce `g`. Take `⟨g, rfl⟩` from `W.resΓ_onto g`. Apply `E.jD_inj` to reduce the goal to its premises. Establish `h1 : W.one.actT g e₀ = e₀` using `Subtype.ext (W.one_triv g _)`. Rewrite using `[E.jD_act, hje]`.

Simplify using `[TWact, h1]`. Establish `heN : e ∈ W.N W.one` using `by rw [hN]; exact Submodule.mem_span_singleton_self e`. Take `⟨Y, ι, π, et, hS, hπ, hrk, hc⟩` from `exists_ext hinj T W.one W.one_triv e₀ he₀ hone ⟨_, hz1⟩`. Establish `hY : IsCrys PD Y.ρ` using `hBK Y ι.f ι.equiv hS.1 hrk et (fun hx => he₀ (by rw [← hπ]; exact (hS.2.2.2.1 _).2 hx)) _ hc ⟨xB, fun g => hxB ⟨g, hmem g⟩⟩`. Take `⟨k, hk⟩` from `hlift Y ι π hY hS`.

Take `⟨x, hxN, hxπ⟩` from `hk e heN`. Establish `hxπ' : W.map π x = ((p : O) ^ k) • e`. Rewrite using `[hxπ, ← algebraMap_smul (LetA O n) ((p : O) ^ k) e, map_pow, map_natCast]`. Take `⟨⟨y, hy, hyι⟩, ⟨z, hz, hzι⟩⟩` from `hint Y ι π hS hY e heN hφe hγe x hxN _ hxπ'`. Establish `hιinj : Function.Injective (W.map ι)`.

Introduce `a b hab`. Apply `E.jD_inj T` to reduce the goal to its premises. Apply `GlobalTheory.Cyc.DictKs.lTensor_inj hS RW` to reduce the goal to its premises. Establish `h1` using `congrArg (E.jD Y) hab`. Rewrite `h1` using `[E.jD_map, E.jD_map]`.

Conclude with `h1`. Establish `key : W.map ι ((W.γD T W.gam y - y) - (W.φD T z - z)) = W.map ι 0`. Rewrite using `[map_zero, map_sub, map_sub, map_sub, W.map_γ, W.map_φ, hyι, hzι, LocWach.γ, map_sub, map_sub, W.φγ_comm]`. Normalize the expressions using the abelian group laws. Establish `hyz : (y, z) ∈ W.divisibleCocycles T`.

Establish `h0` using `hιinj key`. Rewrite `h0` using `[sub_eq_add_neg]`. Conclude with `h0`. Use `⟨k, y, z, hyz, hy, hz, ?_⟩` and prove the remaining obligations. Use `(GlobalTheory.Cyc.DictKs.generic E hR hdense T Y W.one ι π hS (((p : O) ^ k) • et) (((p : O) ^ k) • e₀) x (by` and prove the remaining obligations.

Rewrite using `[Submodule.coe_smul, Submodule.coe_smul, ← hπ, ← algebraMap_smul LL ((p : O) ^ k) (et : Y.V), map_smul, algebraMap_smul])`. Use the proof step `(by rw [hxπ', map_smul, hje, TensorProduct.tmul_smul]) ⟨(y, z), hyz⟩ hyι hzι (((p : O) ^ k) • c₀)`. Use the proof step `(fun g => by`. Establish `h1` using `hc g`. Express the relevant statement in the definitionally equal form `ι.f ((c₀ : ↥W.GKs → T.V) g) = _ at h1`.

Express the relevant statement in the definitionally equal form `ι.f (((p : O) ^ k) • (c₀ : ↥W.GKs → T.V) g) = _`. Rewrite using `[Submodule.coe_smul, ← algebraMap_smul LL ((p : O) ^ k) (et : Y.V), ← algebraMap_smul LL ((p : O) ^ k) ((c₀ : ↥W.GKs → T.V) g), map_smul, map_smul, h1, smul_sub])).trans ?_`. Rewrite using `[Submodule.Quotient.mk_smul, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]`. Both sides reduce to the same expression.
-/
theorem generic [T2Space LL] [IsTopologicalRing LL] (E : EtTie W RA RW inclR φR gR πA)
    (hinj : Function.Injective (algebraMap O LL)) (hR : Function.Injective (algebraMap O RW))
    (hdense : ∀ M : Submonoid ↥W.GKs, IsClosed (M : Set ↥W.GKs) →
      (∀ g : ↥W.GKs, W.resΓ (g : G) = 1 → g ∈ M) → (∀ g : ↥W.GKs, W.resΓ (g : G) = W.gam → g ∈ M) →
      ∀ g, g ∈ M)
    (T : LocLat G Qp LL O) (hGKs : W.GKs = ⊤) (M p : ℕ)
    (hBK : ∀ (Y : LocLat G Qp LL O) (ι : T.V →ₗ[LL] Y.V), (∀ g x, ι (T.ρ g x) = Y.ρ g (ι x)) →
      Function.Injective ι → Module.finrank LL Y.V = Module.finrank LL T.V + 1 →
      ∀ x : Y.V, x ∉ LinearMap.range ι → ∀ c : G → T.V, (∀ g, ι (c g) = Y.ρ g x - x) →
      (∃ y : T.V ⊗[Qp] B, ∀ g, c g ⊗ₜ[Qp] (1 : B) = actVB PD T.ρ g y - y) → IsCrys PD Y.ρ)
    (hlift : ∀ (Y : LocLat G Qp LL O) (ι : LatHom T.L Y.L) (π : LatHom Y.L W.one.L), IsCrys PD Y.ρ →
      IsSESLat (Qp := Qp) ι π →
      ∃ c : ℕ, ∀ z ∈ W.N W.one, ∃ y ∈ W.N Y, W.map π y = (p : LetA O n) ^ c • z)
    (hint : p8 W T M) (κ : LatticeCohomology (resLat T W.GKs)) (hκ : κ ∈ H1fIntegralCyclotomicLayer W T) :
    ∃ (c : ℕ) (y z : W.DD T) (hyz : (y, z) ∈ W.divisibleCocycles T), y ∈ invN W T (W.Q ^ M) ∧ z ∈ aN W T W.X ∧
      W.cl T ⟨(y, z), hyz⟩ = (p ^ c : ℕ) • κ := by
  obtain ⟨c₀, hc₀, rfl⟩ := hκ
  obtain ⟨xB, hxB⟩ : ∃ x : T.V ⊗[Qp] B, ∀ g : ↥W.GKs,
      (c₀ : ↥W.GKs → T.V) g ⊗ₜ[Qp] (1 : B) = actVB PD T.ρ (g : G) x - x := hc₀.2.2
  have hmem : ∀ g, g ∈ W.GKs := fun g => by rw [hGKs]; exact Subgroup.mem_top g
  have hz1 : (fun g => (c₀ : ↥W.GKs → T.V) ⟨g, hmem g⟩) ∈ latticeCocycles T.L :=
    ⟨⟨c₀.2.1.1.comp (Continuous.subtype_mk continuous_id hmem),
      fun g g' => c₀.2.1.2 ⟨g, hmem g⟩ ⟨g', hmem g'⟩⟩, fun g _ => c₀.2.2 ⟨g, hmem g⟩ (Set.mem_univ _)⟩
  obtain ⟨e, e₀, hspan, hje, hN⟩ := E.one_e
  have hone : W.one.L.T = Submodule.span O {(e₀ : W.one.V)} := by
    have h1 := congrArg (Submodule.map W.one.L.T.subtype) hspan
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, Set.image_singleton] at h1
    exact h1.symm
  have he₀ : (e₀ : W.one.V) ≠ 0 := by
    intro h0
    obtain ⟨e', he', hsp⟩ := W.one_line
    have : e' ∈ W.one.L.T := by rw [hsp]; exact Submodule.mem_span_singleton_self e'
    rw [hone, h0, Submodule.span_singleton_eq_bot.2 rfl] at this
    exact he' ((Submodule.mem_bot _).1 this)
  have hφe : W.φD W.one e = e := by
    apply E.jD_inj
    rw [E.jD_φ, hje]
    simp [TWmap]
  have hγe : ∀ g, W.γD W.one g e = e := by
    intro g
    obtain ⟨g, rfl⟩ := W.resΓ_onto g
    apply E.jD_inj
    have h1 : W.one.actT g e₀ = e₀ := Subtype.ext (W.one_triv g _)
    rw [E.jD_act, hje]
    simp [TWact, h1]
  have heN : e ∈ W.N W.one := by rw [hN]; exact Submodule.mem_span_singleton_self e
  obtain ⟨Y, ι, π, et, hS, hπ, hrk, hc⟩ := exists_ext hinj T W.one W.one_triv e₀ he₀ hone ⟨_, hz1⟩
  have hY : IsCrys PD Y.ρ := hBK Y ι.f ι.equiv hS.1 hrk et
    (fun hx => he₀ (by rw [← hπ]; exact (hS.2.2.2.1 _).2 hx)) _ hc ⟨xB, fun g => hxB ⟨g, hmem g⟩⟩
  obtain ⟨k, hk⟩ := hlift Y ι π hY hS
  obtain ⟨x, hxN, hxπ⟩ := hk e heN
  have hxπ' : W.map π x = ((p : O) ^ k) • e := by
    rw [hxπ, ← algebraMap_smul (LetA O n) ((p : O) ^ k) e, map_pow, map_natCast]
  obtain ⟨⟨y, hy, hyι⟩, ⟨z, hz, hzι⟩⟩ := hint Y ι π hS hY e heN hφe hγe x hxN _ hxπ'
  have hιinj : Function.Injective (W.map ι) := by
    intro a b hab
    apply E.jD_inj T
    apply GlobalTheory.Cyc.DictKs.lTensor_inj hS RW
    have h1 := congrArg (E.jD Y) hab
    rw [E.jD_map, E.jD_map] at h1
    exact h1
  have key : W.map ι ((W.γD T W.gam y - y) - (W.φD T z - z)) = W.map ι 0 := by
    rw [map_zero, map_sub, map_sub, map_sub, W.map_γ, W.map_φ, hyι, hzι, LocWach.γ, map_sub, map_sub,
      W.φγ_comm]
    abel
  have hyz : (y, z) ∈ W.divisibleCocycles T := by
    have h0 := hιinj key
    rw [sub_eq_add_neg] at h0
    exact h0
  refine ⟨k, y, z, hyz, hy, hz, ?_⟩
  refine (GlobalTheory.Cyc.DictKs.generic E hR hdense T Y W.one ι π hS (((p : O) ^ k) • et) (((p : O) ^ k) • e₀) x
    (by
      rw [Submodule.coe_smul, Submodule.coe_smul, ← hπ, ← algebraMap_smul LL ((p : O) ^ k) (et : Y.V),
        map_smul, algebraMap_smul])
    (by rw [hxπ', map_smul, hje, TensorProduct.tmul_smul]) ⟨(y, z), hyz⟩ hyι hzι (((p : O) ^ k) • c₀)
    (fun g => by
      have h1 := hc g
      change ι.f ((c₀ : ↥W.GKs → T.V) g) = _ at h1
      change ι.f (((p : O) ^ k) • (c₀ : ↥W.GKs → T.V) g) = _
      rw [Submodule.coe_smul, ← algebraMap_smul LL ((p : O) ^ k) (et : Y.V),
        ← algebraMap_smul LL ((p : O) ^ k) ((c₀ : ↥W.GKs → T.V) g), map_smul, map_smul, h1, smul_sub])).trans ?_
  rw [Submodule.Quotient.mk_smul, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  rfl

end Generic

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Introduce `D HW F Cm l _ K s LL h W E C T hT hGKs M hh hJ κ hκ`. Use `haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2`. Use `generic E (fun a b hab => Subtype.ext hab) (GlobalTheory.Cyc.DictKs.algebraMap_RW_inj LL) (GlobalTheory.Cyc.DictKs.dense_gen (D.loc l) (D.locA l) K s LL h _ ((HW l).W_s K s LL h)) T hGKs (mx M) l ?_ ?_ (GlobalTheory.T.p8_of_cmpOf D HW F Cm l K s LL h T M hh hT hJ) κ hκ` and prove the remaining obligations. Introduce `Y ι h1 h2 h3 x h4 c h5`. Conclude with `(GlobalTheory.CrysExtCrit.coboundary_iff_isCrys l (D.loc l) (D.locA l) (D.locT l) K LL T.V T.ρ Y.V Y.ρ ι h1 h2 h3 hT x h4 c h5).1`.

Introduce `Y ι π hY hS`. Conclude with `(GlobalTheory.T.wachN_cokernel_killed_by_power D HW F Cm l K s LL h T Y _ ι π hT hY (Formalism.MainNotions.LiftingTheory.gen_one_crys _) hS).imp fun c hc z hz => (hc z hz).1`.
-/
theorem main : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → W.GKs = ⊤ → ∀ (M hh : Let K → ℕ), JumpsLet W T M hh → ∀ κ ∈ H1fIntegralCyclotomicLayer W T, ∃ (c : ℕ) (y z : W.DD T) (hyz : (y, z) ∈ W.divisibleCocycles T), y ∈ invN W T (W.Q ^ mx M) ∧ z ∈ aN W T W.X ∧ W.cl T ⟨(y, z), hyz⟩ = (l ^ c : ℕ) • κ := by
  intro D HW F Cm l _ K s LL h W E C T hT hGKs M hh hJ κ hκ
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  refine generic E (fun a b hab => Subtype.ext hab) (GlobalTheory.Cyc.DictKs.algebraMap_RW_inj LL)
    (GlobalTheory.Cyc.DictKs.dense_gen (D.loc l) (D.locA l) K s LL h _ ((HW l).W_s K s LL h)) T hGKs (mx M) l
    ?_ ?_ (GlobalTheory.T.p8_of_cmpOf D HW F Cm l K s LL h T M hh hT hJ) κ hκ
  · intro Y ι h1 h2 h3 x h4 c h5
    exact (GlobalTheory.CrysExtCrit.coboundary_iff_isCrys l (D.loc l) (D.locA l) (D.locT l) K LL T.V T.ρ Y.V Y.ρ ι
      h1 h2 h3 hT x h4 c h5).1
  · intro Y ι π hY hS
    exact (GlobalTheory.T.wachN_cokernel_killed_by_power D HW F Cm l K s LL h T Y _ ι π hT hY (Formalism.MainNotions.LiftingTheory.gen_one_crys _) hS).imp
      fun c hc z hz => (hc z hz).1

end GlobalTheory.NL.ExtClassKs
