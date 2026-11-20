import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanPeriodLatticeComplexSemiAbelianEqTopStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsToricTorsionCubWeilOne
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Laws3
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyFamilyUnifIffUnifAt
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FibTors

open GlobalTheory.Models GlobalTheory.UU

/- English proof (translation)
Establish `hG' : IsSemiAbelian ((Over.pullback y).obj G)` using `IsSemiAbelian.pullback y G hG`. Use `hG'.smooth` as an intermediate fact. Use `hG'.geomConnected` as an intermediate fact. Establish `: ConnectedSpace ((Over.pullback y).obj G).left` using `GeometricallyConnected.connectedSpace_of_subsingleton ((Over.pullback y).obj G).hom`. Conclude with `exists_dim_of_preconnected _ (((1 : 𝟙_ (Over (Sp ℂ)) ⟶ (Over.pullback y).obj G).left) (default : PrimeSpectrum ℂ))`.
-/
theorem exists_relDim_fibre (X : Scheme.{0}) (G : Over X) [GrpObj G] (hG : IsSemiAbelian G) (y : Sp ℂ ⟶ X) :
    ∃ n, SmoothOfRelativeDimension n ((Over.pullback y).obj G).hom := by
  have hG' : IsSemiAbelian ((Over.pullback y).obj G) := IsSemiAbelian.pullback y G hG
  have := hG'.smooth
  have := hG'.geomConnected
  have : ConnectedSpace ((Over.pullback y).obj G).left :=
    GeometricallyConnected.connectedSpace_of_subsingleton ((Over.pullback y).obj G).hom
  exact exists_dim_of_preconnected _ (((1 : 𝟙_ (Over (Sp ℂ)) ⟶ (Over.pullback y).obj G).left) (default : PrimeSpectrum ℂ))

/- English proof (translation)
Set `G'` to `(Over.pullback y).obj G`. Establish `h0 : e 0 = 1`. Use `hadd 0 0` as an intermediate fact. Rewrite `this` using `[add_zero]`. Conclude with `mul_eq_left.1 this.symm`.

Set `ρ : epsPt y ⟶ Over.mk ((epsR ℂ).hom ≫ y)` to `Over.homMk (𝟙 _) rfl`. Set `T : (epsR ℂ ⟶ G') →* (epsPt y ⟶ G)` to `(ReciprocityTheory.ChartRestriction.G.Geo.Tor.preHom ρ).comp (toBaseHom (toBase_mul_pullback G y) (epsR ℂ))`. Establish `hT : ∀ a, (T a).left = a.left ≫ pullback.fst G.hom y` using `fun a => Category.id_comp _`. Set `U : Over (Sp ℂ)` to `𝟙_ (Over (Sp ℂ))`. Set `ρ0 : Over.mk y ⟶ Over.mk (U.hom ≫ y)` to `Over.homMk (𝟙 _) rfl`.

Set `φ : (U ⟶ G') →* (Over.mk y ⟶ G)` to `(ReciprocityTheory.ChartRestriction.G.Geo.Tor.preHom ρ0).comp (toBaseHom (toBase_mul_pullback G y) U)`. Establish `hη : η[G'].left ≫ pullback.fst G.hom y = (1 : Over.mk y ⟶ G).left`. Establish `h' : (φ 1).left = (1 : U ⟶ G').left ≫ pullback.fst G.hom y` using `Category.id_comp _`. Rewrite `h'` using `[map_one]`. Rewrite using `[h']`.

Use `congr 2`. Establish `hTb : Function.Bijective T`. Use `⟨fun a b h => Over.OverMorphism.ext (pullback.hom_ext ?_ ?_), fun p => ?_⟩` and prove the remaining obligations. Rewrite using `[← hT, ← hT, h]`. Conclude with `(Over.w a).trans (Over.w b).symm`.

Use `⟨Over.homMk (pullback.lift p.left (epsR ℂ).hom (Over.w p)) (pullback.lift_snd _ _ _), Over.OverMorphism.ext ((hT _).trans (pullback.lift_fst _ _ _))⟩` and prove the remaining obligations. Establish `htan : ∀ a : epsR ℂ ⟶ G', IsTangent a ↔ spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ (T a).left = (e 0).left`. Introduce `a`. Rewrite using `[h0, hT, ← hη]`. Use `⟨fun h => by rw [← Category.assoc, h], fun h => pullback.hom_ext ?_ ?_⟩` and prove the remaining obligations.

Rewrite using `[Category.assoc]`. Conclude with `h`. Establish `e1 : a.left ≫ pullback.snd G.hom y = (epsR ℂ).hom` using `Over.w a`. Establish `e2 : η[G'].left ≫ pullback.snd G.hom y = 𝟙 _` using `Over.w η[G']`. Rewrite using `[Category.assoc, e1, e2]`.

Use `show spMap _ ≫ spMap _ = _`. Rewrite using `[GlobalTheory.TanMod.spMap_comp']`. Establish `: (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp (algebraMap ℂ (DualNumber ℂ)) = RingHom.id ℂ` using `RingHom.ext fun _ => rfl`. Rewrite using `[this]`. Conclude with `Spec.map_id _`.

Set `Te` to `MulEquiv.ofBijective T hTb`. Establish `hTe : ∀ a, Te a = T a` using `fun _ => rfl`. Use `choose D hD _ using h1`. Establish `hDmul : ∀ w w', D (w + w') = D w * D w'` using `fun w w' => Over.OverMorphism.ext (GlobalTheory.VerticalDeriv.isDerivAt0_unique (hD (w + w')) (GlobalTheory.UnifCompare.isDerivAt0_mul (congrArg (·.left) h0) (hD w) (hD w')))`. Establish `hDtan : ∀ w, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ (D w).left = (e 0).left` using `fun w => (hD w).1`.

Set `Dl : (Fin g → ℂ) → (epsR ℂ ⟶ G')` to `fun w => Te.symm (D w)`. Establish `hTDl : ∀ w, T (Dl w) = D w` using `fun w => Te.apply_symm_apply (D w)`. Establish `hDl_tan : ∀ w, IsTangent (Dl w)` using `fun w => (htan _).2 (by rw [hTDl]; exact hDtan w)`. Establish `hDl_add : ∀ w w', Dl (w + w') = Dl w * Dl w'` using `fun w w' => by`. Apply `Te.injective` to reduce the goal to its premises.

Rewrite using `[map_mul, hTe, hTe, hTe, hTDl, hTDl, hTDl, hDmul]`. Establish `hDl_zero : Dl 0 = 1`. Use `hDl_add 0 0` as an intermediate fact. Rewrite `this` using `[add_zero]`. Conclude with `mul_eq_left.1 this.symm`.

Establish `hDl_smul : ∀ (c : ℂ) w, (Dl (c • w)).left = spMap (epsScaleR c) ≫ (Dl w).left`. Introduce `c w`. Establish `hov : (spMap (epsScaleR c) ≫ (Dl w).left) ≫ G'.hom = (epsR ℂ).hom`. Rewrite using `[Category.assoc, Over.w (Dl w)]`. Use `show spMap _ ≫ spMap _ = spMap _`.

Rewrite using `[GlobalTheory.TanMod.spMap_comp']`. Apply the tactic sequence `have hc : (epsScaleR c).comp (algebraMap ℂ (DualNumber ℂ)) = algebraMap ℂ (DualNumber ℂ) := RingHom.ext fun a => by ext <;> simp [epsScaleR]`. Rewrite using `[hc]`. Set `a : epsR ℂ ⟶ G'` to `Over.homMk (spMap (epsScaleR c) ≫ (Dl w).left) hov`. Establish `ha : T a = D (c • w)`.

Use `Over.OverMorphism.ext (GlobalTheory.VerticalDeriv.isDerivAt0_unique ?_ (hD (c • w)))` and prove the remaining obligations. Rewrite using `[hT]`. Use `GlobalTheory.UnifCompare.isDerivAt0_smul (hD w) c` as an intermediate fact. Rewrite `this` using `[← hTDl w, hT]`. Use `show IsDerivAt0 _ _ ((spMap (epsScaleR c) ≫ (Dl w).left) ≫ pullback.fst G.hom y)`.

Rewrite using `[Category.assoc]`. Conclude with `this`. Establish `: a = Dl (c • w)`. Apply `Te.injective` to reduce the goal to its premises. Rewrite using `[hTe, hTe, ha, hTDl]`.

Rewrite using `[← this]`. Both sides reduce to the same expression. Establish `hDl_inj : ∀ w w', Dl w = Dl w' → w = w'`. Introduce `w w' h`. Establish `h' : D w = D w'` using `by rw [← hTDl, ← hTDl, h]`.

Conclude with `(h2 (D w) (hDtan w)).unique (hD w) (h' ▸ hD w')`. Establish `hDl_onto : ∀ a, IsTangent a → ∃ w, Dl w = a`. Introduce `a ha`. Take `⟨w, hw, -⟩` from `h2 (T a) ((htan a).1 ha)`. Use `⟨w, Te.injective ?_⟩` and prove the remaining obligations.

Rewrite using `[Te.apply_symm_apply, hTe]`. Conclude with `Over.OverMorphism.ext (GlobalTheory.VerticalDeriv.isDerivAt0_unique (hD w) hw)`. Establish `hsum : ∀ (k : ℕ) (f : Fin k → Fin g → ℂ), Dl (∑ i, f i) = (List.ofFn fun i => Dl (f i)).prod`. Introduce `k`. Proceed by induction on `k with`.

Consider the case `zero => intro f`. Simplify using `[hDl_zero]`. Consider the case `succ k ih`. Introduce `f`. Rewrite using `[Fin.sum_univ_succ, List.ofFn_succ, List.prod_cons, hDl_add, ih]`.

Use `choose ws hws using fun i => hDl_onto (v i) (hv.1 i)`. Establish `hcomb : ∀ c : Fin n → ℂ, IsLieComb c v (Dl (∑ i, c i • ws i))`. Introduce `c`. Use `⟨fun i => Dl (c i • ws i), fun i => ?_, hsum n _⟩` and prove the remaining obligations. Rewrite using `[hDl_smul, hws]`.

Establish `hdet : ∀ (c : Fin n → ℂ) (a a' : epsR ℂ ⟶ G'), IsLieComb c v a → IsLieComb c v a' → a = a'`. Introduce and unpack `c a a' ⟨u, hu, rfl⟩ ⟨u', hu', rfl⟩`. Establish `: u = u'` using `funext fun i => Over.OverMorphism.ext ((hu i).trans (hu' i).symm)`. Rewrite using `[this]`. Establish `hli : LinearIndependent ℂ ws`.

Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `c hc`. Establish `e1` using `hcomb c`. Rewrite `e1` using `[hc]`. Establish `e2` using `hcomb 0`.

Simplify using `only [Pi.zero_apply, zero_smul, Finset.sum_const_zero] at e2`. Use `(hv.2 (Dl 0) (hDl_tan 0)).unique e1 e2` as an intermediate fact. Conclude with `fun i => congrFun this i`. Establish `hsp : ⊤ ≤ Submodule.span ℂ (Set.range ws)`. Introduce `w _`.

Take `⟨c, hc, -⟩` from `hv.2 (Dl w) (hDl_tan w)`. Use `hDl_inj _ _ (hdet c _ _ hc (hcomb c))` as an intermediate fact. Rewrite using `[this]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Establish `hb` using `Module.finrank_eq_card_basis (Module.Basis.mk hli hsp)`.

Simplify using `using hb.symm`.
-/
theorem lieBasis_card (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (y : Sp ℂ ⟶ X) (g n : ℕ)
    (e : (Fin g → ℂ) → (Over.mk y ⟶ G)) (hadd : ∀ z w, e (z + w) = e z * e w)
    (h1 : ∀ w, ∃! v : epsPt y ⟶ G, IsDerivAt0 (fun z => (e z).left) w v.left)
    (h2 : ∀ v : epsPt y ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left →
      ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left)
    (v : Fin n → (epsR ℂ ⟶ (Over.pullback y).obj G)) (hv : IsLieBasis v) : n = g := by
  classical
  let G' := (Over.pullback y).obj G
  have h0 : e 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  let ρ : epsPt y ⟶ Over.mk ((epsR ℂ).hom ≫ y) := Over.homMk (𝟙 _) rfl
  let T : (epsR ℂ ⟶ G') →* (epsPt y ⟶ G) :=
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.preHom ρ).comp (toBaseHom (toBase_mul_pullback G y) (epsR ℂ))
  have hT : ∀ a, (T a).left = a.left ≫ pullback.fst G.hom y := fun a => Category.id_comp _
  let U : Over (Sp ℂ) := 𝟙_ (Over (Sp ℂ))
  let ρ0 : Over.mk y ⟶ Over.mk (U.hom ≫ y) := Over.homMk (𝟙 _) rfl
  let φ : (U ⟶ G') →* (Over.mk y ⟶ G) :=
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.preHom ρ0).comp (toBaseHom (toBase_mul_pullback G y) U)
  have hη : η[G'].left ≫ pullback.fst G.hom y = (1 : Over.mk y ⟶ G).left := by
    have h' : (φ 1).left = (1 : U ⟶ G').left ≫ pullback.fst G.hom y := Category.id_comp _
    rw [map_one] at h'
    rw [h']
    congr 2
  have hTb : Function.Bijective T := by
    refine ⟨fun a b h => Over.OverMorphism.ext (pullback.hom_ext ?_ ?_), fun p => ?_⟩
    · rw [← hT, ← hT, h]
    · exact (Over.w a).trans (Over.w b).symm
    · refine ⟨Over.homMk (pullback.lift p.left (epsR ℂ).hom (Over.w p)) (pullback.lift_snd _ _ _),
        Over.OverMorphism.ext ((hT _).trans (pullback.lift_fst _ _ _))⟩
  have htan : ∀ a : epsR ℂ ⟶ G', IsTangent a ↔
      spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ (T a).left = (e 0).left := by
    intro a
    rw [h0, hT, ← hη]
    refine ⟨fun h => by rw [← Category.assoc, h], fun h => pullback.hom_ext ?_ ?_⟩
    · rw [Category.assoc]; exact h
    · have e1 : a.left ≫ pullback.snd G.hom y = (epsR ℂ).hom := Over.w a
      have e2 : η[G'].left ≫ pullback.snd G.hom y = 𝟙 _ := Over.w η[G']
      rw [Category.assoc, e1, e2]
      show spMap _ ≫ spMap _ = _
      rw [GlobalTheory.TanMod.spMap_comp']
      have : (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp (algebraMap ℂ (DualNumber ℂ)) = RingHom.id ℂ :=
        RingHom.ext fun _ => rfl
      rw [this]
      exact Spec.map_id _
  let Te := MulEquiv.ofBijective T hTb
  have hTe : ∀ a, Te a = T a := fun _ => rfl
  choose D hD _ using h1
  have hDmul : ∀ w w', D (w + w') = D w * D w' := fun w w' =>
    Over.OverMorphism.ext (GlobalTheory.VerticalDeriv.isDerivAt0_unique (hD (w + w'))
      (GlobalTheory.UnifCompare.isDerivAt0_mul (congrArg (·.left) h0) (hD w) (hD w')))
  have hDtan : ∀ w, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ (D w).left = (e 0).left := fun w => (hD w).1
  let Dl : (Fin g → ℂ) → (epsR ℂ ⟶ G') := fun w => Te.symm (D w)
  have hTDl : ∀ w, T (Dl w) = D w := fun w => Te.apply_symm_apply (D w)
  have hDl_tan : ∀ w, IsTangent (Dl w) := fun w => (htan _).2 (by rw [hTDl]; exact hDtan w)
  have hDl_add : ∀ w w', Dl (w + w') = Dl w * Dl w' := fun w w' => by
    apply Te.injective
    rw [map_mul, hTe, hTe, hTe, hTDl, hTDl, hTDl, hDmul]
  have hDl_zero : Dl 0 = 1 := by
    have := hDl_add 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have hDl_smul : ∀ (c : ℂ) w, (Dl (c • w)).left = spMap (epsScaleR c) ≫ (Dl w).left := by
    intro c w
    have hov : (spMap (epsScaleR c) ≫ (Dl w).left) ≫ G'.hom = (epsR ℂ).hom := by
      rw [Category.assoc, Over.w (Dl w)]
      show spMap _ ≫ spMap _ = spMap _
      rw [GlobalTheory.TanMod.spMap_comp']
      have hc : (epsScaleR c).comp (algebraMap ℂ (DualNumber ℂ)) = algebraMap ℂ (DualNumber ℂ) :=
        RingHom.ext fun a => by ext <;> simp [epsScaleR]
      rw [hc]
    let a : epsR ℂ ⟶ G' := Over.homMk (spMap (epsScaleR c) ≫ (Dl w).left) hov
    have ha : T a = D (c • w) := by
      refine Over.OverMorphism.ext (GlobalTheory.VerticalDeriv.isDerivAt0_unique ?_ (hD (c • w)))
      rw [hT]
      have := GlobalTheory.UnifCompare.isDerivAt0_smul (hD w) c
      rw [← hTDl w, hT] at this
      show IsDerivAt0 _ _ ((spMap (epsScaleR c) ≫ (Dl w).left) ≫ pullback.fst G.hom y)
      rw [Category.assoc]
      exact this
    have : a = Dl (c • w) := by
      apply Te.injective
      rw [hTe, hTe, ha, hTDl]
    rw [← this]
    rfl
  have hDl_inj : ∀ w w', Dl w = Dl w' → w = w' := by
    intro w w' h
    have h' : D w = D w' := by rw [← hTDl, ← hTDl, h]
    exact (h2 (D w) (hDtan w)).unique (hD w) (h' ▸ hD w')
  have hDl_onto : ∀ a, IsTangent a → ∃ w, Dl w = a := by
    intro a ha
    obtain ⟨w, hw, -⟩ := h2 (T a) ((htan a).1 ha)
    refine ⟨w, Te.injective ?_⟩
    rw [Te.apply_symm_apply, hTe]
    exact Over.OverMorphism.ext (GlobalTheory.VerticalDeriv.isDerivAt0_unique (hD w) hw)
  have hsum : ∀ (k : ℕ) (f : Fin k → Fin g → ℂ), Dl (∑ i, f i) = (List.ofFn fun i => Dl (f i)).prod := by
    intro k
    induction k with
    | zero => intro f; simp [hDl_zero]
    | succ k ih =>
      intro f
      rw [Fin.sum_univ_succ, List.ofFn_succ, List.prod_cons, hDl_add, ih]
  choose ws hws using fun i => hDl_onto (v i) (hv.1 i)
  have hcomb : ∀ c : Fin n → ℂ, IsLieComb c v (Dl (∑ i, c i • ws i)) := by
    intro c
    refine ⟨fun i => Dl (c i • ws i), fun i => ?_, hsum n _⟩
    rw [hDl_smul, hws]
  have hdet : ∀ (c : Fin n → ℂ) (a a' : epsR ℂ ⟶ G'), IsLieComb c v a → IsLieComb c v a' → a = a' := by
    rintro c a a' ⟨u, hu, rfl⟩ ⟨u', hu', rfl⟩
    have : u = u' := funext fun i => Over.OverMorphism.ext ((hu i).trans (hu' i).symm)
    rw [this]
  have hli : LinearIndependent ℂ ws := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have e1 := hcomb c
    rw [hc] at e1
    have e2 := hcomb 0
    simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero] at e2
    have := (hv.2 (Dl 0) (hDl_tan 0)).unique e1 e2
    exact fun i => congrFun this i
  have hsp : ⊤ ≤ Submodule.span ℂ (Set.range ws) := by
    intro w _
    obtain ⟨c, hc, -⟩ := hv.2 (Dl w) (hDl_tan w)
    have := hDl_inj _ _ (hdet c _ _ hc (hcomb c))
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hb := Module.finrank_eq_card_basis (Module.Basis.mk hli hsp)
  simpa using hb.symm

end GlobalTheory.FibTors

open GlobalTheory.FibTors GlobalTheory.Models GlobalTheory.UU in

/- English proof (translation)
Introduce `E _ _ _ H X t y g N e hN hexp _ _`. Take `⟨hadd, hd1, hd2⟩` from `hexp`. Establish `h0 : e 0 = 1`. Use `hadd 0 0` as an intermediate fact. Rewrite `this` using `[add_zero]`.

Conclude with `mul_eq_left.1 this.symm`. Establish `h1 : ∀ w, ∃! v : epsPt y ⟶ t.G, IsDerivAt0 (fun z => (e z).left) w v.left`. Introduce `w`. Take `⟨v, ⟨hv1, hv2⟩, hu⟩` from `hd1 w`. Use `⟨Over.homMk v hv1.1, hv2, fun v' hv' => Over.OverMorphism.ext (hu v'.left ⟨⟨Over.w v', ?_⟩, hv'⟩)⟩` and prove the remaining obligations.

Use `hv'.1.trans ?_` and prove the remaining obligations. Use `show (e 0).left = _`. Rewrite using `[h0]`. Establish `h2 : ∀ v : epsPt y ⟶ t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left → ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left`. Introduce `v hv`.

Conclude with `hd2 v.left ⟨Over.w v, by rw [hv, h0]⟩`. Take `⟨n, hn⟩` from `exists_relDim_fibre X t.G t.semi y`. Take `⟨v, hv⟩` from `GlobalTheory.KeyPow.exists_isLieBasis _ hn`. Establish `hng` using `lieBasis_card X t.G y g n e hadd h1 h2 v hv`. Substitute `hng` using the available equality.

Establish `hN' : (N : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 hN.ne'`. Set `G : Over X` to `t.G`. Set `x` to `y`. Set `k` to `ℂ`. Establish `h3` using `GlobalTheory.laws3`.

Set `G' : Over (Sp k)` to `(Over.pullback x).obj G`. Establish `hp : IsGrpPullback G' G x (pullback.fst G.hom x)` using `isGrpPullback_pullback G x`. Establish `hG' : IsSemiAbelian G'` using `IsSemiAbelian.pullback x G t.semi`. Use `hG'.comm` as an intermediate fact. Use `hG'.smooth` as an intermediate fact.

Use `hG'.geomConnected` as an intermediate fact. Establish `dG' : SmoothOfRelativeDimension n G'.hom` using `hn`. Take `⟨E⟩` from `t.semi.fibres k x`. Set `` to `E.addCommGroup`. Set `` to `E.grpB`.

Use `E.free` as an intermediate fact. Use `E.finite` as an intermediate fact. Use `E.i_hom` as an intermediate fact. Take `⟨hL, hr, ⟨c', hc'⟩, -⟩` from `h3.cubePull _ _ G G' (cubeMapOf hp) t.PP t.cub`. Take `⟨σ⟩` from `GlobalTheory.BiextTriv.main k E.X G' _ c' E.i E.i_hom`.

Establish `hw : pullback.fst G.hom x ≫ G.hom = G'.hom ≫ x` using `pullback.condition`. Set `U : Over (Sp k)` to `𝟙_ (Over (Sp k))`. Set `ρ : Over.mk x ⟶ Over.mk (U.hom ≫ x)` to `Over.homMk (𝟙 _) rfl`. Set `φ : (U ⟶ G') →* (Over.mk x ⟶ G)` to `(ReciprocityTheory.ChartRestriction.G.Geo.Tor.preHom ρ).comp (toBaseHom (toBase_mul_pullback G x) U)`. Establish `hφ : ∀ a : U ⟶ G', (φ a).left = a.left ≫ pullback.fst G.hom x` using `fun a => Category.id_comp _`.

Establish `hb : Function.Bijective φ`. Use `⟨fun a b h => Over.OverMorphism.ext (pullback.hom_ext ?_ ?_), fun p => ?_⟩` and prove the remaining obligations. Rewrite using `[← hφ, ← hφ, h]`. Conclude with `(Over.w a).trans (Over.w b).symm`. Use `⟨Over.homMk (pullback.lift p.left (𝟙 _) ((Over.w p).trans (Category.id_comp _).symm)) (pullback.lift_snd _ _ _), Over.OverMorphism.ext ((hφ _).trans (pullback.lift_fst _ _ _))⟩` and prove the remaining obligations.

Set `e'` to `MulEquiv.ofBijective φ hb`. Establish `he : ∀ a : U ⟶ G', e' a ^ N = 1 ↔ a ^ N = 1` using `fun a => by rw [← map_pow, e'.map_eq_one_iff]`. Establish `hcount` using `GlobalTheory.card_torsion_mul_card_toric_torsion k G' E n N hG' dG' hN'`. Use `⟨e' '' {y | y ^ N = 1 ∧ ∃ t, y = t ≫ E.i}, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨a, ⟨ha, -⟩, rfl⟩`.

Conclude with `(he a).2 ha`. Introduce and unpack `_ ⟨_, ⟨ha, s0, rfl⟩, rfl⟩ y hy`. Take `⟨b, rfl⟩` from `e'.surjective y`. Establish `ht : s0 ^ N = 1` using `E.isKernel.hom_ext (by rw [MonObj.pow_comp, ha, MonObj.one_comp]) (toUnit_unique _ _)`. Establish `h1` using `σ.cubWeil ht ((he b).1 hy)`.

Establish `h2` using `(GlobalTheory.UU.cubWeil_of_isPullCubical _ _ x G G' (cubeMapOf hp) hw (toBase_mul_pullback G x) t.PP _ t.cub c' hc' N U _ _ _ h1).comp ρ`. Rewrite `h2` using `[map_one]`. Conclude with `h2`. Rewrite using `[← hcount]`. Use `congr 1`.

Conclude with `(Nat.card_congr (e'.toEquiv.subtypeEquiv fun a => (he a).symm)).symm`. Conclude with `Nat.card_image_of_injective e'.injective _`.
-/
theorem GlobalTheory.exists_toric_torsion_cubWeil_one_of_exp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (y : Sp ℂ ⟶ X) (g N : ℕ) (e : (Fin g → ℂ) → (Over.mk y ⟶ t.G)), 0 < N → IsExpAt t y e → Function.Surjective e → IsHolTo Set.univ (fun w => (e w).left) → ∃ T : Set (Over.mk y ⟶ t.G), (∀ τ ∈ T, τ ^ N = 1) ∧ (∀ τ ∈ T, ∀ x : Over.mk y ⟶ t.G, x ^ N = 1 → GlobalTheory.UU.CubWeil t.cub N τ x 1) ∧ Nat.card {p : Over.mk y ⟶ t.G // p ^ N = 1} * Nat.card T = N ^ (2 * g) := by
  intro E _ _ _ H X t y g N e hN hexp _ _
  obtain ⟨hadd, hd1, hd2⟩ := hexp
  have h0 : e 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have h1 : ∀ w, ∃! v : epsPt y ⟶ t.G, IsDerivAt0 (fun z => (e z).left) w v.left := by
    intro w
    obtain ⟨v, ⟨hv1, hv2⟩, hu⟩ := hd1 w
    refine ⟨Over.homMk v hv1.1, hv2, fun v' hv' => Over.OverMorphism.ext (hu v'.left ⟨⟨Over.w v', ?_⟩, hv'⟩)⟩
    refine hv'.1.trans ?_
    show (e 0).left = _
    rw [h0]
  have h2 : ∀ v : epsPt y ⟶ t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left →
      ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left := by
    intro v hv
    exact hd2 v.left ⟨Over.w v, by rw [hv, h0]⟩
  obtain ⟨n, hn⟩ := exists_relDim_fibre X t.G t.semi y
  obtain ⟨v, hv⟩ := GlobalTheory.KeyPow.exists_isLieBasis _ hn
  have hng := lieBasis_card X t.G y g n e hadd h1 h2 v hv
  subst hng
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  let G : Over X := t.G
  let x := y
  let k := ℂ
  have h3 := GlobalTheory.laws3
  let G' : Over (Sp k) := (Over.pullback x).obj G
  have hp : IsGrpPullback G' G x (pullback.fst G.hom x) := isGrpPullback_pullback G x
  have hG' : IsSemiAbelian G' := IsSemiAbelian.pullback x G t.semi
  have := hG'.comm
  have := hG'.smooth
  have := hG'.geomConnected
  have dG' : SmoothOfRelativeDimension n G'.hom := hn
  obtain ⟨E⟩ := t.semi.fibres k x
  let := E.addCommGroup
  let := E.grpB
  have := E.free
  have := E.finite
  have := E.i_hom
  obtain ⟨hL, hr, ⟨c', hc'⟩, -⟩ := h3.cubePull _ _ G G' (cubeMapOf hp) t.PP t.cub
  obtain ⟨σ⟩ := GlobalTheory.BiextTriv.main k E.X G' _ c' E.i E.i_hom
  have hw : pullback.fst G.hom x ≫ G.hom = G'.hom ≫ x := pullback.condition
  let U : Over (Sp k) := 𝟙_ (Over (Sp k))
  let ρ : Over.mk x ⟶ Over.mk (U.hom ≫ x) := Over.homMk (𝟙 _) rfl
  let φ : (U ⟶ G') →* (Over.mk x ⟶ G) := (ReciprocityTheory.ChartRestriction.G.Geo.Tor.preHom ρ).comp (toBaseHom (toBase_mul_pullback G x) U)
  have hφ : ∀ a : U ⟶ G', (φ a).left = a.left ≫ pullback.fst G.hom x := fun a => Category.id_comp _
  have hb : Function.Bijective φ := by
    refine ⟨fun a b h => Over.OverMorphism.ext (pullback.hom_ext ?_ ?_), fun p => ?_⟩
    · rw [← hφ, ← hφ, h]
    · exact (Over.w a).trans (Over.w b).symm
    · refine ⟨Over.homMk (pullback.lift p.left (𝟙 _) ((Over.w p).trans (Category.id_comp _).symm))
        (pullback.lift_snd _ _ _), Over.OverMorphism.ext ((hφ _).trans (pullback.lift_fst _ _ _))⟩
  let e' := MulEquiv.ofBijective φ hb
  have he : ∀ a : U ⟶ G', e' a ^ N = 1 ↔ a ^ N = 1 := fun a => by rw [← map_pow, e'.map_eq_one_iff]
  have hcount := GlobalTheory.card_torsion_mul_card_toric_torsion k G' E n N hG' dG' hN'
  refine ⟨e' '' {y | y ^ N = 1 ∧ ∃ t, y = t ≫ E.i}, ?_, ?_, ?_⟩
  · rintro _ ⟨a, ⟨ha, -⟩, rfl⟩
    exact (he a).2 ha
  · rintro _ ⟨_, ⟨ha, s0, rfl⟩, rfl⟩ y hy
    obtain ⟨b, rfl⟩ := e'.surjective y
    have ht : s0 ^ N = 1 := E.isKernel.hom_ext
      (by rw [MonObj.pow_comp, ha, MonObj.one_comp]) (toUnit_unique _ _)
    have h1 := σ.cubWeil ht ((he b).1 hy)
    have h2 := (GlobalTheory.UU.cubWeil_of_isPullCubical _ _ x G G' (cubeMapOf hp) hw (toBase_mul_pullback G x) t.PP _ t.cub c' hc' N U _ _ _ h1).comp ρ
    rw [map_one] at h2
    exact h2
  · rw [← hcount]
    congr 1
    · exact (Nat.card_congr (e'.toEquiv.subtypeEquiv fun a => (he a).symm)).symm
    · exact Nat.card_image_of_injective e'.injective _
