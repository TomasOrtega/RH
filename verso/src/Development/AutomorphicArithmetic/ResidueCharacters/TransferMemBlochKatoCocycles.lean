import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictionCorestrictionH1f
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations TensorProduct

noncomputable section

namespace UpperTheory.N.CorD

variable {G G' : Type} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G']
    {Qp LL O : Type} [Field Qp] [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL]
    {K₀ K K₀' K' : Type} [Field K₀] [Field K] [Field K₀'] [Field K']
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    [Algebra Qp K₀'] [Algebra Qp K'] [Algebra K₀' K'] [IsScalarTower Qp K₀' K']
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    [Algebra K₀' B] [IsScalarTower Qp K₀' B] [Algebra K₀' BdR] [Algebra K' BdR]
    [IsScalarTower Qp K' BdR] [IsScalarTower K₀' K' BdR] [IsScalarTower Qp K₀' BdR]

open GlobalTheory.InducedSectionsSpanStatement

/- English proof (translation)
Establish `hinj : Function.Injective ι` using `he.injective`. Establish `hinv : ∀ a : G, Function.invFun ι (ι a) = a` using `fun a => Function.leftInverse_invFun hinj a`. Establish `hmem` using `GlobalTheory.transfer_cocycle_formula LL G' T.V T.ρ ι.range`. Take `⟨hzc, x, hx⟩` from `hz`. Take `⟨hzcont, hzcoc⟩` from `hzc`.

Use `set f : G' → T.V := fun h => z (Function.invFun ι h) with hf`. Establish `htr : ∀ g, trCochain ι T z g = ∑ q : G' ⧸ ι.range, T.ρ (Quotient.out (g • q)) (f ((Quotient.out (g • q))⁻¹ * g * Quotient.out q))`. Introduce `g`. Rewrite using `[trCochain_apply]`. Use `⟨⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations.

Use `haveI : IsTopologicalAddGroup T.V := { continuous_neg := by`. Use `continuous_const_smul (-1 : LL) (T := T.V)` as an intermediate fact. Simplify using `using this }`. Establish `hρc : ∀ g : G', Continuous (T.ρ g)` using `fun g => IsModuleTopology.continuous_of_linearMap (R := LL) (T.ρ g)`. Establish `hfc : ContinuousOn f (ι.range : Set G')`.

Rewrite using `[continuousOn_iff_continuous_restrict]`. Use `(hzcont.comp (he.toHomeomorph).symm.continuous).congr ?_` and prove the remaining obligations. Introduce and unpack `⟨h, a, rfl⟩`. Simplify using `only [Function.comp_apply, hf, hinv]`. Use `congr 1`.

Establish `hc` using `GlobalTheory.transfer_continuous_of_continuousOn LL G' T.V T.ρ ι.range ho hρc f hfc`. Establish `hfun : (trCochain ι T z : G' → T.V) = fun g => ∑ q : G' ⧸ ι.range, T.ρ (Quotient.out (g • q)) (f ((Quotient.out (g • q))⁻¹ * g * Quotient.out q))` using `funext htr`. Rewrite using `[hfun]`. Conclude with `hc`. Introduce `a b`.

Rewrite using `[htr, htr, htr]`. Use `hmem.2.1 f ?_ a b` and prove the remaining obligations. Introduce and unpack `_ ⟨a', rfl⟩ _ ⟨b', rfl⟩`. Simplify using `only [hf, ← map_mul, hinv]`. Conclude with `hzcoc a' b'`.

Establish `hW` using `GlobalTheory.transfer_cocycle_formula LL G' (T.V ⊗[Qp] B) (repVB PD' T) ι.range`. Use `⟨∑ q : G' ⧸ ι.range, repVB PD' T (Quotient.out q) x, fun g => ?_⟩` and prove the remaining obligations. Establish `key` using `hW.2.2.1 (fun h => f h ⊗ₜ[Qp] (1 : B)) x (by`. Introduce and unpack `_ ⟨a, rfl⟩`. Simplify using `only [hf, hinv]`.

Rewrite using `[hx a, actVB_res PD PD' ι hι hact T a x]`. Use the proof step `rfl) g`. Simplify using `only at key`. Rewrite using `[htr, TensorProduct.sum_tmul]`. Establish `hstep : ∀ (h : G') (v : T.V), (T.ρ h v) ⊗ₜ[Qp] (1 : B) = repVB PD' T h (v ⊗ₜ[Qp] 1)`.

Introduce `h v`. Conclude with `(actVB_tmul_one PD' T h v).symm`. Simplify using `only [hstep]`. Rewrite using `[key]`. Both sides reduce to the same expression.
-/
theorem transfer_mem_blochKato_cocycles [IsTopologicalGroup G'] (PD : PeriodData G Qp K₀ K B BdR) (PD' : PeriodData G' Qp K₀' K' B BdR)
    (ι : G →* G') (hι : Continuous ι) (he : Topology.IsEmbedding ι) (ho : IsOpen (ι.range : Set G'))
    [Fintype (G' ⧸ ι.range)] (hact : ∀ g b, PD.actB g b = PD'.actB (ι g) b) (T : LocLat G' Qp LL O)
    (z : G → T.V) (hz : z ∈ finiteCocycles PD (LiftingTheory.resLoc ι hι T).ρ) : trCochain ι T z ∈ finiteCocycles PD' T.ρ := by
  have hinj : Function.Injective ι := he.injective
  have hinv : ∀ a : G, Function.invFun ι (ι a) = a := fun a => Function.leftInverse_invFun hinj a
  have hmem := GlobalTheory.transfer_cocycle_formula LL G' T.V T.ρ ι.range
  obtain ⟨hzc, x, hx⟩ := hz
  obtain ⟨hzcont, hzcoc⟩ := hzc
  set f : G' → T.V := fun h => z (Function.invFun ι h) with hf
  have htr : ∀ g, trCochain ι T z g =
      ∑ q : G' ⧸ ι.range, T.ρ (Quotient.out (g • q)) (f ((Quotient.out (g • q))⁻¹ * g * Quotient.out q)) := by
    intro g
    rw [trCochain_apply]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · haveI : IsTopologicalAddGroup T.V :=
      { continuous_neg := by
          have := continuous_const_smul (-1 : LL) (T := T.V)
          simpa using this }
    have hρc : ∀ g : G', Continuous (T.ρ g) := fun g =>
      IsModuleTopology.continuous_of_linearMap (R := LL) (T.ρ g)
    have hfc : ContinuousOn f (ι.range : Set G') := by
      rw [continuousOn_iff_continuous_restrict]
      refine (hzcont.comp (he.toHomeomorph).symm.continuous).congr ?_
      rintro ⟨h, a, rfl⟩
      simp only [Function.comp_apply, hf, hinv]
      congr 1
    have hc := GlobalTheory.transfer_continuous_of_continuousOn LL G' T.V T.ρ ι.range ho hρc f hfc
    have hfun : (trCochain ι T z : G' → T.V) = fun g => ∑ q : G' ⧸ ι.range,
        T.ρ (Quotient.out (g • q)) (f ((Quotient.out (g • q))⁻¹ * g * Quotient.out q)) := funext htr
    rw [hfun]
    exact hc
  · intro a b
    rw [htr, htr, htr]
    refine hmem.2.1 f ?_ a b
    rintro _ ⟨a', rfl⟩ _ ⟨b', rfl⟩
    simp only [hf, ← map_mul, hinv]
    exact hzcoc a' b'
  · have hW := GlobalTheory.transfer_cocycle_formula LL G' (T.V ⊗[Qp] B) (repVB PD' T) ι.range
    refine ⟨∑ q : G' ⧸ ι.range, repVB PD' T (Quotient.out q) x, fun g => ?_⟩
    have key := hW.2.2.1 (fun h => f h ⊗ₜ[Qp] (1 : B)) x (by
      rintro _ ⟨a, rfl⟩
      simp only [hf, hinv]
      rw [hx a, actVB_res PD PD' ι hι hact T a x]
      rfl) g
    simp only at key
    rw [htr, TensorProduct.sum_tmul]
    have hstep : ∀ (h : G') (v : T.V), (T.ρ h v) ⊗ₜ[Qp] (1 : B) = repVB PD' T h (v ⊗ₜ[Qp] 1) := by
      intro h v
      exact (actVB_tmul_one PD' T h v).symm
    simp only [hstep]
    rw [key]
    rfl

/- English proof (translation)
Use `haveI : Fintype (G' ⧸ ι.range) := Subgroup.fintypeQuotientOfFiniteIndex`. Establish `hinj : Function.Injective ι` using `he.injective`. Establish `hinv : ∀ a : G, Function.invFun ι (ι a) = a` using `fun a => Function.leftInverse_invFun hinj a`. Take `⟨y, hy, bb, hbb, hsum⟩` from `Submodule.mem_sup.mp hres`. Take `⟨z, hz, rfl⟩` from `hy`.

Take `⟨w, rfl⟩` from `hbb`. Establish `hzf : z ∈ finiteCocycles PD (LiftingTheory.resLoc ι hι T).ρ` using `hz`. Establish `htrz` using `transfer_mem_blochKato_cocycles PD PD' ι hι he ho hact T z hzf`. Establish `hD` using `GlobalTheory.transfer_cocycle_formula O G' (T.V ⧸ T.L.T) (repD T.L) ι.range`. Use `set S' : T.V ⧸ T.L.T := ∑ q : G' ⧸ ι.range, c (Quotient.out q) with hS'`.

Use `set S : T.V ⧸ T.L.T := ∑ q : G' ⧸ ι.range, repD T.L (Quotient.out q) w with hS`. Establish `hcsplit : ∀ a : G, c (ι a) = T.L.T.mkQ (z a) + (actD T.L (ι a) w - w)`. Introduce `a`. Use `congrFun hsum a` as an intermediate fact. Rewrite using `[← this]`.

Both sides reduce to the same expression. Establish `h4` using `hD.2.2.2 c (fun a b => hc a b)`. Establish `h3` using `hD.2.2.1 (fun h => actD T.L h w - w) w (fun h _ => rfl)`. Establish `hkey : ∀ g : G', ((ι.range.index : ℕ) : O) • c g = T.L.T.mkQ (trCochain ι T z g) + (repD T.L g (S - S') - (S - S'))`. Introduce `g`.

Establish `h4g` using `h4 g`. Establish `h3g` using `h3 g`. Simplify using `only at h4g h3g`. Establish `e1 : (∑ q : G' ⧸ ι.range, repD T.L (Quotient.out (g • q)) (c ((Quotient.out (g • q))⁻¹ * g * Quotient.out q))) = T.L.T.mkQ (trCochain ι T z g) + ∑ q : G' ⧸ ι.range, repD T.L (Quotient.out (g • q)) (actD T.L ((Quotient.out (g • q))⁻¹ * g * Quotient.out q) w - w)`. Rewrite using `[trCochain_apply, map_sum, ← Finset.sum_add_distrib]`.

Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Take `⟨a, ha⟩` from `MonoidHom.mem_range.mp (hD.1 g q)`. Rewrite using `[← ha, hcsplit a, hinv, map_add]`. Both sides reduce to the same expression. Rewrite using `[Nat.cast_smul_eq_nsmul]`.

Establish `hh : ι.range.index • c g = (∑ q : G' ⧸ ι.range, repD T.L (Quotient.out (g • q)) (c ((Quotient.out (g • q))⁻¹ * g * Quotient.out q))) - (repD T.L g S' - S')`. Rewrite using `[h4g]`. Normalize the expressions using the abelian group laws. Rewrite using `[hh, e1, h3g, map_sub]`. Normalize the expressions using the abelian group laws.

Use `Submodule.mem_sup.mpr ⟨T.L.T.mkQ.compLeft G' (trCochain ι T z), ⟨_, htrz, rfl⟩, fun g => repD T.L g (S - S') - (S - S'), ⟨S - S', rfl⟩, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `g`. Rewrite using `[Pi.add_apply, Pi.smul_apply, hkey g]`. Both sides reduce to the same expression.
-/
theorem index_smul_mem [IsTopologicalGroup G'] (PD : PeriodData G Qp K₀ K B BdR) (PD' : PeriodData G' Qp K₀' K' B BdR)
    (ι : G →* G') (hι : Continuous ι) (he : Topology.IsEmbedding ι) (ho : IsOpen (ι.range : Set G'))
    [ι.range.FiniteIndex] (hact : ∀ g b, PD.actB g b = PD'.actB (ι g) b) (T : LocLat G' Qp LL O)
    (c : G' → T.V ⧸ T.L.T) (hc : ∀ a b, c (a * b) = c a + actD T.L a (c b))
    (hres : (fun g => c (ι g)) ∈ HfD PD (LiftingTheory.resLoc ι hι T).L) :
    ((ι.range.index : ℕ) : O) • c ∈ HfD PD' T.L := by
  haveI : Fintype (G' ⧸ ι.range) := Subgroup.fintypeQuotientOfFiniteIndex
  have hinj : Function.Injective ι := he.injective
  have hinv : ∀ a : G, Function.invFun ι (ι a) = a := fun a => Function.leftInverse_invFun hinj a
  obtain ⟨y, hy, bb, hbb, hsum⟩ := Submodule.mem_sup.mp hres
  obtain ⟨z, hz, rfl⟩ := hy
  obtain ⟨w, rfl⟩ := hbb
  have hzf : z ∈ finiteCocycles PD (LiftingTheory.resLoc ι hι T).ρ := hz
  have htrz := transfer_mem_blochKato_cocycles PD PD' ι hι he ho hact T z hzf
  have hD := GlobalTheory.transfer_cocycle_formula O G' (T.V ⧸ T.L.T) (repD T.L) ι.range
  set S' : T.V ⧸ T.L.T := ∑ q : G' ⧸ ι.range, c (Quotient.out q) with hS'
  set S : T.V ⧸ T.L.T := ∑ q : G' ⧸ ι.range, repD T.L (Quotient.out q) w with hS
  have hcsplit : ∀ a : G, c (ι a) = T.L.T.mkQ (z a) + (actD T.L (ι a) w - w) := by
    intro a
    have := congrFun hsum a
    rw [← this]
    rfl
  have h4 := hD.2.2.2 c (fun a b => hc a b)
  have h3 := hD.2.2.1 (fun h => actD T.L h w - w) w (fun h _ => rfl)
  have hkey : ∀ g : G', ((ι.range.index : ℕ) : O) • c g =
      T.L.T.mkQ (trCochain ι T z g) + (repD T.L g (S - S') - (S - S')) := by
    intro g
    have h4g := h4 g
    have h3g := h3 g
    dsimp only at h4g h3g
    have e1 : (∑ q : G' ⧸ ι.range, repD T.L (Quotient.out (g • q))
        (c ((Quotient.out (g • q))⁻¹ * g * Quotient.out q))) =
        T.L.T.mkQ (trCochain ι T z g) + ∑ q : G' ⧸ ι.range, repD T.L (Quotient.out (g • q))
          (actD T.L ((Quotient.out (g • q))⁻¹ * g * Quotient.out q) w - w) := by
      rw [trCochain_apply, map_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun q _ => ?_
      obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp (hD.1 g q)
      rw [← ha, hcsplit a, hinv, map_add]
      rfl
    rw [Nat.cast_smul_eq_nsmul]
    have hh : ι.range.index • c g = (∑ q : G' ⧸ ι.range, repD T.L (Quotient.out (g • q))
        (c ((Quotient.out (g • q))⁻¹ * g * Quotient.out q))) - (repD T.L g S' - S') := by
      rw [h4g]
      abel
    rw [hh, e1, h3g, map_sub]
    abel
  refine Submodule.mem_sup.mpr ⟨T.L.T.mkQ.compLeft G' (trCochain ι T z), ⟨_, htrz, rfl⟩,
    fun g => repD T.L g (S - S') - (S - S'), ⟨S - S', rfl⟩, ?_⟩
  funext g
  rw [Pi.add_apply, Pi.smul_apply, hkey g]
  rfl

end UpperTheory.N.CorD

end
