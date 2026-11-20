import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinsumOutOfLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousBlkOneVal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComapUNAndMapSM
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HintEqOfLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsBlocksOfUpper
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumParabolicQuotientFubini
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviProjectionMaximalCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarIntegralNormalizedIntegralMatricesTwoSidedMu
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportTwistedConstantTermSplitPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockUpperTimesUnipotentMulBlockDiagonal

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcN.F2
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.IntDec

section Generic

variable {G : Type} [Group G]

/- English proof (translation)
Take `⟨⟨y, hy⟩, hy'⟩` from `QuotientGroup.mk_out_eq_mul S g`. Rewrite using `[hy']`. Conclude with `hu hy g`.
-/
theorem out_inv {S : Subgroup G} {u : G → ℂ} (hu : S ≤ rStab u) (g : G) :
    u (QuotientGroup.mk g : G ⧸ S).out = u g := by
  obtain ⟨⟨y, hy⟩, hy'⟩ := QuotientGroup.mk_out_eq_mul S g
  rw [hy']
  exact hu hy g

/- English proof (translation)
Establish `hm' : Nat.card (K ⧸ S.subgroupOf K) ≠ 0` using `hfin`. Use `haveI : Finite (K ⧸ S.subgroupOf K) := Nat.finite_of_card_ne_zero hm'`. Set `e` to `Subgroup.quotientEquivProdOfLE hSK`. Establish `hfst : ∀ q : G ⧸ S, (e q).1 = (QuotientGroup.mk q.out : G ⧸ K)`. Introduce `q`.

Take `⟨g, rfl⟩` from `QuotientGroup.mk_surjective q`. Establish `h1 : (e (g : G ⧸ S)).1 = (g : G ⧸ K)` using `rfl`. Rewrite using `[h1]`. Conclude with `QuotientGroup.eq.2 (hSK (QuotientGroup.eq.1 (QuotientGroup.out_eq' (g : G ⧸ S)).symm))`. Use `((hA.prod (Set.finite_univ (α := K ⧸ S.subgroupOf K))).preimage e.injective.injOn).subset ?_` and prove the remaining obligations.

Introduce `q hq`. Conclude with `⟨⟨q, hq, (hfst q).symm⟩, Set.mem_univ _⟩`.
-/
theorem finite_of_image {S K : Subgroup G} (hSK : S ≤ K) (hfin : S.relIndex K ≠ 0) (A : Set (G ⧸ S))
    (hA : ((fun q : G ⧸ S => (QuotientGroup.mk q.out : G ⧸ K)) '' A).Finite) : A.Finite := by
  have hm' : Nat.card (K ⧸ S.subgroupOf K) ≠ 0 := hfin
  haveI : Finite (K ⧸ S.subgroupOf K) := Nat.finite_of_card_ne_zero hm'
  let e := Subgroup.quotientEquivProdOfLE hSK
  have hfst : ∀ q : G ⧸ S, (e q).1 = (QuotientGroup.mk q.out : G ⧸ K) := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    have h1 : (e (g : G ⧸ S)).1 = (g : G ⧸ K) := rfl
    rw [h1]
    exact QuotientGroup.eq.2 (hSK (QuotientGroup.eq.1 (QuotientGroup.out_eq' (g : G ⧸ S)).symm))
  refine ((hA.prod (Set.finite_univ (α := K ⧸ S.subgroupOf K))).preimage e.injective.injOn).subset ?_
  intro q hq
  exact ⟨⟨q, hq, (hfst q).symm⟩, Set.mem_univ _⟩

/- English proof (translation)
Set `f : X → K ⧸ K'.subgroupOf K` to `fun x => QuotientGroup.mk ⟨x.1, hX x.1 x.2⟩`. Establish `hf : Function.Bijective f`. Prove the components needed by the constructor for the conclusion. Introduce `x x' hxx`. Establish `h1 : (x.1)⁻¹ * x'.1 ∈ K'`.

Use `QuotientGroup.eq.1 hxx` as an intermediate fact. Simplify `this` using `[Subgroup.mem_subgroupOf]`. Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `(hu x'.1 (hX _ x'.2)).unique ⟨x.2, h1⟩ ⟨x'.2, by simp [K'.one_mem]⟩`. Introduce `q`.

Take `⟨⟨k, hk⟩, rfl⟩` from `QuotientGroup.mk_surjective q`. Take `⟨x, ⟨hx, hxk⟩, -⟩` from `hu k hk`. Use `⟨⟨x, hx⟩, QuotientGroup.eq.2 ?_⟩` and prove the remaining obligations. Simplify `hxk` using `[Subgroup.mem_subgroupOf]`. Use `show Nat.card (K ⧸ K'.subgroupOf K) = X.card`.

Rewrite using `[← Nat.card_congr (Equiv.ofBijective f hf)]`. Simplify using the standard rewrite rules.
-/
theorem relIndex_eq_card {K K' : Subgroup G} (X : Finset G) (hX : ∀ x ∈ X, x ∈ K)
    (hu : ∀ k ∈ K, ∃! x ∈ X, x⁻¹ * k ∈ K') : K'.relIndex K = X.card := by
  let f : X → K ⧸ K'.subgroupOf K := fun x => QuotientGroup.mk ⟨x.1, hX x.1 x.2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x x' hxx
      have h1 : (x.1)⁻¹ * x'.1 ∈ K' := by
        have := QuotientGroup.eq.1 hxx
        simpa [Subgroup.mem_subgroupOf] using this
      apply Subtype.ext
      exact (hu x'.1 (hX _ x'.2)).unique ⟨x.2, h1⟩ ⟨x'.2, by simp [K'.one_mem]⟩
    · intro q
      obtain ⟨⟨k, hk⟩, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨x, ⟨hx, hxk⟩, -⟩ := hu k hk
      refine ⟨⟨x, hx⟩, QuotientGroup.eq.2 ?_⟩
      simpa [Subgroup.mem_subgroupOf] using hxk
  show Nat.card (K ⧸ K'.subgroupOf K) = X.card
  rw [← Nat.card_congr (Equiv.ofBijective f hf)]
  simp

/- English proof (translation)
Establish `hex : ∀ y : X, ∃ x : X, x.1⁻¹ * (k * y.1) ∈ K'` using `fun y => by`. Take `⟨x, ⟨hx, hxk⟩, -⟩` from `hu (k * y.1) (K.mul_mem hk (hX _ y.2))`. Conclude with `⟨⟨x, hx⟩, hxk⟩`. Use `choose σ hσ using hex`. Establish `hinj : Function.Injective σ`.

Introduce `y y' hyy`. Establish `h1` using `hσ y`. Establish `h2` using `hσ y'`. Rewrite `h2` using `[← hyy]`. Establish `h3 : (y.1)⁻¹ * y'.1 ∈ K'`.

Establish `h4` using `K'.mul_mem (K'.inv_mem h1) h2`. Establish `e : ((σ y).1⁻¹ * (k * y.1))⁻¹ * ((σ y).1⁻¹ * (k * y'.1)) = (y.1)⁻¹ * y'.1` using `by group`. Rewrite `h4` using `[e]`. Then use the resulting hypothesis. Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `(hu y'.1 (hX _ y'.2)).unique ⟨y.2, h3⟩ ⟨y'.2, by simp [K'.one_mem]⟩`.

Establish `hbij : Function.Bijective σ` using `Finite.injective_iff_bijective.1 hinj`. Establish `hterm : ∀ y : X, φ (g * k * y.1) = φ (g * (σ y).1)`. Introduce `y`. Establish `e : g * k * y.1 = g * (σ y).1 * ((σ y).1⁻¹ * (k * y.1))` using `by group`. Rewrite using `[e]`.

Conclude with `hφ (hσ y) _`. Rewrite using `[← Finset.sum_coe_sort X (fun y => φ (g * k * y)), ← Finset.sum_coe_sort X (fun y => φ (g * y))]`. Rewrite using `[Finset.sum_congr rfl fun y _ => hterm y]`. Conclude with `hbij.sum_comp (fun x : X => φ (g * x.1))`.
-/
theorem sum_mul_mem {K K' : Subgroup G} (X : Finset G) (hX : ∀ x ∈ X, x ∈ K)
    (hu : ∀ k ∈ K, ∃! x ∈ X, x⁻¹ * k ∈ K') (φ : G → ℂ) (hφ : K' ≤ rStab φ) (g k : G) (hk : k ∈ K) :
    ∑ y ∈ X, φ (g * k * y) = ∑ y ∈ X, φ (g * y) := by
  have hex : ∀ y : X, ∃ x : X, x.1⁻¹ * (k * y.1) ∈ K' := fun y => by
    obtain ⟨x, ⟨hx, hxk⟩, -⟩ := hu (k * y.1) (K.mul_mem hk (hX _ y.2))
    exact ⟨⟨x, hx⟩, hxk⟩
  choose σ hσ using hex
  have hinj : Function.Injective σ := by
    intro y y' hyy
    have h1 := hσ y
    have h2 := hσ y'
    rw [← hyy] at h2
    have h3 : (y.1)⁻¹ * y'.1 ∈ K' := by
      have h4 := K'.mul_mem (K'.inv_mem h1) h2
      have e : ((σ y).1⁻¹ * (k * y.1))⁻¹ * ((σ y).1⁻¹ * (k * y'.1)) = (y.1)⁻¹ * y'.1 := by group
      rwa [e] at h4
    apply Subtype.ext
    exact (hu y'.1 (hX _ y'.2)).unique ⟨y.2, h3⟩ ⟨y'.2, by simp [K'.one_mem]⟩
  have hbij : Function.Bijective σ := Finite.injective_iff_bijective.1 hinj
  have hterm : ∀ y : X, φ (g * k * y.1) = φ (g * (σ y).1) := by
    intro y
    have e : g * k * y.1 = g * (σ y).1 * ((σ y).1⁻¹ * (k * y.1)) := by group
    rw [e]
    exact hφ (hσ y) _
  rw [← Finset.sum_coe_sort X (fun y => φ (g * k * y)), ← Finset.sum_coe_sort X (fun y => φ (g * y))]
  rw [Finset.sum_congr rfl fun y _ => hterm y]
  exact hbij.sum_comp (fun x : X => φ (g * x.1))

/- English proof (translation)
Set `e : (G ⧸ K) × X → G ⧸ K'` to `fun py => QuotientGroup.mk (py.1.out * py.2.1)`. Establish `he : Function.Bijective e`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨p, y⟩ ⟨p', y'⟩ hpp`. Establish `h1 : (p.out * y.1)⁻¹ * (p'.out * y'.1) ∈ K'` using `QuotientGroup.eq.1 hpp`.

Establish `h2 : p.out⁻¹ * p'.out ∈ K`. Establish `h3` using `K.mul_mem (K.mul_mem (hX _ y.2) (hle h1)) (K.inv_mem (hX _ y'.2))`. Establish `e2 : y.1 * ((p.out * y.1)⁻¹ * (p'.out * y'.1)) * y'.1⁻¹ = p.out⁻¹ * p'.out` using `by group`. Rewrite `h3` using `[e2]`. Then use the resulting hypothesis. Establish `hp : p = p'`.

Rewrite using `[← QuotientGroup.out_eq' p, ← QuotientGroup.out_eq' p']`. Conclude with `QuotientGroup.eq.2 h2`. Substitute `hp` using the available equality. Establish `h3 : y.1⁻¹ * y'.1 ∈ K'`. Establish `e2 : (p.out * y.1)⁻¹ * (p.out * y'.1) = y.1⁻¹ * y'.1` using `by group`.

Rewrite `h1` using `[e2]`. Then use the resulting hypothesis. Establish `hy : y = y'` using `Subtype.ext ((hu y'.1 (hX _ y'.2)).unique ⟨y.2, h3⟩ ⟨y'.2, by simp [K'.one_mem]⟩)`. Rewrite using `[hy]`. Introduce `q`. Take `⟨g, rfl⟩` from `QuotientGroup.mk_surjective q`.

Establish `hk : (QuotientGroup.mk g : G ⧸ K).out⁻¹ * g ∈ K` using `QuotientGroup.eq.1 (QuotientGroup.out_eq' (QuotientGroup.mk g : G ⧸ K))`. Take `⟨x, ⟨hx, hxk⟩, -⟩` from `hu _ hk`. Use `⟨((QuotientGroup.mk g : G ⧸ K), ⟨x, hx⟩), QuotientGroup.eq.2 ?_⟩` and prove the remaining obligations. Establish `e2 : ((QuotientGroup.mk g : G ⧸ K).out * x)⁻¹ * g = x⁻¹ * ((QuotientGroup.mk g : G ⧸ K).out⁻¹ * g)` using `by group`. Rewrite using `[e2]` and apply the resulting hypothesis.

Establish `hterm : ∀ py, φ (e py).out = φ (py.1.out * py.2.1)` using `fun py => out_inv hφ _`. Establish `hsupp : (Function.support fun py : (G ⧸ K) × X => φ (py.1.out * py.2.1)).Finite`. Use `(hfin.preimage he.1.injOn).subset fun py hpy => ?_` and prove the remaining obligations. Use `show φ (e py).out ≠ 0`. Rewrite using `[hterm]`.

Conclude with `hpy`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[finsum_eq_sum_of_fintype, Finset.sum_coe_sort X (fun y => φ (p.out * y))]`.
-/
theorem finsum_fibre {K K' : Subgroup G} (hle : K' ≤ K) (X : Finset G) (hX : ∀ x ∈ X, x ∈ K)
    (hu : ∀ k ∈ K, ∃! x ∈ X, x⁻¹ * k ∈ K') (φ : G → ℂ) (hφ : K' ≤ rStab φ)
    (hfin : {q : G ⧸ K' | φ q.out ≠ 0}.Finite) :
    ∑ᶠ q : G ⧸ K', φ q.out = ∑ᶠ p : G ⧸ K, ∑ y ∈ X, φ (p.out * y) := by
  let e : (G ⧸ K) × X → G ⧸ K' := fun py => QuotientGroup.mk (py.1.out * py.2.1)
  have he : Function.Bijective e := by
    constructor
    · rintro ⟨p, y⟩ ⟨p', y'⟩ hpp
      have h1 : (p.out * y.1)⁻¹ * (p'.out * y'.1) ∈ K' := QuotientGroup.eq.1 hpp
      have h2 : p.out⁻¹ * p'.out ∈ K := by
        have h3 := K.mul_mem (K.mul_mem (hX _ y.2) (hle h1)) (K.inv_mem (hX _ y'.2))
        have e2 : y.1 * ((p.out * y.1)⁻¹ * (p'.out * y'.1)) * y'.1⁻¹ = p.out⁻¹ * p'.out := by group
        rwa [e2] at h3
      have hp : p = p' := by
        rw [← QuotientGroup.out_eq' p, ← QuotientGroup.out_eq' p']
        exact QuotientGroup.eq.2 h2
      subst hp
      have h3 : y.1⁻¹ * y'.1 ∈ K' := by
        have e2 : (p.out * y.1)⁻¹ * (p.out * y'.1) = y.1⁻¹ * y'.1 := by group
        rwa [e2] at h1
      have hy : y = y' :=
        Subtype.ext ((hu y'.1 (hX _ y'.2)).unique ⟨y.2, h3⟩ ⟨y'.2, by simp [K'.one_mem]⟩)
      rw [hy]
    · intro q
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      have hk : (QuotientGroup.mk g : G ⧸ K).out⁻¹ * g ∈ K :=
        QuotientGroup.eq.1 (QuotientGroup.out_eq' (QuotientGroup.mk g : G ⧸ K))
      obtain ⟨x, ⟨hx, hxk⟩, -⟩ := hu _ hk
      refine ⟨((QuotientGroup.mk g : G ⧸ K), ⟨x, hx⟩), QuotientGroup.eq.2 ?_⟩
      have e2 : ((QuotientGroup.mk g : G ⧸ K).out * x)⁻¹ * g = x⁻¹ * ((QuotientGroup.mk g : G ⧸ K).out⁻¹ * g) := by
        group
      rwa [e2]
  have hterm : ∀ py, φ (e py).out = φ (py.1.out * py.2.1) := fun py => out_inv hφ _
  have hsupp : (Function.support fun py : (G ⧸ K) × X => φ (py.1.out * py.2.1)).Finite := by
    refine (hfin.preimage he.1.injOn).subset fun py hpy => ?_
    show φ (e py).out ≠ 0
    rw [hterm]
    exact hpy
  calc ∑ᶠ q : G ⧸ K', φ q.out = ∑ᶠ py : (G ⧸ K) × X, φ (e py).out :=
        (finsum_comp (g := fun q : G ⧸ K' => φ q.out) e he).symm
    _ = ∑ᶠ py : (G ⧸ K) × X, φ (py.1.out * py.2.1) := finsum_congr hterm
    _ = ∑ᶠ p : G ⧸ K, ∑ᶠ y : X, φ (p.out * y.1) := finsum_curry _ hsupp
    _ = ∑ᶠ p : G ⧸ K, ∑ y ∈ X, φ (p.out * y) := finsum_congr fun p => by
        rw [finsum_eq_sum_of_fintype, Finset.sum_coe_sort X (fun y => φ (p.out * y))]

end Generic

/- English proof (translation)
Use `haveI : DiscreteTopology (G ⧸ S) := QuotientGroup.discreteTopology hS`. Conclude with `(hc.isCompact.image QuotientGroup.continuous_mk).finite_of_discrete.subset (Set.image_mono (subset_tsupport φ))`.
-/
theorem finite_mk_support {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (S : Subgroup G)
    (hS : IsOpen (S : Set G)) (φ : G → ℂ) (hc : HasCompactSupport φ) :
    ((QuotientGroup.mk : G → G ⧸ S) '' Function.support φ).Finite := by
  haveI : DiscreteTopology (G ⧸ S) := QuotientGroup.discreteTopology hS
  exact (hc.isCompact.image QuotientGroup.continuous_mk).finite_of_discrete.subset
    (Set.image_mono (subset_tsupport φ))

section Blocks

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b n : ℕ}

/- English proof (translation)
Use `ext1`. Rewrite using `[CtLevel.blk_val, CtLevel.dgM_val, CtLevel.dgMat, Matrix.mul_zero]`.
-/
theorem blk_zero_eq_dgM (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w) :
    blk h w m 0 = CtLevel.dgM h w m := by
  ext1
  rw [CtLevel.blk_val, CtLevel.dgM_val, CtLevel.dgMat, Matrix.mul_zero]

/- English proof (translation)
Rewrite using `[GlobalTheory.LeviFubini.blk_mul_blk]`. Simplify using `[add_comm]`.
-/
theorem blk_add (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w)
    (Y Z : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    blk h w m (Y + Z) = blk h w m Y * blk h w 1 Z := by
  rw [GlobalTheory.LeviFubini.blk_mul_blk]
  simp [add_comm]

/- English proof (translation)
Take `⟨hN, hM⟩` from `GlobalTheory.CompanionTheory.LeviInt.comap_uN_and_map_sM E a b n h w`. Set `P` to `GlobalTheory.LeviFubini.parB h w`. Set `KP : Subgroup P` to `(GlobalTheory.LFun.KGL w n).subgroupOf P`. Set `ι : P ⧸ KP → GLw n w ⧸ GlobalTheory.LFun.KGL w n` to `fun q => QuotientGroup.mk (q.out : GLw n w)`. Establish `hι : Function.Bijective ι`.

Prove the components needed by the constructor for the conclusion. Introduce `q q' hqq`. Establish `h1 : ((q.out : GLw n w))⁻¹ * (q'.out : GLw n w) ∈ GlobalTheory.LFun.KGL w n` using `QuotientGroup.eq.1 hqq`. Rewrite using `[← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q']`. Conclude with `QuotientGroup.eq.2 h1`.

Introduce `p`. Take `⟨g, rfl⟩` from `QuotientGroup.mk_surjective p`. Take `⟨m, Y, k, hk, rfl⟩` from `GlobalTheory.CompanionTheory.IwaBlock.iwasawa_parabolic E n a b h w g`. Use `⟨QuotientGroup.mk ⟨blk h w m Y, GlobalTheory.LeviFubini.blk_mem h w m Y⟩, ?_⟩` and prove the remaining obligations. Take `⟨⟨y, hy⟩, hy'⟩` from `QuotientGroup.mk_out_eq_mul KP ⟨blk h w m Y, GlobalTheory.LeviFubini.blk_mem h w m Y⟩`.

Use `QuotientGroup.eq.2 ?_` and prove the remaining obligations. Rewrite using `[hy']`. Establish `hy2 : (y : GLw n w) ∈ GlobalTheory.LFun.KGL w n` using `hy`. Establish `e : (blk h w m Y * (y : GLw n w))⁻¹ * (blk h w m Y * k) = (y : GLw n w)⁻¹ * k` using `by group`. Use `show (blk h w m Y * (y : GLw n w))⁻¹ * (blk h w m Y * k) ∈ GlobalTheory.LFun.KGL w n`.

Rewrite using `[e]`. Conclude with `mul_mem (inv_mem hy2) hk`. Establish `hterm : ∀ q : P ⧸ KP, Ψ (ι q).out = Ψ (q.out : GLw n w)` using `fun q => out_inv hΨ _`. Establish `hfinP : {q : P ⧸ KP | Ψ (q.out : GLw n w) ≠ 0}.Finite`. Use `(hfin.preimage hι.1.injOn).subset fun q hq => ?_` and prove the remaining obligations.

Use `show Ψ (ι q).out ≠ 0`. Rewrite using `[hterm]`. Conclude with `hq`. Establish `e1 : ∑ᶠ p : GLw n w ⧸ GlobalTheory.LFun.KGL w n, Ψ p.out = ∑ᶠ q : P ⧸ KP, Ψ (q.out : GLw n w)` using `(finsum_comp (g := fun p : GLw n w ⧸ GlobalTheory.LFun.KGL w n => Ψ p.out) ι hι).symm.trans (finsum_congr hterm)`. Establish `hl : KP.map (GlobalTheory.LeviFubini.levH h w) ≤ (GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)`.

Introduce and unpack `_ ⟨p, hp, rfl⟩`. Conclude with `GlobalTheory.LeviFubini.levH_mem_KGL_of_mem E a b n h w p hp`. Establish `e2` using `GlobalTheory.split_quotient_finsum_regroup P (GLw a w × GLw b w) (Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E))) ℂ (GlobalTheory.LeviFubini.levH h w) (GlobalTheory.LeviFubini.sM h w) (GlobalTheory.LeviFubini.uN h w) (GlobalTheory.LeviFubini.levH_sM h w) (GlobalTheo …`. Establish `hN' : KP.comap (GlobalTheory.LeviFubini.uN h w) = intMat a b w` using `hN`. Rewrite `e2` using `[hN']`.

Use `e1.trans (e2.trans (finsum_congr fun c => finsum_congr fun x => ?_))` and prove the remaining obligations. Conclude with `congrArg Ψ (GlobalTheory.LeviFubini.sM_mul_uN h w _ _)`.
-/
theorem iwasawa_sum (h : a + b = n) (w : Pl E) (Ψ : GLw n w → ℂ) (hΨ : GlobalTheory.LFun.KGL w n ≤ rStab Ψ)
    (hfin : {p : GLw n w ⧸ GlobalTheory.LFun.KGL w n | Ψ p.out ≠ 0}.Finite) :
    ∑ᶠ p : GLw n w ⧸ GlobalTheory.LFun.KGL w n, Ψ p.out =
      ∑ᶠ c : (GLw a w × GLw b w) ⧸ (GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b),
        ∑ᶠ x : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) ⧸ intMat a b w,
          Ψ (blk h w c.out (Multiplicative.toAdd x.out)) := by
  obtain ⟨hN, hM⟩ := GlobalTheory.CompanionTheory.LeviInt.comap_uN_and_map_sM E a b n h w
  let P := GlobalTheory.LeviFubini.parB h w
  let KP : Subgroup P := (GlobalTheory.LFun.KGL w n).subgroupOf P
  let ι : P ⧸ KP → GLw n w ⧸ GlobalTheory.LFun.KGL w n := fun q => QuotientGroup.mk (q.out : GLw n w)
  have hι : Function.Bijective ι := by
    constructor
    · intro q q' hqq
      have h1 : ((q.out : GLw n w))⁻¹ * (q'.out : GLw n w) ∈ GlobalTheory.LFun.KGL w n := QuotientGroup.eq.1 hqq
      rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q']
      exact QuotientGroup.eq.2 h1
    · intro p
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective p
      obtain ⟨m, Y, k, hk, rfl⟩ := GlobalTheory.CompanionTheory.IwaBlock.iwasawa_parabolic E n a b h w g
      refine ⟨QuotientGroup.mk ⟨blk h w m Y, GlobalTheory.LeviFubini.blk_mem h w m Y⟩, ?_⟩
      obtain ⟨⟨y, hy⟩, hy'⟩ := QuotientGroup.mk_out_eq_mul KP ⟨blk h w m Y, GlobalTheory.LeviFubini.blk_mem h w m Y⟩
      refine QuotientGroup.eq.2 ?_
      rw [hy']
      have hy2 : (y : GLw n w) ∈ GlobalTheory.LFun.KGL w n := hy
      have e : (blk h w m Y * (y : GLw n w))⁻¹ * (blk h w m Y * k) = (y : GLw n w)⁻¹ * k := by group
      show (blk h w m Y * (y : GLw n w))⁻¹ * (blk h w m Y * k) ∈ GlobalTheory.LFun.KGL w n
      rw [e]
      exact mul_mem (inv_mem hy2) hk
  have hterm : ∀ q : P ⧸ KP, Ψ (ι q).out = Ψ (q.out : GLw n w) := fun q => out_inv hΨ _
  have hfinP : {q : P ⧸ KP | Ψ (q.out : GLw n w) ≠ 0}.Finite := by
    refine (hfin.preimage hι.1.injOn).subset fun q hq => ?_
    show Ψ (ι q).out ≠ 0
    rw [hterm]
    exact hq
  have e1 : ∑ᶠ p : GLw n w ⧸ GlobalTheory.LFun.KGL w n, Ψ p.out = ∑ᶠ q : P ⧸ KP, Ψ (q.out : GLw n w) :=
    (finsum_comp (g := fun p : GLw n w ⧸ GlobalTheory.LFun.KGL w n => Ψ p.out) ι hι).symm.trans (finsum_congr hterm)
  have hl : KP.map (GlobalTheory.LeviFubini.levH h w) ≤ (GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b) := by
    rintro _ ⟨p, hp, rfl⟩
    exact GlobalTheory.LeviFubini.levH_mem_KGL_of_mem E a b n h w p hp
  have e2 := GlobalTheory.split_quotient_finsum_regroup P (GLw a w × GLw b w)
    (Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E))) ℂ (GlobalTheory.LeviFubini.levH h w)
    (GlobalTheory.LeviFubini.sM h w) (GlobalTheory.LeviFubini.uN h w) (GlobalTheory.LeviFubini.levH_sM h w) (GlobalTheory.LeviFubini.levH_uN h w)
    (GlobalTheory.LeviFubini.uN_injective h w) (GlobalTheory.LeviFubini.exists_uN h w) KP
    ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)) hM hl (fun p => Ψ p)
    (fun p q hq => hΨ hq (p : GLw n w)) hfinP
  have hN' : KP.comap (GlobalTheory.LeviFubini.uN h w) = intMat a b w := hN
  rw [hN'] at e2
  refine e1.trans (e2.trans (finsum_congr fun c => finsum_congr fun x => ?_))
  exact congrArg Ψ (GlobalTheory.LeviFubini.sM_mul_uN h w _ _)

/- English proof (translation)
Establish `h2` using `GlobalTheory.LeviFubini.levH_mem_KGL_of_mem E a b n h w (p'⁻¹ * p) (by simpa using hc)`. Rewrite `h2` using `[map_mul, map_inv]`. Conclude with `Subgroup.mem_prod.2 h2`.
-/
theorem lev_mul_mem (h : a + b = n) (w : Pl E) (p p' : GlobalTheory.LeviFubini.parB h w)
    (hc : ((p' : GLw n w))⁻¹ * (p : GLw n w) ∈ GlobalTheory.LFun.KGL w n) :
    (GlobalTheory.LeviFubini.levH h w p')⁻¹ * GlobalTheory.LeviFubini.levH h w p ∈ (GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b) := by
  have h2 := GlobalTheory.LeviFubini.levH_mem_KGL_of_mem E a b n h w (p'⁻¹ * p) (by simpa using hc)
  rw [map_mul, map_inv] at h2
  exact Subgroup.mem_prod.2 h2

/- English proof (translation)
Establish `h2` using `lev_mul_mem h w ⟨blk h w m Y, GlobalTheory.LeviFubini.blk_mem h w m Y⟩ ⟨blk h w m' Y', GlobalTheory.LeviFubini.blk_mem h w m' Y'⟩ hc`. Rewrite `h2` using `[GlobalTheory.LeviFubini.levH_blk, GlobalTheory.LeviFubini.levH_blk]`. Then use the resulting hypothesis.
-/
theorem lev_coset (h : a + b = n) (w : Pl E) (m m' : GLw a w × GLw b w)
    (Y Y' : Matrix (Fin a) (Fin b) (w.adicCompletion E))
    (hc : (blk h w m' Y')⁻¹ * blk h w m Y ∈ GlobalTheory.LFun.KGL w n) :
    m'⁻¹ * m ∈ (GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b) := by
  have h2 := lev_mul_mem h w ⟨blk h w m Y, GlobalTheory.LeviFubini.blk_mem h w m Y⟩
    ⟨blk h w m' Y', GlobalTheory.LeviFubini.blk_mem h w m' Y'⟩ hc
  rwa [GlobalTheory.LeviFubini.levH_blk, GlobalTheory.LeviFubini.levH_blk] at h2

/- English proof (translation)
Establish `hex : ∀ c : B, ∃ (m : GLw a w × GLw b w) (Y : Matrix (Fin a) (Fin b) (w.adicCompletion E)), (QuotientGroup.mk m : (GLw a w × GLw b w) ⧸ (GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)) = c.1 ∧ (QuotientGroup.mk (blk h w m Y) : GLw n w ⧸ GlobalTheory.LFun.KGL w n) ∈ Z` using `fun c => hB c.1 c.2`. Use `choose tm tY ht1 ht2 using hex`. Use `haveI := hZ.to_subtype`. Establish `hinj : Function.Injective fun c : B => (⟨_, ht2 c⟩ : Z)`. Introduce `c c' hcc`.

Establish `hc` using `congrArg Subtype.val hcc`. Establish `h1` using `lev_coset h w (tm c') (tm c) (tY c') (tY c) (QuotientGroup.eq.1 hc)`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← ht1 c, ← ht1 c']`. Conclude with `QuotientGroup.eq.2 h1`.

Use `haveI : Finite B := Finite.of_injective _ hinj`. Conclude with `Set.toFinite B`.
-/
theorem finite_lev (h : a + b = n) (w : Pl E) (Z : Set (GLw n w ⧸ GlobalTheory.LFun.KGL w n)) (hZ : Z.Finite)
    (B : Set ((GLw a w × GLw b w) ⧸ (GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)))
    (hB : ∀ c ∈ B, ∃ (m : GLw a w × GLw b w) (Y : Matrix (Fin a) (Fin b) (w.adicCompletion E)),
      (QuotientGroup.mk m : (GLw a w × GLw b w) ⧸ (GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)) = c ∧
        (QuotientGroup.mk (blk h w m Y) : GLw n w ⧸ GlobalTheory.LFun.KGL w n) ∈ Z) : B.Finite := by
  have hex : ∀ c : B, ∃ (m : GLw a w × GLw b w) (Y : Matrix (Fin a) (Fin b) (w.adicCompletion E)),
      (QuotientGroup.mk m : (GLw a w × GLw b w) ⧸ (GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)) = c.1 ∧
        (QuotientGroup.mk (blk h w m Y) : GLw n w ⧸ GlobalTheory.LFun.KGL w n) ∈ Z := fun c => hB c.1 c.2
  choose tm tY ht1 ht2 using hex
  haveI := hZ.to_subtype
  have hinj : Function.Injective fun c : B => (⟨_, ht2 c⟩ : Z) := by
    intro c c' hcc
    have hc := congrArg Subtype.val hcc
    have h1 := lev_coset h w (tm c') (tm c) (tY c') (tY c) (QuotientGroup.eq.1 hc)
    apply Subtype.ext
    rw [← ht1 c, ← ht1 c']
    exact QuotientGroup.eq.2 h1
  haveI : Finite B := Finite.of_injective _ hinj
  exact Set.toFinite B

end Blocks

/- English proof (translation)
Introduce `E _ _ _ n a b h w K' hK'o hK'K hnorm X hX hu φ hφ hφc`. Establish `hφS : K' ≤ rStab φ` using `fun k hk g => hφ g k hk`. Establish `hKo : IsOpen (GlobalTheory.LFun.KGL w n : Set (GLw n w))` using `Subgroup.isOpen_mono hK'K hK'o`. Establish `hZ'` using `finite_mk_support K' hK'o φ hφc`. Establish `hZ` using `finite_mk_support (GlobalTheory.LFun.KGL w n) hKo φ hφc`.

Establish `hfin0 : {q : GLw n w ⧸ K' | φ q.out ≠ 0}.Finite` using `hZ'.subset fun q hq => ⟨q.out, hq, QuotientGroup.out_eq' q⟩`. Set `Ψ : GLw n w → ℂ` to `fun g => ∑ y ∈ X, φ (g * y)`. Establish `hΨ : GlobalTheory.LFun.KGL w n ≤ rStab Ψ` using `fun k hk g => sum_mul_mem X hX hu φ hφS g k hk`. Establish `hfinΨ : {p : GLw n w ⧸ GlobalTheory.LFun.KGL w n | Ψ p.out ≠ 0}.Finite`. Use `hZ.subset fun p hp => ?_` and prove the remaining obligations.

Take `⟨y, hy, hy0⟩` from `Finset.exists_ne_zero_of_sum_ne_zero hp`. Use `⟨p.out * y, hy0, ?_⟩` and prove the remaining obligations. Rewrite using `[QuotientGroup.mk_mul_of_mem _ (hX y hy)]`. Conclude with `QuotientGroup.out_eq' p`. Establish `hcard` using `relIndex_eq_card X hX hu`.

Establish `hcard0 : K'.relIndex (GlobalTheory.LFun.KGL w n) ≠ 0`. Take `⟨x, ⟨hx, -⟩, -⟩` from `hu 1 (one_mem _)`. Rewrite using `[hcard]`. Conclude with `Finset.card_ne_zero.2 ⟨x, hx⟩`. Establish `hLHS : hint (GlobalTheory.LFun.KGL w n) φ = ((X.card : ℂ))⁻¹ * ∑ᶠ p : GLw n w ⧸ GlobalTheory.LFun.KGL w n, Ψ p.out`.

Rewrite using `[GlobalTheory.CompanionTheory.HintSmaller.hint_eq_of_le _ K' φ hK'K hφS hcard0 hfin0, hcard, finsum_fibre hK'K X hX hu φ hφS hfin0]`. Take `⟨hN, hM⟩` from `GlobalTheory.CompanionTheory.LeviInt.comap_uN_and_map_sM E a b n h w`. Take `⟨hLle, hLfin⟩` from `GlobalTheory.CompanionTheory.UnipLevel.unip_level E a b n h w K' hK'o hK'K`. Generalize the expression as in `hLdef : (K'.subgroupOf (GlobalTheory.LeviFubini.parB h w)).comap (GlobalTheory.LeviFubini.uN h w) = L at hLle hLfin`. Establish `hLmem : ∀ Z ∈ L, blk h w 1 (Multiplicative.toAdd Z) ∈ K'`.

Introduce `Z hZ`. Rewrite `hZ` using `[← hLdef]`. Conclude with `hZ`. Establish `hmemL : ∀ Z, blk h w 1 (Multiplicative.toAdd Z) ∈ K' → Z ∈ L`. Introduce `Z hZ`.

Rewrite using `[← hLdef]`. Conclude with `hZ`. Establish `hLinv : ∀ y ∈ X, ∀ m, L ≤ rStab (fun Y => φ (blk h w m (Multiplicative.toAdd Y) * y))`. Introduce `y hy m Z hZ Y`. Use `show φ (blk h w m (Multiplicative.toAdd (Y * Z)) * y) = φ (blk h w m (Multiplicative.toAdd Y) * y)`.

Rewrite using `[toAdd_mul, blk_add]`. Establish `e : blk h w m (Multiplicative.toAdd Y) * blk h w 1 (Multiplicative.toAdd Z) * y = blk h w m (Multiplicative.toAdd Y) * y * (y⁻¹ * blk h w 1 (Multiplicative.toAdd Z) * y)` using `by group`. Rewrite using `[e]`. Conclude with `hφ _ _ (by simpa using hnorm y⁻¹ (inv_mem (hX y hy)) _ (hLmem Z hZ))`. Establish `hLΨ : ∀ m, L ≤ rStab (fun Y => Ψ (blk h w m (Multiplicative.toAdd Y)))`.

Introduce `m Z hZ Y`. Conclude with `Finset.sum_congr rfl fun y hy => hLinv y hy m hZ Y`. Establish `hNfin : ∀ m, ∀ y ∈ X, (Function.support fun q : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) ⧸ L => φ (blk h w m (Multiplicative.toAdd q.out) * y)).Finite`. Introduce `m y hy`. Use `Set.Finite.of_injOn (f := fun q : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) ⧸ L => (QuotientGroup.mk (blk h w m (Multiplicative.toAdd q.out) * y) : GLw n w ⧸ K')) ?_ ?_ hZ'` and prove the remaining obligations.

Introduce `q hq`. Conclude with `⟨_, hq, rfl⟩`. Introduce `q _ q' _ hqq`. Establish `h1` using `QuotientGroup.eq.1 hqq`. Establish `e0 : blk h w m (Multiplicative.toAdd q.out) * blk h w 1 (Multiplicative.toAdd (q.out⁻¹ * q'.out)) = blk h w m (Multiplicative.toAdd q'.out)`.

Rewrite using `[← blk_add]`. Use `congr 1`. Simplify using the standard rewrite rules. Rewrite `h1` using `[← e0]`. Establish `h2` using `hnorm y (hX y hy) _ h1`.

Establish `e1 : y * ((blk h w m (Multiplicative.toAdd q.out) * y)⁻¹ * (blk h w m (Multiplicative.toAdd q.out) * blk h w 1 (Multiplicative.toAdd (q.out⁻¹ * q'.out)) * y)) * y⁻¹ = blk h w 1 (Multiplicative.toAdd (q.out⁻¹ * q'.out))` using `by group`. Rewrite `h2` using `[e1]`. Rewrite using `[← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q']`. Conclude with `QuotientGroup.eq.2 (hmemL _ h2)`. Establish `hNsum : ∀ m, ∑ y ∈ X, hint (intMat a b w) (fun Y => φ (blk h w m (Multiplicative.toAdd Y) * y)) = hint (intMat a b w) (fun Y => Ψ (blk h w m (Multiplicative.toAdd Y)))`.

Introduce `m`. Rewrite using `[GlobalTheory.CompanionTheory.HintLevel.hint_eq_level _ (intMat a b w) L _ hLle (hLΨ m) hLfin, Finset.sum_congr rfl fun y hy => GlobalTheory.CompanionTheory.HintLevel.hint_eq_level _ (intMat a b w) L _ hLle (hLinv y hy m) hLfin, ← Finset.mul_sum]`. Use `congr 1`. Conclude with `(finsum_sum_comm X _ fun y hy => hNfin m y hy).symm`. Establish `hdiag : ∀ c ∈ (GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b), blk h w c 0 ∈ GlobalTheory.LFun.KGL w n`.

Introduce `c hc`. Conclude with `hM ⟨c, hc, rfl⟩`. Establish `hNK : ∀ Z ∈ intMat a b w, blk h w 1 (Multiplicative.toAdd Z) ∈ GlobalTheory.LFun.KGL w n`. Introduce `Z hZ`. Rewrite `hZ` using `[← hN]`.

Conclude with `hZ`. Establish `hNΨ : ∀ m, intMat a b w ≤ rStab (fun Y => Ψ (blk h w m (Multiplicative.toAdd Y)))`. Introduce `m Z hZ Y`. Use `show Ψ (blk h w m (Multiplicative.toAdd (Y * Z))) = Ψ (blk h w m (Multiplicative.toAdd Y))`. Rewrite using `[toAdd_mul, blk_add]`.

Conclude with `hΨ (hNK Z hZ) _`. Set `f : GLw a w × GLw b w →* GLw n w` to `(GlobalTheory.LeviFubini.parB h w).subtype.comp (GlobalTheory.LeviFubini.sM h w)`. Establish `hf : ∀ c, f c = blk h w c 0` using `fun c => rfl`. Establish `hSMK : K'.comap f ≤ (GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)`. Introduce `c hc`.

Establish `h1` using `GlobalTheory.LeviFubini.levH_mem_KGL_of_mem E a b n h w (GlobalTheory.LeviFubini.sM h w c) (hK'K hc)`. Rewrite `h1` using `[GlobalTheory.LeviFubini.levH_sM]`. Conclude with `Subgroup.mem_prod.2 h1`. Establish `hSMfin : (K'.comap f).relIndex ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)) ≠ 0`. Rewrite using `[Subgroup.relIndex_comap]`.

Introduce `h0`. Use `hcard0 (Subgroup.relIndex_eq_zero_of_le_right ?_ h0)` and prove the remaining obligations. Introduce and unpack `_ ⟨c, hc, rfl⟩`. Conclude with `hdiag c hc`. Establish `hFinv : ∀ y ∈ X, K'.comap f ≤ rStab (fun m => hint (intMat a b w) (fun Y => φ (blk h w m (Multiplicative.toAdd Y) * y)))`.

Introduce `y hy c hc m`. Establish `hcK` using `Subgroup.mem_prod.1 (hSMK hc)`. Establish `hd : CtLevel.dgM h w c ∈ K'`. Rewrite using `[← blk_zero_eq_dgM]`. Conclude with `hc`.

Establish `e : (fun Y => φ (blk h w (m * c) (Multiplicative.toAdd Y) * y)) = fun Y => (fun Z => φ (blk h w m (Multiplicative.toAdd Z) * y)) (Multiplicative.ofAdd (c.1.val * Multiplicative.toAdd Y * (c.2⁻¹).val))`. Use function extensionality and compare the values at `Y`. Rewrite using `[(CtLevel.blk_mul_dgM E a b n h w m c _).2]`. Establish `e2 : blk h w m (c.1.val * Multiplicative.toAdd Y * (c.2⁻¹).val) * CtLevel.dgM h w c * y = blk h w m (c.1.val * Multiplicative.toAdd Y * (c.2⁻¹).val) * y * (y⁻¹ * CtLevel.dgM h w c * y)` using `by group`. Rewrite using `[e2]`.

Conclude with `hφ _ _ (by simpa using hnorm y⁻¹ (inv_mem (hX y hy)) _ hd)`. Establish `hh` using `HintInv.hint_intMat_mul_mul E a b w (fun Z => φ (blk h w m (Multiplicative.toAdd Z) * y)) c.1 c.2⁻¹ hcK.1 (inv_mem hcK.2)`. Use `show hint (intMat a b w) (fun Y => φ (blk h w (m * c) (Multiplicative.toAdd Y) * y)) = hint (intMat a b w) (fun Y => φ (blk h w m (Multiplicative.toAdd Y) * y))`. Rewrite using `[e]`. Conclude with `hh`.

Establish `hTinv : (GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b) ≤ rStab (fun m => hint (intMat a b w) (fun Y => Ψ (blk h w m (Multiplicative.toAdd Y))))`. Introduce `c hc m`. Establish `hcK` using `Subgroup.mem_prod.1 hc`. Establish `hd : CtLevel.dgM h w c ∈ GlobalTheory.LFun.KGL w n`. Rewrite using `[← blk_zero_eq_dgM]`.

Conclude with `hdiag c hc`. Establish `e : (fun Y => Ψ (blk h w (m * c) (Multiplicative.toAdd Y))) = fun Y => (fun Z => Ψ (blk h w m (Multiplicative.toAdd Z))) (Multiplicative.ofAdd (c.1.val * Multiplicative.toAdd Y * (c.2⁻¹).val))`. Use function extensionality and compare the values at `Y`. Rewrite using `[(CtLevel.blk_mul_dgM E a b n h w m c _).2]`. Conclude with `hΨ hd _`.

Establish `hh` using `HintInv.hint_intMat_mul_mul E a b w (fun Z => Ψ (blk h w m (Multiplicative.toAdd Z))) c.1 c.2⁻¹ hcK.1 (inv_mem hcK.2)`. Use `show hint (intMat a b w) (fun Y => Ψ (blk h w (m * c) (Multiplicative.toAdd Y))) = hint (intMat a b w) (fun Y => Ψ (blk h w m (Multiplicative.toAdd Y)))`. Rewrite using `[e]`. Conclude with `hh`. Establish `hFfin : ∀ y ∈ X, (Function.support fun q : (GLw a w × GLw b w) ⧸ K'.comap f => hint (intMat a b w) (fun Y => φ (blk h w q.out (Multiplicative.toAdd Y) * y))).Finite`.

Introduce `y hy`. Use `finite_of_image hSMK hSMfin _ (finite_lev h w _ hZ _ ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨q, hq, rfl⟩`. Take `⟨Y, hY⟩` from `CtLevel.exists_ne_zero_of_hint_ne_zero _ _ hq`. Use `⟨q.out, Multiplicative.toAdd Y, rfl, blk h w q.out (Multiplicative.toAdd Y) * y, hY, ?_⟩` and prove the remaining obligations.

Conclude with `QuotientGroup.mk_mul_of_mem _ (hX y hy)`. Establish `hself : ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)).relIndex ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)) ≠ 0`. Rewrite using `[Subgroup.relIndex_self]`. Conclude with `one_ne_zero`. Establish `hselfN : (intMat a b w).relIndex (intMat a b w) ≠ 0`.

Rewrite using `[Subgroup.relIndex_self]`. Conclude with `one_ne_zero`. Establish `hR : ∑ y ∈ X, hint ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)) (fun m => hint (intMat a b w) (fun Y => φ (blk h w m (Multiplicative.toAdd Y) * y))) = ∑ᶠ p : GLw n w ⧸ GlobalTheory.LFun.KGL w n, Ψ p.out`. Rewrite using `[Finset.sum_congr rfl fun y hy => GlobalTheory.CompanionTheory.HintLevel.hint_eq_level _ _ (K'.comap f) _ hSMK (hFinv y hy) hSMfin, ← Finset.mul_sum, ← finsum_sum_comm X _ hFfin]`. Simplify using `only [hNsum]`.

Rewrite using `[← GlobalTheory.CompanionTheory.HintLevel.hint_eq_level _ _ (K'.comap f) _ hSMK (hSMK.trans hTinv) hSMfin, GlobalTheory.CompanionTheory.HintLevel.hint_eq_level _ _ _ _ le_rfl hTinv hself, Subgroup.relIndex_self, Nat.cast_one, inv_one, one_mul, iwasawa_sum h w Ψ hΨ hfinΨ]`. Use `finsum_congr fun c => ?_` and prove the remaining obligations. Rewrite using `[GlobalTheory.CompanionTheory.HintLevel.hint_eq_level _ _ _ _ le_rfl (hNΨ c.out) hselfN, Subgroup.relIndex_self, Nat.cast_one, inv_one, one_mul]`. Rewrite using `[hLHS, hR]`.
-/
theorem integral_decomposition : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (K' : Subgroup (GLw n w)), IsOpen (K' : Set (GLw n w)) → K' ≤ GlobalTheory.LFun.KGL w n → (∀ k ∈ GlobalTheory.LFun.KGL w n, ∀ k' ∈ K', k * k' * k⁻¹ ∈ K') → ∀ X : Finset (GLw n w), (∀ x ∈ X, x ∈ GlobalTheory.LFun.KGL w n) → (∀ k ∈ GlobalTheory.LFun.KGL w n, ∃! x ∈ X, x⁻¹ * k ∈ K') → ∀ φ : GLw n w → ℂ, (∀ g, ∀ k ∈ K', φ (g * k) = φ g) → HasCompactSupport φ → hint (GlobalTheory.LFun.KGL w n) φ = ((X.card : ℂ))⁻¹ * ∑ y ∈ X, hint ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)) fun m => hint (intMat a b w) fun Y => φ (blk h w m (Multiplicative.toAdd Y) * y) := by
  intro E _ _ _ n a b h w K' hK'o hK'K hnorm X hX hu φ hφ hφc
  have hφS : K' ≤ rStab φ := fun k hk g => hφ g k hk
  have hKo : IsOpen (GlobalTheory.LFun.KGL w n : Set (GLw n w)) := Subgroup.isOpen_mono hK'K hK'o
  have hZ' := finite_mk_support K' hK'o φ hφc
  have hZ := finite_mk_support (GlobalTheory.LFun.KGL w n) hKo φ hφc
  have hfin0 : {q : GLw n w ⧸ K' | φ q.out ≠ 0}.Finite :=
    hZ'.subset fun q hq => ⟨q.out, hq, QuotientGroup.out_eq' q⟩
  let Ψ : GLw n w → ℂ := fun g => ∑ y ∈ X, φ (g * y)
  have hΨ : GlobalTheory.LFun.KGL w n ≤ rStab Ψ := fun k hk g => sum_mul_mem X hX hu φ hφS g k hk
  have hfinΨ : {p : GLw n w ⧸ GlobalTheory.LFun.KGL w n | Ψ p.out ≠ 0}.Finite := by
    refine hZ.subset fun p hp => ?_
    obtain ⟨y, hy, hy0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hp
    refine ⟨p.out * y, hy0, ?_⟩
    rw [QuotientGroup.mk_mul_of_mem _ (hX y hy)]
    exact QuotientGroup.out_eq' p
  have hcard := relIndex_eq_card X hX hu
  have hcard0 : K'.relIndex (GlobalTheory.LFun.KGL w n) ≠ 0 := by
    obtain ⟨x, ⟨hx, -⟩, -⟩ := hu 1 (one_mem _)
    rw [hcard]
    exact Finset.card_ne_zero.2 ⟨x, hx⟩
  have hLHS : hint (GlobalTheory.LFun.KGL w n) φ =
      ((X.card : ℂ))⁻¹ * ∑ᶠ p : GLw n w ⧸ GlobalTheory.LFun.KGL w n, Ψ p.out := by
    rw [GlobalTheory.CompanionTheory.HintSmaller.hint_eq_of_le _ K' φ hK'K hφS hcard0 hfin0, hcard,
      finsum_fibre hK'K X hX hu φ hφS hfin0]
  obtain ⟨hN, hM⟩ := GlobalTheory.CompanionTheory.LeviInt.comap_uN_and_map_sM E a b n h w
  obtain ⟨hLle, hLfin⟩ := GlobalTheory.CompanionTheory.UnipLevel.unip_level E a b n h w K' hK'o hK'K
  generalize hLdef : (K'.subgroupOf (GlobalTheory.LeviFubini.parB h w)).comap (GlobalTheory.LeviFubini.uN h w) = L at hLle hLfin
  have hLmem : ∀ Z ∈ L, blk h w 1 (Multiplicative.toAdd Z) ∈ K' := by
    intro Z hZ
    rw [← hLdef] at hZ
    exact hZ
  have hmemL : ∀ Z, blk h w 1 (Multiplicative.toAdd Z) ∈ K' → Z ∈ L := by
    intro Z hZ
    rw [← hLdef]
    exact hZ
  have hLinv : ∀ y ∈ X, ∀ m, L ≤ rStab (fun Y => φ (blk h w m (Multiplicative.toAdd Y) * y)) := by
    intro y hy m Z hZ Y
    show φ (blk h w m (Multiplicative.toAdd (Y * Z)) * y) = φ (blk h w m (Multiplicative.toAdd Y) * y)
    rw [toAdd_mul, blk_add]
    have e : blk h w m (Multiplicative.toAdd Y) * blk h w 1 (Multiplicative.toAdd Z) * y =
        blk h w m (Multiplicative.toAdd Y) * y * (y⁻¹ * blk h w 1 (Multiplicative.toAdd Z) * y) := by group
    rw [e]
    exact hφ _ _ (by simpa using hnorm y⁻¹ (inv_mem (hX y hy)) _ (hLmem Z hZ))
  have hLΨ : ∀ m, L ≤ rStab (fun Y => Ψ (blk h w m (Multiplicative.toAdd Y))) := by
    intro m Z hZ Y
    exact Finset.sum_congr rfl fun y hy => hLinv y hy m hZ Y
  have hNfin : ∀ m, ∀ y ∈ X, (Function.support fun q : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) ⧸ L =>
      φ (blk h w m (Multiplicative.toAdd q.out) * y)).Finite := by
    intro m y hy
    refine Set.Finite.of_injOn (f := fun q : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) ⧸ L =>
      (QuotientGroup.mk (blk h w m (Multiplicative.toAdd q.out) * y) : GLw n w ⧸ K')) ?_ ?_ hZ'
    · intro q hq
      exact ⟨_, hq, rfl⟩
    · intro q _ q' _ hqq
      have h1 := QuotientGroup.eq.1 hqq
      have e0 : blk h w m (Multiplicative.toAdd q.out) * blk h w 1 (Multiplicative.toAdd (q.out⁻¹ * q'.out)) =
          blk h w m (Multiplicative.toAdd q'.out) := by
        rw [← blk_add]
        congr 1
        simp
      rw [← e0] at h1
      have h2 := hnorm y (hX y hy) _ h1
      have e1 : y * ((blk h w m (Multiplicative.toAdd q.out) * y)⁻¹ * (blk h w m (Multiplicative.toAdd q.out) *
          blk h w 1 (Multiplicative.toAdd (q.out⁻¹ * q'.out)) * y)) * y⁻¹ =
          blk h w 1 (Multiplicative.toAdd (q.out⁻¹ * q'.out)) := by group
      rw [e1] at h2
      rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q']
      exact QuotientGroup.eq.2 (hmemL _ h2)
  have hNsum : ∀ m, ∑ y ∈ X, hint (intMat a b w) (fun Y => φ (blk h w m (Multiplicative.toAdd Y) * y)) =
      hint (intMat a b w) (fun Y => Ψ (blk h w m (Multiplicative.toAdd Y))) := by
    intro m
    rw [GlobalTheory.CompanionTheory.HintLevel.hint_eq_level _ (intMat a b w) L _ hLle (hLΨ m) hLfin,
      Finset.sum_congr rfl fun y hy =>
        GlobalTheory.CompanionTheory.HintLevel.hint_eq_level _ (intMat a b w) L _ hLle (hLinv y hy m) hLfin, ← Finset.mul_sum]
    congr 1
    exact (finsum_sum_comm X _ fun y hy => hNfin m y hy).symm
  have hdiag : ∀ c ∈ (GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b), blk h w c 0 ∈ GlobalTheory.LFun.KGL w n := by
    intro c hc
    exact hM ⟨c, hc, rfl⟩
  have hNK : ∀ Z ∈ intMat a b w, blk h w 1 (Multiplicative.toAdd Z) ∈ GlobalTheory.LFun.KGL w n := by
    intro Z hZ
    rw [← hN] at hZ
    exact hZ
  have hNΨ : ∀ m, intMat a b w ≤ rStab (fun Y => Ψ (blk h w m (Multiplicative.toAdd Y))) := by
    intro m Z hZ Y
    show Ψ (blk h w m (Multiplicative.toAdd (Y * Z))) = Ψ (blk h w m (Multiplicative.toAdd Y))
    rw [toAdd_mul, blk_add]
    exact hΨ (hNK Z hZ) _
  let f : GLw a w × GLw b w →* GLw n w := (GlobalTheory.LeviFubini.parB h w).subtype.comp (GlobalTheory.LeviFubini.sM h w)
  have hf : ∀ c, f c = blk h w c 0 := fun c => rfl
  have hSMK : K'.comap f ≤ (GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b) := by
    intro c hc
    have h1 := GlobalTheory.LeviFubini.levH_mem_KGL_of_mem E a b n h w (GlobalTheory.LeviFubini.sM h w c) (hK'K hc)
    rw [GlobalTheory.LeviFubini.levH_sM] at h1
    exact Subgroup.mem_prod.2 h1
  have hSMfin : (K'.comap f).relIndex ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)) ≠ 0 := by
    rw [Subgroup.relIndex_comap]
    intro h0
    refine hcard0 (Subgroup.relIndex_eq_zero_of_le_right ?_ h0)
    rintro _ ⟨c, hc, rfl⟩
    exact hdiag c hc
  have hFinv : ∀ y ∈ X, K'.comap f ≤ rStab (fun m =>
      hint (intMat a b w) (fun Y => φ (blk h w m (Multiplicative.toAdd Y) * y))) := by
    intro y hy c hc m
    have hcK := Subgroup.mem_prod.1 (hSMK hc)
    have hd : CtLevel.dgM h w c ∈ K' := by
      rw [← blk_zero_eq_dgM]
      exact hc
    have e : (fun Y => φ (blk h w (m * c) (Multiplicative.toAdd Y) * y)) = fun Y =>
        (fun Z => φ (blk h w m (Multiplicative.toAdd Z) * y))
          (Multiplicative.ofAdd (c.1.val * Multiplicative.toAdd Y * (c.2⁻¹).val)) := by
      funext Y
      rw [(CtLevel.blk_mul_dgM E a b n h w m c _).2]
      have e2 : blk h w m (c.1.val * Multiplicative.toAdd Y * (c.2⁻¹).val) * CtLevel.dgM h w c * y =
          blk h w m (c.1.val * Multiplicative.toAdd Y * (c.2⁻¹).val) * y * (y⁻¹ * CtLevel.dgM h w c * y) := by group
      rw [e2]
      exact hφ _ _ (by simpa using hnorm y⁻¹ (inv_mem (hX y hy)) _ hd)
    have hh := HintInv.hint_intMat_mul_mul E a b w (fun Z => φ (blk h w m (Multiplicative.toAdd Z) * y))
      c.1 c.2⁻¹ hcK.1 (inv_mem hcK.2)
    show hint (intMat a b w) (fun Y => φ (blk h w (m * c) (Multiplicative.toAdd Y) * y)) =
      hint (intMat a b w) (fun Y => φ (blk h w m (Multiplicative.toAdd Y) * y))
    rw [e]
    exact hh
  have hTinv : (GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b) ≤ rStab (fun m =>
      hint (intMat a b w) (fun Y => Ψ (blk h w m (Multiplicative.toAdd Y)))) := by
    intro c hc m
    have hcK := Subgroup.mem_prod.1 hc
    have hd : CtLevel.dgM h w c ∈ GlobalTheory.LFun.KGL w n := by
      rw [← blk_zero_eq_dgM]
      exact hdiag c hc
    have e : (fun Y => Ψ (blk h w (m * c) (Multiplicative.toAdd Y))) = fun Y =>
        (fun Z => Ψ (blk h w m (Multiplicative.toAdd Z)))
          (Multiplicative.ofAdd (c.1.val * Multiplicative.toAdd Y * (c.2⁻¹).val)) := by
      funext Y
      rw [(CtLevel.blk_mul_dgM E a b n h w m c _).2]
      exact hΨ hd _
    have hh := HintInv.hint_intMat_mul_mul E a b w (fun Z => Ψ (blk h w m (Multiplicative.toAdd Z)))
      c.1 c.2⁻¹ hcK.1 (inv_mem hcK.2)
    show hint (intMat a b w) (fun Y => Ψ (blk h w (m * c) (Multiplicative.toAdd Y))) =
      hint (intMat a b w) (fun Y => Ψ (blk h w m (Multiplicative.toAdd Y)))
    rw [e]
    exact hh
  have hFfin : ∀ y ∈ X, (Function.support fun q : (GLw a w × GLw b w) ⧸ K'.comap f =>
      hint (intMat a b w) (fun Y => φ (blk h w q.out (Multiplicative.toAdd Y) * y))).Finite := by
    intro y hy
    refine finite_of_image hSMK hSMfin _ (finite_lev h w _ hZ _ ?_)
    rintro _ ⟨q, hq, rfl⟩
    obtain ⟨Y, hY⟩ := CtLevel.exists_ne_zero_of_hint_ne_zero _ _ hq
    refine ⟨q.out, Multiplicative.toAdd Y, rfl, blk h w q.out (Multiplicative.toAdd Y) * y, hY, ?_⟩
    exact QuotientGroup.mk_mul_of_mem _ (hX y hy)
  have hself : ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)).relIndex
      ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)) ≠ 0 := by
    rw [Subgroup.relIndex_self]
    exact one_ne_zero
  have hselfN : (intMat a b w).relIndex (intMat a b w) ≠ 0 := by
    rw [Subgroup.relIndex_self]
    exact one_ne_zero
  have hR : ∑ y ∈ X, hint ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)) (fun m =>
      hint (intMat a b w) (fun Y => φ (blk h w m (Multiplicative.toAdd Y) * y))) =
      ∑ᶠ p : GLw n w ⧸ GlobalTheory.LFun.KGL w n, Ψ p.out := by
    rw [Finset.sum_congr rfl fun y hy =>
        GlobalTheory.CompanionTheory.HintLevel.hint_eq_level _ _ (K'.comap f) _ hSMK (hFinv y hy) hSMfin, ← Finset.mul_sum,
      ← finsum_sum_comm X _ hFfin]
    simp only [hNsum]
    rw [← GlobalTheory.CompanionTheory.HintLevel.hint_eq_level _ _ (K'.comap f) _ hSMK (hSMK.trans hTinv) hSMfin,
      GlobalTheory.CompanionTheory.HintLevel.hint_eq_level _ _ _ _ le_rfl hTinv hself, Subgroup.relIndex_self, Nat.cast_one, inv_one,
      one_mul, iwasawa_sum h w Ψ hΨ hfinΨ]
    refine finsum_congr fun c => ?_
    rw [GlobalTheory.CompanionTheory.HintLevel.hint_eq_level _ _ _ _ le_rfl (hNΨ c.out) hselfN, Subgroup.relIndex_self, Nat.cast_one,
      inv_one, one_mul]
  rw [hLHS, hR]

end GlobalTheory.CompanionTheory.IntDec
