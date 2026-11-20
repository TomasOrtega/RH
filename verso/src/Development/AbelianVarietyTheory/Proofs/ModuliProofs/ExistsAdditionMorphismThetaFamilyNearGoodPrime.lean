import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DenseOfDenseP
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFamilyAdditionMorphismThetaLevel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFamilyHomOfGraphsOverRingInvertingElementStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AdditionGraphThetaObjectCutOutBoundedDegree

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild
open GlobalTheory.ZM.BuildAdd

noncomputable section
namespace GlobalTheory.ZM.NearBuild

/- English proof (translation)
Introduce `hL hL2 g J _ Mat κ n hn hodd`. Take `⟨j₀, hj₀⟩` from `GlobalTheory.cutBy_graph_addition hL hL2 g J Mat κ n hn hodd`. Use `⟨j₀, fun j hj o _ b R _ _ _ β v Z M th sc q₀ hDen hFam hSm => ?_⟩` and prove the remaining obligations. Take `⟨Q, d, hQ⟩` from `hj₀ j hj o b`. Establish `: NeZero ((n ^ j) ^ 2)` using `⟨pow_ne_zero _ (pow_ne_zero _ hn.ne_zero)⟩`.

Take `⟨⟨I, p, hPR, hp⟩, -, hfib⟩` from `hFam`. Take `⟨I₂, M₂, th₂, hPR₂, hseg⟩` from `GlobalTheory.SegreCoord.exists_segre_coordinates R (Ix g ((n ^ j) ^ 2)) I Z M th hPR`. Establish `hP1` using `(GlobalTheory.ZM.projRep_projective_ample _ _ _ _ _ _ hPR).2.1`. Establish `hP2` using `(GlobalTheory.ZM.projRep_projective_ample _ _ _ _ _ _ hPR₂).2.1`. Establish `hS2 : Smooth (Z ⊗ Z).hom`.

Use `hSm` as an intermediate fact. Rewrite using `[Over.tensorObj_hom]`. Use `infer_instance`. Set `G : ∀ (K : Type) [Field K] (x : R →+* K), (pullback (Z ⊗ Z).hom (spMap x) ⟶ Z.left) → Prop` to `fun K _ x φ => ∃ (_ : IsAlgClosed K) (s : Sp K ⟶ Sp o) (t : TObj g ((n ^ j) ^ 2) J b s) (ψ : t.A.left ⟶ Z.left) (e : (t.A ⊗ t.A).left ⟶ pullback (Z ⊗ Z).hom (spMap x)), IsIso e ∧ Good b Mat κ β v x t ∧ Fib (n ^ 2) M th sc x t ψ ∧ IsSquare ψ (e ≫ pullback.fst _ _) ∧ e ≫ pullback.s …`. Establish `mk : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (s : Sp K ⟶ Sp o) (t : TObj g ((n ^ j) ^ 2) J b s) (ψ : t.A.left ⟶ Z.left), Good b Mat κ β v x t → Fib (n ^ 2) M th sc x t ψ → ∀ φ₂ : (t.A ⊗ t.A).left ⟶ (Z ⊗ Z).left, IsSquare ψ φ₂ → ∃ φ, G K x φ`.

Introduce `K _ _ x s t ψ hG hF φ₂ hsq`. Establish `hpb` using `GlobalTheory.ZM.BuildAdd.isPullback_square hF.1 φ₂ hsq`. Use `⟨hpb.isoPullback.inv ≫ (μ[t.A]).left ≫ ψ, inferInstance, s, t, ψ, hpb.isoPullback.hom, inferInstance, hG, hF, ?_, hpb.isoPullback_hom_snd, by simp⟩` and prove the remaining obligations. Rewrite using `[hpb.isoPullback_hom_fst]`. Conclude with `hsq`.

Establish `hGprop : ∀ (K : Type) [Field K] (x : R →+* K) (φ : pullback (Z ⊗ Z).hom (spMap x) ⟶ Z.left), G K x φ → φ ≫ Z.hom = pullback.snd _ _ ≫ spMap x ∧ CutBy (graphIdeal (pullback.snd (Z ⊗ Z).hom (spMap x)) M₂ th₂ (pullback.fst _ _) M th φ) Q d (fun (h : Ix g ((n ^ j) ^ 2) × Ix g ((n ^ j …`. Introduce `K _ x φ hφ`. Take `⟨_, s, t, ψ, e, _, hG, hF, hsq, hsn, heφ⟩` from `hφ`. Establish `hw : ψ ≫ Z.hom = t.A.hom ≫ spMap x` using `hF.1.w`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[← cancel_epi e, reassoc_of% heφ, reassoc_of% hsn, hw, ← Category.assoc, Over.w]`. Establish `hs : s = spMap (x.comp β)` using `hG.1.trans (spMap_comp x β).symm`. Substitute `hs` using the available equality. Take `⟨-, ⟨σ, hEmb, hσ⟩, -, hlab⟩` from `hF`. Take `⟨N₂, t₂, hN₂, hseg₂, heq⟩` from `GlobalTheory.ZM.BuildAdd.graph_transport x Z M th M₂ th₂ hPR₂.1 hseg t.A ψ _ σ hσ e hsq hsn φ heφ`.

Rewrite using `[← heq]`. Establish `hl : ∀ h, SecCoord _ σ (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab h ^ n ^ j)).left (fun a => x (p h a))`. Introduce `h`. Rewrite using `[hσ, ← Category.assoc, ← Over.comp_left, lift_snd, hlab h]`. Establish `hx : (sc h).left ≫ Z.hom = spMap (RingHom.id R)`.

Rewrite using `[Over.w]`. Simplify using `[Out.baseOver, spMap]`. Establish `hu` using `(hPR.2.1 R (RingHom.id R) (sc h).left (p h) hx (hp h)).1`. Conclude with `GlobalTheory.SegreCoord.secCoord_of_loc (GlobalTheory.SegreCoord.unimod_map hu x) ((GlobalTheory.SegreCoord.loc_of_secCoord (hp h)).baseChange x)`. Use `hQ K (x.comp β) t σ (fun h a => x (p h a)) N₂ t₂ hN₂ hEmb hseg₂ hl` as an intermediate fact.

Simplify using `only [map_mul]`. Conclude with `this`. Establish `hDense : DenseP {q | ∃ (K : Type) (_ : Field K) (x : R →+* K) (φ : _), RingHom.ker x = q ∧ G K x φ}`. Introduce `f hf`. Apply `hDen.1 f` to reduce the goal to its premises.

Introduce `q hq hqp`. Take `⟨K, _, _, x, t, hker, hsh, hth⟩` from `hq`. Establish `hG : Good b Mat κ β v x t` using `⟨rfl, hsh, hth⟩`. Take `⟨ψ, hψ⟩` from `hfib K x _ t hG`. Take `⟨φ₂, hsq⟩` from `GlobalTheory.ZM.BuildAdd.exists_isSquare hψ.1.w`.

Take `⟨φ, hφ⟩` from `mk K x _ t ψ hG hψ φ₂ hsq`. Conclude with `hf q ⟨K, inferInstance, x, φ, hker, hφ⟩ hqp`. Take `⟨K₀, _, _, x₀, t₀, hker₀, hsh₀, hth₀⟩` from `hDen.2`. Establish `hG₀ : Good b Mat κ β v x₀ t₀` using `⟨rfl, hsh₀, hth₀⟩`. Take `⟨ψ₀, hψ₀⟩` from `hfib K₀ x₀ _ t₀ hG₀`.

Take `⟨φ₂₀, hsq₀⟩` from `GlobalTheory.ZM.BuildAdd.exists_isSquare hψ₀.1.w`. Take `⟨φ₀, hφ₀⟩` from `mk K₀ x₀ _ t₀ ψ₀ hG₀ hψ₀ φ₂₀ hsq₀`. Take `⟨f, hf0, H⟩` from `GlobalTheory.ZM.NearBuild.exists_hom_of_graphs_of_isUnit R (Ix g ((n ^ j) ^ 2) × Ix g ((n ^ j) ^ 2)) (Ix g ((n ^ j) ^ 2)) (Ix g ((n ^ j) ^ 2) × Ix g ((n ^ j) ^ 2)) (Z ⊗ Z) Z I₂ I M₂ M th₂ th (fun h i => p h.1 i.1 * p h.2 i.2) (fun h c => p (h.1 + h.2) c) Q d G hPR₂ hPR hP2 hP1 hS …`. Use `⟨f, fun hf => hf0 ?_, ?_⟩` and prove the remaining obligations. Rewrite `hf` using `[← hker₀]`.

Conclude with `RingHom.mem_ker.mp hf`. Introduce `R' _ ρ hu Z' π hπ`. Take `⟨π₂, hsqπ⟩` from `GlobalTheory.ZM.BuildAdd.exists_isSquare hπ.w`. Establish `hpbπ` using `GlobalTheory.ZM.BuildAdd.isPullback_square hπ π₂ hsqπ`. Take `⟨F, hF, hU⟩` from `H R' ρ hu (Z' ⊗ Z').left π₂ (Z' ⊗ Z').hom hpbπ.w`.

Use `⟨Over.homMk (hπ.lift F (Z' ⊗ Z').hom hF) (hπ.lift_snd _ _ _), ?_⟩` and prove the remaining obligations. Introduce `K _ _ x s t φ hG hFib hφw φ₂ hsq`. Establish `hpb1 : IsPullback φ t.A.hom Z'.hom (spMap x)`. Use `IsPullback.of_right ?_ hφw hπ` and prove the remaining obligations. Rewrite using `[← spMap_comp]`.

Conclude with `hFib.1`. Establish `hpb2` using `GlobalTheory.ZM.BuildAdd.isPullback_square hpb1 φ₂ hsq`. Establish `hsq' : IsSquare (φ ≫ π) (φ₂ ≫ π₂)`. Prove the components needed by the constructor for the conclusion. Rewrite using `[Category.assoc, hsqπ.1, reassoc_of% hsq.1]`.

Rewrite using `[Category.assoc, hsqπ.2, reassoc_of% hsq.2]`. Establish `hpb3` using `GlobalTheory.ZM.BuildAdd.isPullback_square hFib.1 (φ₂ ≫ π₂) hsq'`. Establish `hGφ : G K (x.comp ρ) (hpb3.isoPullback.inv ≫ (μ[t.A]).left ≫ φ ≫ π)` using `⟨inferInstance, s, t, φ ≫ π, hpb3.isoPullback.hom, inferInstance, hG, hFib, by rw [hpb3.isoPullback_hom_fst]; exact hsq', hpb3.isoPullback_hom_snd, by simp⟩`. Establish `key` using `hU K (x.comp ρ) _ hGφ (hpb3.isoPullback.inv ≫ φ₂) (by rw [Category.assoc]; exact hpb3.isoPullback_inv_fst)`. Rewrite `key` using `[Category.assoc, cancel_epi]`.

Use `show φ₂ ≫ hπ.lift F (Z' ⊗ Z').hom hF = (μ[t.A]).left ≫ φ`. Apply `hπ.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, hπ.lift_fst, Category.assoc]`. Conclude with `key.symm`. Rewrite using `[Category.assoc, hπ.lift_snd, Category.assoc, hφw, ← Category.assoc, Over.w]`.

Conclude with `hpb2.w`.
-/
theorem exists_add_near : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (v : Ix g ((n ^ j) ^ 2) → R) (Z : Over (Sp R)) (M : LB Z.left) (th : Ix g ((n ^ j) ^ 2) → M.Sec) (sc : Ix g ((n ^ j) ^ 2) → (Out.baseOver (Sp R) ⟶ Z)) (q₀ : Ideal R), Den b Mat κ β v q₀ → Fam b Mat κ β v (n ^ 2) M th sc → Smooth Z.hom → ∃ f : R, f ∉ q₀ ∧ ∀ (R' : Type) [CommRing R'] (ρ : R →+* R'), IsUnit (ρ f) → ∀ (Z' : Over (Sp R')) (π : Z'.left ⟶ Z.left), IsPullback π Z'.hom Z.hom (spMap ρ) → ∃ mu : Z' ⊗ Z' ⟶ Z', AddOk b Mat κ β v (n ^ 2) M th sc ρ π mu := by
  intro hL hL2 g J _ Mat κ n hn hodd
  obtain ⟨j₀, hj₀⟩ := GlobalTheory.cutBy_graph_addition hL hL2 g J Mat κ n hn hodd
  refine ⟨j₀, fun j hj o _ b R _ _ _ β v Z M th sc q₀ hDen hFam hSm => ?_⟩
  obtain ⟨Q, d, hQ⟩ := hj₀ j hj o b
  have : NeZero ((n ^ j) ^ 2) := ⟨pow_ne_zero _ (pow_ne_zero _ hn.ne_zero)⟩
  obtain ⟨⟨I, p, hPR, hp⟩, -, hfib⟩ := hFam
  obtain ⟨I₂, M₂, th₂, hPR₂, hseg⟩ :=
    GlobalTheory.SegreCoord.exists_segre_coordinates R (Ix g ((n ^ j) ^ 2)) I Z M th hPR
  have hP1 := (GlobalTheory.ZM.projRep_projective_ample _ _ _ _ _ _ hPR).2.1
  have hP2 := (GlobalTheory.ZM.projRep_projective_ample _ _ _ _ _ _ hPR₂).2.1
  have hS2 : Smooth (Z ⊗ Z).hom := by
    have := hSm
    rw [Over.tensorObj_hom]
    infer_instance
  let G : ∀ (K : Type) [Field K] (x : R →+* K), (pullback (Z ⊗ Z).hom (spMap x) ⟶ Z.left) → Prop :=
    fun K _ x φ => ∃ (_ : IsAlgClosed K) (s : Sp K ⟶ Sp o) (t : TObj g ((n ^ j) ^ 2) J b s)
      (ψ : t.A.left ⟶ Z.left) (e : (t.A ⊗ t.A).left ⟶ pullback (Z ⊗ Z).hom (spMap x)), IsIso e ∧
      Good b Mat κ β v x t ∧ Fib (n ^ 2) M th sc x t ψ ∧ IsSquare ψ (e ≫ pullback.fst _ _) ∧
      e ≫ pullback.snd _ _ = (t.A ⊗ t.A).hom ∧ e ≫ φ = (μ[t.A]).left ≫ ψ
  have mk : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (s : Sp K ⟶ Sp o)
      (t : TObj g ((n ^ j) ^ 2) J b s) (ψ : t.A.left ⟶ Z.left), Good b Mat κ β v x t →
      Fib (n ^ 2) M th sc x t ψ → ∀ φ₂ : (t.A ⊗ t.A).left ⟶ (Z ⊗ Z).left, IsSquare ψ φ₂ → ∃ φ, G K x φ := by
    intro K _ _ x s t ψ hG hF φ₂ hsq
    have hpb := GlobalTheory.ZM.BuildAdd.isPullback_square hF.1 φ₂ hsq
    refine ⟨hpb.isoPullback.inv ≫ (μ[t.A]).left ≫ ψ, inferInstance, s, t, ψ, hpb.isoPullback.hom, inferInstance, hG, hF, ?_,
      hpb.isoPullback_hom_snd, by simp⟩
    rw [hpb.isoPullback_hom_fst]
    exact hsq
  have hGprop : ∀ (K : Type) [Field K] (x : R →+* K) (φ : pullback (Z ⊗ Z).hom (spMap x) ⟶ Z.left), G K x φ →
      φ ≫ Z.hom = pullback.snd _ _ ≫ spMap x ∧
      CutBy (graphIdeal (pullback.snd (Z ⊗ Z).hom (spMap x)) M₂ th₂ (pullback.fst _ _) M th φ) Q d
        (fun (h : Ix g ((n ^ j) ^ 2) × Ix g ((n ^ j) ^ 2)) (i : (Ix g ((n ^ j) ^ 2) × Ix g ((n ^ j) ^ 2)) × Ix g ((n ^ j) ^ 2)) =>
          x ((p h.1 i.1.1 * p h.2 i.1.2) * p (h.1 + h.2) i.2)) := by
    intro K _ x φ hφ
    obtain ⟨_, s, t, ψ, e, _, hG, hF, hsq, hsn, heφ⟩ := hφ
    have hw : ψ ≫ Z.hom = t.A.hom ≫ spMap x := hF.1.w
    refine ⟨?_, ?_⟩
    · rw [← cancel_epi e, reassoc_of% heφ, reassoc_of% hsn, hw, ← Category.assoc, Over.w]
    have hs : s = spMap (x.comp β) := hG.1.trans (spMap_comp x β).symm
    subst hs
    obtain ⟨-, ⟨σ, hEmb, hσ⟩, -, hlab⟩ := hF
    obtain ⟨N₂, t₂, hN₂, hseg₂, heq⟩ :=
      GlobalTheory.ZM.BuildAdd.graph_transport x Z M th M₂ th₂ hPR₂.1 hseg t.A ψ _ σ hσ e hsq hsn φ heφ
    rw [← heq]
    have hl : ∀ h, SecCoord _ σ (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab h ^ n ^ j)).left (fun a => x (p h a)) := by
      intro h
      rw [hσ, ← Category.assoc, ← Over.comp_left, lift_snd, hlab h]
      have hx : (sc h).left ≫ Z.hom = spMap (RingHom.id R) := by
        rw [Over.w]
        simp [Out.baseOver, spMap]
      have hu := (hPR.2.1 R (RingHom.id R) (sc h).left (p h) hx (hp h)).1
      exact GlobalTheory.SegreCoord.secCoord_of_loc (GlobalTheory.SegreCoord.unimod_map hu x)
        ((GlobalTheory.SegreCoord.loc_of_secCoord (hp h)).baseChange x)
    have := hQ K (x.comp β) t σ (fun h a => x (p h a)) N₂ t₂ hN₂ hEmb hseg₂ hl
    simp only [map_mul]
    exact this
  have hDense : DenseP {q | ∃ (K : Type) (_ : Field K) (x : R →+* K) (φ : _), RingHom.ker x = q ∧ G K x φ} := by
    intro f hf
    apply hDen.1 f
    intro q hq hqp
    obtain ⟨K, _, _, x, t, hker, hsh, hth⟩ := hq
    have hG : Good b Mat κ β v x t := ⟨rfl, hsh, hth⟩
    obtain ⟨ψ, hψ⟩ := hfib K x _ t hG
    obtain ⟨φ₂, hsq⟩ := GlobalTheory.ZM.BuildAdd.exists_isSquare hψ.1.w
    obtain ⟨φ, hφ⟩ := mk K x _ t ψ hG hψ φ₂ hsq
    exact hf q ⟨K, inferInstance, x, φ, hker, hφ⟩ hqp
  obtain ⟨K₀, _, _, x₀, t₀, hker₀, hsh₀, hth₀⟩ := hDen.2
  have hG₀ : Good b Mat κ β v x₀ t₀ := ⟨rfl, hsh₀, hth₀⟩
  obtain ⟨ψ₀, hψ₀⟩ := hfib K₀ x₀ _ t₀ hG₀
  obtain ⟨φ₂₀, hsq₀⟩ := GlobalTheory.ZM.BuildAdd.exists_isSquare hψ₀.1.w
  obtain ⟨φ₀, hφ₀⟩ := mk K₀ x₀ _ t₀ ψ₀ hG₀ hψ₀ φ₂₀ hsq₀
  obtain ⟨f, hf0, H⟩ := GlobalTheory.ZM.NearBuild.exists_hom_of_graphs_of_isUnit R
    (Ix g ((n ^ j) ^ 2) × Ix g ((n ^ j) ^ 2)) (Ix g ((n ^ j) ^ 2)) (Ix g ((n ^ j) ^ 2) × Ix g ((n ^ j) ^ 2))
    (Z ⊗ Z) Z I₂ I M₂ M th₂ th (fun h i => p h.1 i.1 * p h.2 i.2) (fun h c => p (h.1 + h.2) c) Q d G
    hPR₂ hPR hP2 hP1 hS2 hGprop hDense K₀ x₀ φ₀ hφ₀
  refine ⟨f, fun hf => hf0 ?_, ?_⟩
  · rw [← hker₀] at hf
    exact RingHom.mem_ker.mp hf
  intro R' _ ρ hu Z' π hπ
  obtain ⟨π₂, hsqπ⟩ := GlobalTheory.ZM.BuildAdd.exists_isSquare hπ.w
  have hpbπ := GlobalTheory.ZM.BuildAdd.isPullback_square hπ π₂ hsqπ
  obtain ⟨F, hF, hU⟩ := H R' ρ hu (Z' ⊗ Z').left π₂ (Z' ⊗ Z').hom hpbπ.w
  refine ⟨Over.homMk (hπ.lift F (Z' ⊗ Z').hom hF) (hπ.lift_snd _ _ _), ?_⟩
  intro K _ _ x s t φ hG hFib hφw φ₂ hsq
  have hpb1 : IsPullback φ t.A.hom Z'.hom (spMap x) := by
    refine IsPullback.of_right ?_ hφw hπ
    rw [← spMap_comp]
    exact hFib.1
  have hpb2 := GlobalTheory.ZM.BuildAdd.isPullback_square hpb1 φ₂ hsq
  have hsq' : IsSquare (φ ≫ π) (φ₂ ≫ π₂) := by
    constructor
    · rw [Category.assoc, hsqπ.1, reassoc_of% hsq.1]
    · rw [Category.assoc, hsqπ.2, reassoc_of% hsq.2]
  have hpb3 := GlobalTheory.ZM.BuildAdd.isPullback_square hFib.1 (φ₂ ≫ π₂) hsq'
  have hGφ : G K (x.comp ρ) (hpb3.isoPullback.inv ≫ (μ[t.A]).left ≫ φ ≫ π) :=
    ⟨inferInstance, s, t, φ ≫ π, hpb3.isoPullback.hom, inferInstance, hG, hFib,
      by rw [hpb3.isoPullback_hom_fst]; exact hsq', hpb3.isoPullback_hom_snd, by simp⟩
  have key := hU K (x.comp ρ) _ hGφ (hpb3.isoPullback.inv ≫ φ₂)
    (by rw [Category.assoc]; exact hpb3.isoPullback_inv_fst)
  rw [Category.assoc, cancel_epi] at key
  show φ₂ ≫ hπ.lift F (Z' ⊗ Z').hom hF = (μ[t.A]).left ≫ φ
  apply hπ.hom_ext
  · rw [Category.assoc, hπ.lift_fst, Category.assoc]
    exact key.symm
  · rw [Category.assoc, hπ.lift_snd, Category.assoc, hφw, ← Category.assoc, Over.w]
    exact hpb2.w

end GlobalTheory.ZM.NearBuild
end
