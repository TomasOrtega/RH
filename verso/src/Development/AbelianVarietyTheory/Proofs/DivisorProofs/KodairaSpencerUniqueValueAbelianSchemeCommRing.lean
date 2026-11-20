import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerMatrixUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DeRham

open GlobalTheory.Published GlobalTheory.Published.AbelianDeRham

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Establish `a₀` using `PolPull.isAbelianScheme_of_isGrpPullback hA h`. Establish `g₀` using `(smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback h.1 hg`. Establish `hL` using `(P.2.1 K A g a₀ g₀).1`. Use `letI : Algebra (DualNumber K) K := (TrivSqZeroExt.fstHom K K K).toRingHom.toAlgebra`. Take `⟨-, hF⟩` from `P.2.2.1 (DualNumber K) A' g hA hg K A i h`.

Take `⟨-, ⟨N, hN⟩, -⟩` from `P.2.1 (DualNumber K) A' g hA hg`. Take `⟨-, hproj, -⟩` from `P.1.prim hA hg`. Establish `su : Function.Surjective (TrivSqZeroExt.fstHom K K K).toRingHom` using `fun r => ⟨TrivSqZeroExt.inl r, rfl⟩`. Establish `rA` using `P.2.2.2.1 _ A' g hA hg _ (epsDP K) (isDPNilpotent_squareZero _) K _ su rfl A i h`. Establish `rB` using `P.2.2.2.1.crysToDR_bijective hA hg (κ := epsDP K) (isDPNilpotent_squareZero _) su rfl h`.

Set `φL : primDR A' →ₗ[DualNumber K] K` to `{ toFun := fun c => f ((bcMor h).pull c) map_add' := fun x y => by simp only [map_add] map_smul' := fun r c => by`. Rewrite using `[LinearMap.map_smulₛₗ, map_smul, smul_eq_mul, RingHom.id_apply, Algebra.smul_def] }`. Take `⟨u, hu⟩` from `Module.projective_lifting_property (Algebra.linearMap (DualNumber K) K) φL (fun r => ⟨TrivSqZeroExt.inl r, rfl⟩)`. Set `d' : HdR A'` to `u ∘ₗ N.projection (PrimitiveSubmodule A') hN.symm`. Establish `hd' : d' ∈ Fil A'`.

Rewrite using `[Fil, Submodule.mem_dualAnnihilator]`. Introduce `x hx`. Express the relevant statement in the definitionally equal form `u (N.projection (PrimitiveSubmodule A') hN.symm x) = 0`. Rewrite using `[Submodule.projection_apply_of_mem_right hN.symm hx, map_zero]`. Establish `fd' : ∀ x, (d' x).fst = f ((bcMor h).pull x)` using `fun x => by`.

Establish `e1 : ∀ y, (u y).fst = f ((bcMor h).pull y)` using `fun y => LinearMap.congr_fun hu y`. Establish `e2` using `Submodule.projection_add_projection_eq_self hN.symm x`. Establish `e3 : f ((bcMor h).pull ((PrimitiveSubmodule A').projection N hN.symm.symm x)) = 0`. Rewrite `hf` using `[Fil, hF]`. Conclude with `(Submodule.mem_dualAnnihilator _).1 hf _ (Submodule.subset_span ⟨_, Submodule.projection_apply_mem _ _, rfl⟩)`.

Express the relevant statement in the definitionally equal form `(u _).fst = _`. Rewrite using `[e1, ← add_zero (f ((bcMor h).pull _)), ← e3, ← map_add, ← map_add, e2]`. Take `⟨d, hd⟩` from `rB.2 d'`. Set `k : HdR A` to `{ toFun := fun c => (d ((constMor A).pull c)).snd map_add' := fun x y => by simp only [map_add, TrivSqZeroExt.snd_add] map_smul' := fun r c => by`. Rewrite using `[LinearMap.map_smulₛₗ, map_smul, smul_eq_mul, RingHom.id_apply, smul_eq_mul, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_mul]`.

Simplify using `}`. Take `⟨v, hv, -⟩` from `hL.1 k`. Use `⟨v, k, ⟨d, by rw [liftFil, Submodule.mem_comap, hd]; exact hd', fun c => ?_⟩, hv⟩` and prove the remaining obligations. Take `⟨x, hx⟩` from `rA.2 ((constMor A).pull c)`. Establish `red : (bcMor h).pull x = c`.

Rewrite using `[← GrpMor.pull_pull (liftMor (epsDP K) h) (redMor A) (bcMor h) (fun _ => rfl) (by simp) x, hx, redMor_constMor]`. Apply `TrivSqZeroExt.ext` to reduce the goal to its premises. Establish `e` using `fd' x`. Rewrite `e` using `[← hd, crysToDR_apply, hx, red]`. Rewrite using `[TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero]`.

Conclude with `e`. Rewrite using `[TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]`. Both sides reduce to the same expression.
-/
theorem IsKSValue.exists_of_isAbelianScheme_ring (P : AbelianDeRham) {K : Type} [CommRing K] {A : Over (Sp K)} [GrpObj A]
    {A' : Over (Sp (DualNumber K))} [GrpObj A'] {i : A.left ⟶ A'.left}
    (h : IsGrpPullback A A' (epsRed K) i) {g : ℕ} (hA : Semi.IsAbelianScheme A')
    (hg : SmoothOfRelativeDimension g A'.hom) {f : HdR A} (hf : f ∈ Fil A) : ∃ v, IsKSValue h f v := by
  have a₀ := PolPull.isAbelianScheme_of_isGrpPullback hA h
  have g₀ := (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback h.1 hg
  have hL := (P.2.1 K A g a₀ g₀).1
  letI : Algebra (DualNumber K) K := (TrivSqZeroExt.fstHom K K K).toRingHom.toAlgebra
  obtain ⟨-, hF⟩ := P.2.2.1 (DualNumber K) A' g hA hg K A i h
  obtain ⟨-, ⟨N, hN⟩, -⟩ := P.2.1 (DualNumber K) A' g hA hg
  obtain ⟨-, hproj, -⟩ := P.1.prim hA hg
  have su : Function.Surjective (TrivSqZeroExt.fstHom K K K).toRingHom :=
    fun r => ⟨TrivSqZeroExt.inl r, rfl⟩
  have rA := P.2.2.2.1 _ A' g hA hg _ (epsDP K) (isDPNilpotent_squareZero _) K _ su rfl A i h
  have rB := P.2.2.2.1.crysToDR_bijective hA hg (κ := epsDP K) (isDPNilpotent_squareZero _) su rfl h
  let φL : primDR A' →ₗ[DualNumber K] K :=
    { toFun := fun c => f ((bcMor h).pull c)
      map_add' := fun x y => by simp only [map_add]
      map_smul' := fun r c => by
        rw [LinearMap.map_smulₛₗ, map_smul, smul_eq_mul, RingHom.id_apply, Algebra.smul_def] }
  obtain ⟨u, hu⟩ := Module.projective_lifting_property (Algebra.linearMap (DualNumber K) K) φL
    (fun r => ⟨TrivSqZeroExt.inl r, rfl⟩)
  let d' : HdR A' := u ∘ₗ N.projection (PrimitiveSubmodule A') hN.symm
  have hd' : d' ∈ Fil A' := by
    rw [Fil, Submodule.mem_dualAnnihilator]
    intro x hx
    change u (N.projection (PrimitiveSubmodule A') hN.symm x) = 0
    rw [Submodule.projection_apply_of_mem_right hN.symm hx, map_zero]
  have fd' : ∀ x, (d' x).fst = f ((bcMor h).pull x) := fun x => by
    have e1 : ∀ y, (u y).fst = f ((bcMor h).pull y) := fun y => LinearMap.congr_fun hu y
    have e2 := Submodule.projection_add_projection_eq_self hN.symm x
    have e3 : f ((bcMor h).pull ((PrimitiveSubmodule A').projection N hN.symm.symm x)) = 0 := by
      rw [Fil, hF] at hf
      exact (Submodule.mem_dualAnnihilator _).1 hf _
        (Submodule.subset_span ⟨_, Submodule.projection_apply_mem _ _, rfl⟩)
    change (u _).fst = _
    rw [e1, ← add_zero (f ((bcMor h).pull _)), ← e3, ← map_add, ← map_add, e2]
  obtain ⟨d, hd⟩ := rB.2 d'
  let k : HdR A :=
    { toFun := fun c => (d ((constMor A).pull c)).snd
      map_add' := fun x y => by simp only [map_add, TrivSqZeroExt.snd_add]
      map_smul' := fun r c => by
        rw [LinearMap.map_smulₛₗ, map_smul, smul_eq_mul, RingHom.id_apply, smul_eq_mul,
          TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_mul]
        simp }
  obtain ⟨v, hv, -⟩ := hL.1 k
  refine ⟨v, k, ⟨d, by rw [liftFil, Submodule.mem_comap, hd]; exact hd', fun c => ?_⟩, hv⟩
  obtain ⟨x, hx⟩ := rA.2 ((constMor A).pull c)
  have red : (bcMor h).pull x = c := by
    rw [← GrpMor.pull_pull (liftMor (epsDP K) h) (redMor A) (bcMor h) (fun _ => rfl) (by simp) x, hx,
      redMor_constMor]
  apply TrivSqZeroExt.ext
  · have e := fd' x
    rw [← hd, crysToDR_apply, hx, red] at e
    rw [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero]
    exact e
  · rw [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
    rfl

/- English proof (translation)
Introduce `P K _ A _ A' _ i h g hA hg f hf`. Take `⟨v, hv⟩` from `IsKSValue.exists_of_isAbelianScheme_ring P h hA hg hf`. Conclude with `⟨v, hv, fun w hw => IsKSValue.unique P hA hg hw hv⟩`.
-/
theorem ksRegular_of_isAbelianScheme_ring : GlobalTheory.Published.AbelianDeRham → ∀ {K : Type} [CommRing K] {A : Over (Sp K)}
    [GrpObj A] {A' : Over (Sp (DualNumber K))} [GrpObj A'] {i : A.left ⟶ A'.left}
    (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) {g : ℕ}, Semi.IsAbelianScheme A' →
    SmoothOfRelativeDimension g A'.hom → KSRegular h := by
  intro P K _ A _ A' _ i h g hA hg f hf
  obtain ⟨v, hv⟩ := IsKSValue.exists_of_isAbelianScheme_ring P h hA hg hf
  exact ⟨v, hv, fun w hw => IsKSValue.unique P hA hg hw hv⟩

end GlobalTheory.DeRham
