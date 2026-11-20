import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DerRingInjective
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueBtOrderEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EmbeddingBaseChangeCompatStatement
import Development.WeilBound.CoreStatements.HodgeTatePoints.GeEmbSub
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderScalarExtensionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HenselianQuasiFiniteFinitePartStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsFinOpenSubOfFiniteStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderFlatBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatLocalExtensionExistsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFiniteBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DualLatticePointUniversalStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HomAddMulOfUnitSectionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderValueEvalStatement

noncomputable section
namespace PositivityTheory.HtPt.Ge.Tan
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.BT.Tan
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.LieEx

section Alg
variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B] (ε : B →ₐ[R] R)
  {V V' : Type} [AddCommGroup V] [Module R V] [Module Rᵐᵒᵖ V] [IsCentralScalar R V]
  [AddCommGroup V'] [Module R V'] [Module Rᵐᵒᵖ V'] [IsCentralScalar R V']

/- English proof (translation)
Establish `hz : ∀ x ∈ (RingHom.ker ε) ^ 2, (ρ x).snd = 0`. Introduce `x hx`. Rewrite `hx` using `[pow_two]`. Use `Submodule.mul_induction_on hx ?_ ?_` and prove the remaining obligations. Introduce `a ha b hb`.

Establish `h1 : (ρ a).fst = 0` using `(h a).trans ha`. Establish `h2 : (ρ b).fst = 0` using `(h b).trans hb`. Rewrite using `[map_mul, TrivSqZeroExt.snd_mul, h1, h2]`. Simplify using the standard rewrite rules. Introduce `a b ha hb`.

Rewrite using `[map_add, TrivSqZeroExt.snd_add, ha, hb, add_zero]`. Set `d : RingHom.ker ε →ₗ[R] V` to `{ toFun := fun f => (ρ f.1).snd map_add' := fun a b => by simp map_smul' := fun r a => by simp }`. Set `tC : RingHom.ker ε →ₗ[R] (RingHom.ker ε).Cotangent` to `{ toFun := fun f => (RingHom.ker ε).toCotangent f map_add' := fun a b => map_add _ a b map_smul' := fun r a => by`. Establish `: r • a = (algebraMap R B r) • a` using `(algebraMap_smul B r a).symm`. Rewrite using `[this, map_smul]`.

Conclude with `algebraMap_smul B r _ }`. Establish `hs : Function.Surjective tC` using `Ideal.toCotangent_surjective _`. Establish `hk : LinearMap.ker tC ≤ LinearMap.ker d`. Introduce `a ha`. Conclude with `hz _ ((Ideal.toCotangent_eq_zero _ _).1 ha)`.

Set `ψ : (RingHom.ker ε).Cotangent →ₗ[R] V` to `((LinearMap.ker tC).liftQ d hk) ∘ₗ (tC.quotKerEquivOfSurjective hs).symm.toLinearMap`. Establish `hψ : ∀ a, ψ (tC a) = d a`. Introduce `a`. Establish `: (tC.quotKerEquivOfSurjective hs).symm (tC a) = Submodule.Quotient.mk a`. Rewrite using `[LinearEquiv.symm_apply_eq]`.

Both sides reduce to the same expression. Simplify using `only [ψ, LinearMap.comp_apply, LinearEquiv.coe_coe, this]`. Both sides reduce to the same expression. Use `⟨ψ, AlgHom.ext fun f => ?_⟩` and prove the remaining obligations. Rewrite using `[derRing_apply]`.

Use `TrivSqZeroExt.ext ?_ ?_` and prove the remaining obligations. Simplify using `[h]`. Establish `: ψ ((RingHom.ker ε).toCotangent (augPart ε f)) = d (augPart ε f)` using `hψ _`. Simplify using `only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add, this]`. Express the relevant statement in the definitionally equal form `(ρ (f - algebraMap R B (ε f))).snd = _`.

Rewrite using `[map_sub, AlgHom.commutes, TrivSqZeroExt.snd_sub]`. Simplify using `[TrivSqZeroExt.algebraMap_eq_inl]`.
-/
theorem exists_der (ρ : B →ₐ[R] TrivSqZeroExt R V) (h : ∀ f, (ρ f).fst = ε f) :
    ∃ ψ : (RingHom.ker ε).Cotangent →ₗ[R] V, derRing ε ψ = ρ := by
  have hz : ∀ x ∈ (RingHom.ker ε) ^ 2, (ρ x).snd = 0 := by
    intro x hx
    rw [pow_two] at hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro a ha b hb
      have h1 : (ρ a).fst = 0 := (h a).trans ha
      have h2 : (ρ b).fst = 0 := (h b).trans hb
      rw [map_mul, TrivSqZeroExt.snd_mul, h1, h2]
      simp
    · intro a b ha hb
      rw [map_add, TrivSqZeroExt.snd_add, ha, hb, add_zero]
  let d : RingHom.ker ε →ₗ[R] V :=
    { toFun := fun f => (ρ f.1).snd
      map_add' := fun a b => by simp
      map_smul' := fun r a => by simp }
  let tC : RingHom.ker ε →ₗ[R] (RingHom.ker ε).Cotangent :=
    { toFun := fun f => (RingHom.ker ε).toCotangent f
      map_add' := fun a b => map_add _ a b
      map_smul' := fun r a => by
        have : r • a = (algebraMap R B r) • a := (algebraMap_smul B r a).symm
        rw [this, map_smul]
        exact algebraMap_smul B r _ }
  have hs : Function.Surjective tC := Ideal.toCotangent_surjective _
  have hk : LinearMap.ker tC ≤ LinearMap.ker d := by
    intro a ha
    exact hz _ ((Ideal.toCotangent_eq_zero _ _).1 ha)
  let ψ : (RingHom.ker ε).Cotangent →ₗ[R] V :=
    ((LinearMap.ker tC).liftQ d hk) ∘ₗ (tC.quotKerEquivOfSurjective hs).symm.toLinearMap
  have hψ : ∀ a, ψ (tC a) = d a := by
    intro a
    have : (tC.quotKerEquivOfSurjective hs).symm (tC a) = Submodule.Quotient.mk a := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    simp only [ψ, LinearMap.comp_apply, LinearEquiv.coe_coe, this]
    rfl
  refine ⟨ψ, AlgHom.ext fun f => ?_⟩
  rw [derRing_apply]
  refine TrivSqZeroExt.ext ?_ ?_
  · simp [h]
  · have : ψ ((RingHom.ker ε).toCotangent (augPart ε f)) = d (augPart ε f) := hψ _
    simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add, this]
    change (ρ (f - algebraMap R B (ε f))).snd = _
    rw [map_sub, AlgHom.commutes, TrivSqZeroExt.snd_sub]
    simp [TrivSqZeroExt.algebraMap_eq_inl]

/- English proof (translation)
Rewrite using `[derRing_apply, derRing_apply]`. Apply the tactic sequence `refine TrivSqZeroExt.ext ?_ ?_ <;> simp`.
-/
theorem derRing_comp (ψ : (RingHom.ker ε).Cotangent →ₗ[R] V) (π : V →ₗ[R] V') (f : B) :
    TrivSqZeroExt.map π (derRing ε ψ f) = derRing ε (π ∘ₗ ψ) f := by
  rw [derRing_apply, derRing_apply]
  refine TrivSqZeroExt.ext ?_ ?_ <;> simp
end Alg

end PositivityTheory.HtPt.Ge.Tan

noncomputable section
namespace PositivityTheory.HtPt.Ge.Tan
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.BT.Tan
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.LieEx

/- English proof (translation)
Rewrite using `[Hom.one_def, Over.comp_left, Over.toUnit_left]`.
-/
theorem one_left_eq {B : Scheme.{0}} {X M : Over B} [GrpObj M] : (1 : X ⟶ M).left = X.hom ≫ η[M].left := by
  rw [Hom.one_def, Over.comp_left, Over.toUnit_left]

section Rel
variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] (Γ : QFGroup R T)
  {S : Scheme.{0}} {G : Over S} [GrpObj G] {x : Spec (CommRingCat.of R) ⟶ S} {N : ℕ} {i : Γ.G.left ⟶ G.left}
  {j : Γ.G.left ⟶ Spec (CommRingCat.of (Γ.btOrder ⊤))}
  {V V' : Type} [AddCommGroup V] [Module R V] [Module Rᵐᵒᵖ V] [IsCentralScalar R V]
  [AddCommGroup V'] [Module R V'] [Module Rᵐᵒᵖ V'] [IsCentralScalar R V']

include Γ in
/- English proof (translation)
Set `w : Over.mk (Y.hom ≫ x) ⟶ G` to `Over.homMk ((1 : Y ⟶ Γ.G).left ≫ i) (by`. Express the relevant statement in the definitionally equal form `((1 : Y ⟶ Γ.G).left ≫ i) ≫ G.hom = Y.hom ≫ x`. Rewrite using `[Category.assoc, ht.isOver, ← Category.assoc, Over.w])`. Establish `h` using `ht.mul Y 1 1 w w rfl rfl`. Rewrite `h` using `[_root_.mul_one]`.

Establish `h1 : w * w = w * 1`. Rewrite using `[_root_.mul_one]`. Conclude with `Over.OverMorphism.ext h`. Establish `h2 : w = 1` using `mul_left_cancel h1`. Conclude with `congrArg CommaMorphism.left h2`.
-/
theorem unit_i (ht : Γ.IsTorsionAlong G x N i) (Y : Over (Spec (CommRingCat.of R))) :
    (1 : Y ⟶ Γ.G).left ≫ i = (1 : Over.mk (Y.hom ≫ x) ⟶ G).left := by
  let w : Over.mk (Y.hom ≫ x) ⟶ G := Over.homMk ((1 : Y ⟶ Γ.G).left ≫ i) (by
    change ((1 : Y ⟶ Γ.G).left ≫ i) ≫ G.hom = Y.hom ≫ x
    rw [Category.assoc, ht.isOver, ← Category.assoc, Over.w])
  have h := ht.mul Y 1 1 w w rfl rfl
  rw [_root_.mul_one] at h
  have h1 : w * w = w * 1 := by
    rw [_root_.mul_one]
    exact Over.OverMorphism.ext h
  have h2 : w = 1 := mul_left_cancel h1
  exact congrArg CommaMorphism.left h2

/- English proof (translation)
Establish `h` using `unit_i Γ ht (Over.mk (𝟙 _))`. Rewrite `h` using `[one_left_eq, one_left_eq]`. Simplify using `using h`.
-/
theorem unit_i' (ht : Γ.IsTorsionAlong G x N i) : η[Γ.G].left ≫ i = x ≫ η[G].left := by
  have h := unit_i Γ ht (Over.mk (𝟙 _))
  rw [one_left_eq, one_left_eq] at h
  simpa using h

/- English proof (translation)
Establish `h1 : (Γ.pt 1).left = (genPt R).hom ≫ η[Γ.G].left`. Rewrite using `[map_one, one_left_eq]`. Establish `h2` using `hj.pt 1`. Rewrite `h2` using `[h1, Category.assoc]`. Set `ρ` to `Spec.preimage (η[Γ.G].left ≫ j)`.

Establish `hρ : Spec.map ρ = η[Γ.G].left ≫ j` using `Spec.map_preimage _`. Rewrite using `[← hρ]`. Rewrite `h2` using `[← hρ]`. Express the relevant statement in the definitionally equal form `Spec.map _ ≫ Spec.map ρ = _ at h2`. Rewrite `h2` using `[← Spec.map_comp]`.

Establish `h3` using `Spec.map_injective h2`. Use `congr 1`. Apply `CommRingCat.hom_ext` to reduce the goal to its premises. Apply `RingHom.ext` to reduce the goal to its premises. Introduce `f`.

Establish `h4` using `congrArg (fun g => g.hom f) h3`. Conclude with `IsFractionRing.injective R (FractionRing R) h4`.
-/
theorem unit_j (hj : Γ.IsEmb (Γ.btOrder ⊤) j) :
    η[Γ.G].left ≫ j = Spec.map (CommRingCat.ofHom (ev1 Γ).toRingHom) := by
  have h1 : (Γ.pt 1).left = (genPt R).hom ≫ η[Γ.G].left := by
    rw [map_one, one_left_eq]
  have h2 := hj.pt 1
  rw [h1, Category.assoc] at h2
  let ρ := Spec.preimage (η[Γ.G].left ≫ j)
  have hρ : Spec.map ρ = η[Γ.G].left ≫ j := Spec.map_preimage _
  rw [← hρ]
  rw [← hρ] at h2
  change Spec.map _ ≫ Spec.map ρ = _ at h2
  rw [← Spec.map_comp] at h2
  have h3 := Spec.map_injective h2
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro f
  have h4 := congrArg (fun g => g.hom f) h3
  exact IsFractionRing.injective R (FractionRing R) h4

/- English proof (translation)
Introduce `p`. Set `q : PrimeSpectrum R` to `PrimeSpectrum.comap (algebraMap R (TrivSqZeroExt R V)) p`. Use `⟨q, PrimeSpectrum.ext (Ideal.ext fun a => ?_)⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `algebraMap R (TrivSqZeroExt R V) a.fst ∈ p.asIdeal ↔ a ∈ p.asIdeal`. Use `set b := algebraMap R (TrivSqZeroExt R V) a.fst with hb`.

Establish `h0 : (b - a).fst = 0` using `by simp [hb, TrivSqZeroExt.algebraMap_eq_inl]`. Establish `hm : b - a ∈ p.asIdeal`. Use `p.isPrime.mem_of_pow_mem 2 ?_` and prove the remaining obligations. Establish `: (b - a) ^ 2 = 0`. Rewrite using `[pow_two]`.

Apply the tactic sequence `refine TrivSqZeroExt.ext ?_ ?_ <;> simp [h0]`. Rewrite using `[this]`. Conclude with `zero_mem _`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Simplify using `using p.asIdeal.sub_mem h hm`. Introduce `h`. Simplify using `using p.asIdeal.add_mem hm h`.
-/
theorem zsec_surj : Function.Surjective (Spec.map (CommRingCat.ofHom
    (TrivSqZeroExt.fstHom R R V).toRingHom)) := by
  intro p
  let q : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R (TrivSqZeroExt R V)) p
  refine ⟨q, PrimeSpectrum.ext (Ideal.ext fun a => ?_)⟩
  change algebraMap R (TrivSqZeroExt R V) a.fst ∈ p.asIdeal ↔ a ∈ p.asIdeal
  set b := algebraMap R (TrivSqZeroExt R V) a.fst with hb
  have h0 : (b - a).fst = 0 := by simp [hb, TrivSqZeroExt.algebraMap_eq_inl]
  have hm : b - a ∈ p.asIdeal := by
    refine p.isPrime.mem_of_pow_mem 2 ?_
    have : (b - a) ^ 2 = 0 := by
      rw [pow_two]
      refine TrivSqZeroExt.ext ?_ ?_ <;> simp [h0]
    rw [this]; exact zero_mem _
  constructor
  · intro h; simpa using p.asIdeal.sub_mem h hm
  · intro h; simpa using p.asIdeal.add_mem hm h

/- English proof (translation)
Rewrite using `[← Spec.map_comp]`. Use `congr 1`. Apply `CommRingCat.hom_ext` to reduce the goal to its premises. Apply `RingHom.ext` to reduce the goal to its premises. Introduce `f`.

Conclude with `(congrArg TrivSqZeroExt.fst (derRing_apply (ev1 Γ) ψ f)).trans (by simp)`.
-/
theorem spec_fst_comp (ψ : omega (Γ.btOrder ⊤) →ₗ[R] V) :
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R V).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (derRing (ev1 Γ) ψ).toRingHom) =
    Spec.map (CommRingCat.ofHom (ev1 Γ).toRingHom) := by
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro f
  exact (congrArg TrivSqZeroExt.fst (derRing_apply (ev1 Γ) ψ f)).trans (by simp)

/- English proof (translation)
Rewrite using `[← Spec.map_comp]`. Use `congr 1`. Apply `CommRingCat.hom_ext` to reduce the goal to its premises. Apply `RingHom.ext` to reduce the goal to its premises. Introduce `r`.

Conclude with `(derRing (ev1 Γ) ψ).commutes r`.
-/
theorem spec_alg_comp (ψ : omega (Γ.btOrder ⊤) →ₗ[R] V) :
    Spec.map (CommRingCat.ofHom (derRing (ev1 Γ) ψ).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (Γ.btOrder ⊤))) =
    Spec.map (CommRingCat.ofHom (algebraMap R (TrivSqZeroExt R V))) := by
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact (derRing (ev1 Γ) ψ).commutes r

/- English proof (translation)
Take `⟨y', hy'⟩` from `(ht.kernel (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R (TrivSqZeroExt R V))))) v).1 hN`. Set `y : Spec (CommRingCat.of (TrivSqZeroExt R V)) ⟶ Γ.G.left` to `y'.left`. Establish `y1 : y ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (algebraMap R (TrivSqZeroExt R V)))` using `Over.w y'`. Establish `y3 : y ≫ i = v.left` using `hy'`. Set `ρ₀` to `Spec.preimage (y ≫ j)`.

Establish `hρ : Spec.map ρ₀ = y ≫ j` using `Spec.map_preimage _`. Establish `hc : CommRingCat.ofHom (algebraMap R (Γ.btOrder ⊤)) ≫ ρ₀ = CommRingCat.ofHom (algebraMap R (TrivSqZeroExt R V))`. Apply `Spec.map_injective` to reduce the goal to its premises. Rewrite using `[Spec.map_comp, hρ, Category.assoc, hj.isOver, y1]`. Set `ρ : (Γ.btOrder ⊤) →ₐ[R] TrivSqZeroExt R V` to `{ ρ₀.hom with commutes' := fun r => congrArg (fun g => g.hom r) hc }`.

Set `a` to `Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R V).toRingHom)`. Establish `ha : a ≫ Spec.map (CommRingCat.ofHom (algebraMap R (TrivSqZeroExt R V))) = 𝟙 _`. Rewrite using `[← Spec.map_comp, ← Spec.map_id]`. Use `congr 1`. Establish `e1 : a ≫ y = η[Γ.G].left`.

Use `ht.inj (Over.mk (𝟙 _)) (Over.homMk (a ≫ y) (by` as an intermediate fact. Express the relevant statement in the definitionally equal form `(a ≫ y) ≫ Γ.G.hom = 𝟙 _`. Rewrite using `[Category.assoc, y1, ha])) 1 (by`. Rewrite using `[one_left_eq]`. Simplify using `only [Over.homMk_left, Over.mk_hom, Category.id_comp, Category.assoc]`.

Rewrite using `[unit_i' Γ ht, y3]`. Use `congrArg Over.Hom.left h1` as an intermediate fact. Rewrite `this` using `[one_left_eq, Over.comp_left]`. Conclude with `this)`. Establish `h` using `congrArg Over.Hom.left this`.

Rewrite `h` using `[one_left_eq]`. Simplify using `using h`. Establish `hfst : ∀ f, (ρ f).fst = ev1 Γ f`. Establish `h2 : Spec.map (ρ₀ ≫ CommRingCat.ofHom (TrivSqZeroExt.fstHom R R V).toRingHom) = Spec.map (CommRingCat.ofHom (ev1 Γ).toRingHom)`. Rewrite using `[Spec.map_comp, hρ, ← Category.assoc, e1, unit_j Γ hj]`.

Establish `h3` using `Spec.map_injective h2`. Introduce `f`. Conclude with `congrArg (fun g => g.hom f) h3`. Take `⟨ψ, hψ⟩` from `exists_der (ev1 Γ) ρ hfst`. Use `⟨ψ, y, y1, ?_, y3⟩` and prove the remaining obligations.

Rewrite using `[hψ, ← hρ]`. Both sides reduce to the same expression.
-/
theorem rel_of_torsion (ht : Γ.IsTorsionAlong G x N i) (hj : Γ.IsEmb (Γ.btOrder ⊤) j)
    (v : ob x V ⟶ G) (h1 : zsec x ≫ v = 1) (hN : v ^ N = 1) :
    ∃ ψ : omega (Γ.btOrder ⊤) →ₗ[R] V, TanRel Γ i j ψ v := by
  obtain ⟨y', hy'⟩ := (ht.kernel (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R (TrivSqZeroExt R V))))) v).1 hN
  let y : Spec (CommRingCat.of (TrivSqZeroExt R V)) ⟶ Γ.G.left := y'.left
  have y1 : y ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (algebraMap R (TrivSqZeroExt R V))) := Over.w y'
  have y3 : y ≫ i = v.left := hy'
  let ρ₀ := Spec.preimage (y ≫ j)
  have hρ : Spec.map ρ₀ = y ≫ j := Spec.map_preimage _
  have hc : CommRingCat.ofHom (algebraMap R (Γ.btOrder ⊤)) ≫ ρ₀ =
      CommRingCat.ofHom (algebraMap R (TrivSqZeroExt R V)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hρ, Category.assoc, hj.isOver, y1]
  let ρ : (Γ.btOrder ⊤) →ₐ[R] TrivSqZeroExt R V :=
    { ρ₀.hom with
      commutes' := fun r => congrArg (fun g => g.hom r) hc }
  let a := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R V).toRingHom)
  have ha : a ≫ Spec.map (CommRingCat.ofHom (algebraMap R (TrivSqZeroExt R V))) = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
  have e1 : a ≫ y = η[Γ.G].left := by
    have := ht.inj (Over.mk (𝟙 _)) (Over.homMk (a ≫ y) (by
        change (a ≫ y) ≫ Γ.G.hom = 𝟙 _
        rw [Category.assoc, y1, ha])) 1 (by
      rw [one_left_eq]
      simp only [Over.homMk_left, Over.mk_hom, Category.id_comp, Category.assoc]
      rw [unit_i' Γ ht, y3]
      have := congrArg Over.Hom.left h1
      rw [one_left_eq, Over.comp_left] at this
      exact this)
    have h := congrArg Over.Hom.left this
    rw [one_left_eq] at h
    simpa using h
  have hfst : ∀ f, (ρ f).fst = ev1 Γ f := by
    have h2 : Spec.map (ρ₀ ≫ CommRingCat.ofHom (TrivSqZeroExt.fstHom R R V).toRingHom) =
        Spec.map (CommRingCat.ofHom (ev1 Γ).toRingHom) := by
      rw [Spec.map_comp, hρ, ← Category.assoc, e1, unit_j Γ hj]
    have h3 := Spec.map_injective h2
    intro f
    exact congrArg (fun g => g.hom f) h3
  obtain ⟨ψ, hψ⟩ := exists_der (ev1 Γ) ρ hfst
  refine ⟨ψ, y, y1, ?_, y3⟩
  rw [hψ, ← hρ]
  rfl

/- English proof (translation)
Take `⟨y, a, b, c⟩` from `h`. Take `⟨y', a', b', c'⟩` from `h'`. Establish `e` using `ht.inj (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R (TrivSqZeroExt R V))))) (Over.homMk y a) (Over.homMk y' a') (by simpa using c.trans c'.symm)`. Establish `e' : y = y'` using `congrArg CommaMorphism.left e`. Rewrite `b` using `[e', b']`.

Establish `h3` using `Spec.map_injective b`. Apply `derRing_injective (ev1 Γ)` to reduce the goal to its premises. Apply `AlgHom.ext` to reduce the goal to its premises. Introduce `f`. Conclude with `(congrArg (fun g => g.hom f) h3).symm`.
-/
theorem rel_unique (ht : Γ.IsTorsionAlong G x N i) {ψ ψ' : omega (Γ.btOrder ⊤) →ₗ[R] V} {v : ob x V ⟶ G}
    (h : TanRel Γ i j ψ v) (h' : TanRel Γ i j ψ' v) : ψ = ψ' := by
  obtain ⟨y, a, b, c⟩ := h
  obtain ⟨y', a', b', c'⟩ := h'
  have e := ht.inj (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R (TrivSqZeroExt R V))))) (Over.homMk y a)
    (Over.homMk y' a') (by simpa using c.trans c'.symm)
  have e' : y = y' := congrArg CommaMorphism.left e
  rw [e', b'] at b
  have h3 := Spec.map_injective b
  apply derRing_injective (ev1 Γ)
  apply AlgHom.ext
  intro f
  exact (congrArg (fun g => g.hom f) h3).symm

/- English proof (translation)
Take `⟨y, a, b, c⟩` from `h`. Use `⟨Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map π).toRingHom) ≫ y, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, a, ← Spec.map_comp]`. Use `congr 1`. Apply `CommRingCat.hom_ext` to reduce the goal to its premises.

Apply `RingHom.ext` to reduce the goal to its premises. Introduce `r`. Conclude with `(TrivSqZeroExt.map π).commutes r`. Rewrite using `[Category.assoc, b, ← Spec.map_comp]`. Use `congr 1`.

Apply `CommRingCat.hom_ext` to reduce the goal to its premises. Apply `RingHom.ext` to reduce the goal to its premises. Introduce `f`. Conclude with `derRing_comp (ev1 Γ) ψ π f`. Rewrite using `[Category.assoc, c]`.

Both sides reduce to the same expression.
-/
theorem rel_map {ψ : omega (Γ.btOrder ⊤) →ₗ[R] V} {v : ob x V ⟶ G} (h : TanRel Γ i j ψ v) (π : V →ₗ[R] V') :
    TanRel Γ i j (π ∘ₗ ψ) (hom x π ≫ v) := by
  obtain ⟨y, a, b, c⟩ := h
  refine ⟨Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map π).toRingHom) ≫ y, ?_, ?_, ?_⟩
  · rw [Category.assoc, a, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    exact (TrivSqZeroExt.map π).commutes r
  · rw [Category.assoc, b, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro f
    exact derRing_comp (ev1 Γ) ψ π f
  · rw [Category.assoc, c]
    rfl

end Rel

end PositivityTheory.HtPt.Ge.Tan

noncomputable section
namespace PositivityTheory.HtPt.Ge.Tan
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.BT.Tan
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.LieEx

/- English proof (translation)
The claim follows from `GlobalTheory.T.hom_add_mul_of_unit_section S R x G P V u hu f g`.
-/
theorem hom_add' {S : Scheme.{0}} {R : Type} [CommRing R] (x : Spec (CommRingCat.of R) ⟶ S) (G : Over S) [GrpObj G]
    {P V : Type} [AddCommGroup P] [Module R P] [Module Rᵐᵒᵖ P] [IsCentralScalar R P]
    [AddCommGroup V] [Module R V] [Module Rᵐᵒᵖ V] [IsCentralScalar R V]
    (u : ob x P ⟶ G) (hu : zsec x ≫ u = 1) (f g : P →ₗ[R] V) :
    hom x (f + g) ≫ u = (hom x f ≫ u) * (hom x g ≫ u) :=
  GlobalTheory.T.hom_add_mul_of_unit_section S R x G P V u hu f g

/- English proof (translation)
The claim follows from `GlobalTheory.T.bt_order_value_eval R T Γ j hj f s hs B y ρ h`.
-/
theorem val_of_emb {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] [Finite T] (Γ : QFGroup R T)
    {j : Γ.G.left ⟶ Spec (CommRingCat.of (Γ.btOrder ⊤))} (hj : Γ.IsEmb (Γ.btOrder ⊤) j)
    (f : Γ.btOrder ⊤) (s : Γ(Γ.G.left, ⊤)) (hs : Γ.HasValues s (f : T → R))
    {B : Type} [CommRing B] (y : Spec (CommRingCat.of B) ⟶ Γ.G.left) (ρ : (Γ.btOrder ⊤) →+* B)
    (h : y ≫ j = Spec.map (CommRingCat.ofHom ρ)) : valAt y ⊤ le_top s = ρ f :=
  GlobalTheory.T.bt_order_value_eval R T Γ j hj f s hs B y ρ h

/- English proof (translation)
Set `I : Ideal R` to `Ideal.span {(N : R)}`. Establish `hI : ∀ e, d e ∈ I` using `fun e => Ideal.Quotient.eq_zero_iff_mem.1 (h e)`. Set `g : L →ₗ[R] I` to `d.codRestrict I hI`. Set `p : R →ₗ[R] I` to `((N : R) • (LinearMap.id : R →ₗ[R] R)).codRestrict I (fun r => by`. Simplify using `using Ideal.mul_mem_right r I (Ideal.mem_span_singleton_self _))`.

Establish `hp : Function.Surjective p`. Introduce and unpack `⟨a, ha⟩`. Take `⟨r, rfl⟩` from `Ideal.mem_span_singleton'.1 ha`. Conclude with `⟨r, Subtype.ext (by simp [p, mul_comm])⟩`. Take `⟨u, hu⟩` from `Module.projective_lifting_property p g hp`.

Use `⟨u, ?_⟩` and prove the remaining obligations. Use extensionality with `e`. Use `congrArg Subtype.val (LinearMap.congr_fun hu e)` as an intermediate fact. Simplify `this.symm` using `[p, g]`.
-/
theorem dual_eq_smul {R L : Type} [CommRing R] [AddCommGroup L] [Module R L] [Module.Projective R L] (N : ℕ)
    (d : Module.Dual R L) (h : ∀ e, Ideal.Quotient.mk (Ideal.span {(N : R)}) (d e) = 0) :
    ∃ u : Module.Dual R L, d = N • u := by
  let I : Ideal R := Ideal.span {(N : R)}
  have hI : ∀ e, d e ∈ I := fun e => Ideal.Quotient.eq_zero_iff_mem.1 (h e)
  let g : L →ₗ[R] I := d.codRestrict I hI
  let p : R →ₗ[R] I := ((N : R) • (LinearMap.id : R →ₗ[R] R)).codRestrict I (fun r => by
    simpa using Ideal.mul_mem_right r I (Ideal.mem_span_singleton_self _))
  have hp : Function.Surjective p := by
    rintro ⟨a, ha⟩
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    exact ⟨r, Subtype.ext (by simp [p, mul_comm])⟩
  obtain ⟨u, hu⟩ := Module.projective_lifting_property p g hp
  refine ⟨u, ?_⟩
  ext e
  have := congrArg Subtype.val (LinearMap.congr_fun hu e)
  simpa [p, g] using this.symm

end PositivityTheory.HtPt.Ge.Tan

namespace PositivityTheory.HtPt.Ge.Tan
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.BT.Tan
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.LieEx

section Core
variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] (Γ : QFGroup R T)
  {S : Scheme.{0}} {G : Over S} [GrpObj G] {x : Spec (CommRingCat.of R) ⟶ S} {N : ℕ} {i : Γ.G.left ⟶ G.left}
  {j : Γ.G.left ⟶ Spec (CommRingCat.of (Γ.btOrder ⊤))}
  {P : Type} [AddCommGroup P] [Module R P] [Module Rᵐᵒᵖ P] [IsCentralScalar R P]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Rewrite using `[zero_smul, pow_zero, hom_zero, Category.assoc, hu, MonObj.comp_one]`. Consider the case `succ n ih => rw [succ_nsmul, hom_add' x G u hu, ih, pow_succ]`.
-/
theorem hom_nsmul (u : ob x P ⟶ G) (hu : zsec x ≫ u = 1) {V : Type} [AddCommGroup V] [Module R V] [Module Rᵐᵒᵖ V]
    [IsCentralScalar R V] (φ : P →ₗ[R] V) (n : ℕ) : hom x (n • φ) ≫ u = (hom x φ ≫ u) ^ n := by
  induction n with
  | zero =>
    rw [zero_smul, pow_zero, hom_zero, Category.assoc, hu, MonObj.comp_one]
  | succ n ih => rw [succ_nsmul, hom_add' x G u hu, ih, pow_succ]

/- English proof (translation)
Rewrite using `[hom_zero, Category.assoc, hu, MonObj.comp_one]`.
-/
theorem hom_zero_comp (u : ob x P ⟶ G) (hu : zsec x ≫ u = 1) {V : Type} [AddCommGroup V] [Module R V] [Module Rᵐᵒᵖ V]
    [IsCentralScalar R V] : hom x (0 : P →ₗ[R] V) ≫ u = 1 := by
  rw [hom_zero, Category.assoc, hu, MonObj.comp_one]

end Core

end PositivityTheory.HtPt.Ge.Tan
