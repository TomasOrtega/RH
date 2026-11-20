import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DerRingInjective
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueBtOrderEmbeddingStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderEmbeddingOpenImmersionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFiniteBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DualLatticePointUniversalStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HomAddMulOfUnitSectionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderValueEvalStatement

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.BT.Tan
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

end GlobalTheory.CompanionTheory.Ar.BT.Tan

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.BT.Tan
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
Use `set f₀ := Spec.map (CommRingCat.ofHom (derRing (ev1 Γ) ψ).toRingHom) with hf₀`. Establish `hr : Set.range f₀ ⊆ Set.range j`. Introduce and unpack `_ ⟨z, rfl⟩`. Take `⟨z', rfl⟩` from `zsec_surj (R := R) (V := V) z`. Establish `e` using `spec_fst_comp Γ ψ`.

Rewrite `e` using `[← unit_j Γ hj]`. Establish `e2 : f₀ (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R V).toRingHom) z') = j (η[Γ.G].left z')`. Conclude with `congrArg (fun k : Spec (CommRingCat.of R) ⟶ _ => k z') e`. Conclude with `⟨_, e2.symm⟩`. Set `y` to `IsOpenImmersion.lift j f₀ hr`.

Establish `yj : y ≫ j = f₀` using `IsOpenImmersion.lift_fac j f₀ hr`. Establish `y1 : y ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (algebraMap R (TrivSqZeroExt R V)))`. Rewrite using `[← hj.isOver, ← Category.assoc, yj]`. Conclude with `spec_alg_comp Γ ψ`. Set `v : ob x V ⟶ G` to `Over.homMk (y ≫ i) (by`.

Express the relevant statement in the definitionally equal form `(y ≫ i) ≫ G.hom = _ ≫ x`. Rewrite using `[Category.assoc, ht.isOver, ← Category.assoc, y1])`. Use `⟨v, ?_, ?_, y, y1, yj, rfl⟩` and prove the remaining obligations. Establish `e1 : (zsec x : Over.mk x ⟶ ob x V).left ≫ y = η[Γ.G].left`. Rewrite using `[← cancel_mono j, Category.assoc, yj, unit_j Γ hj]`.

Conclude with `spec_fst_comp Γ ψ`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[one_left_eq, Over.comp_left]`. Express the relevant statement in the definitionally equal form `(zsec x : Over.mk x ⟶ ob x V).left ≫ y ≫ i = x ≫ _`. Rewrite using `[← Category.assoc, e1, unit_i' Γ ht]`.

Conclude with `(ht.kernel (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R (TrivSqZeroExt R V))))) v).2 ⟨Over.homMk y y1, rfl⟩`.
-/
theorem rel_exists (ht : Γ.IsTorsionAlong G x N i) (hj : Γ.IsEmb (Γ.btOrder ⊤) j) [IsOpenImmersion j]
    (ψ : omega (Γ.btOrder ⊤) →ₗ[R] V) :
    ∃ v : ob x V ⟶ G, zsec x ≫ v = 1 ∧ v ^ N = 1 ∧ TanRel Γ i j ψ v := by
  set f₀ := Spec.map (CommRingCat.ofHom (derRing (ev1 Γ) ψ).toRingHom) with hf₀
  have hr : Set.range f₀ ⊆ Set.range j := by
    rintro _ ⟨z, rfl⟩
    obtain ⟨z', rfl⟩ := zsec_surj (R := R) (V := V) z
    have e := spec_fst_comp Γ ψ
    rw [← unit_j Γ hj] at e
    have e2 : f₀ (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R V).toRingHom) z') = j (η[Γ.G].left z') := by
      exact congrArg (fun k : Spec (CommRingCat.of R) ⟶ _ => k z') e
    exact ⟨_, e2.symm⟩
  let y := IsOpenImmersion.lift j f₀ hr
  have yj : y ≫ j = f₀ := IsOpenImmersion.lift_fac j f₀ hr
  have y1 : y ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (algebraMap R (TrivSqZeroExt R V))) := by
    rw [← hj.isOver, ← Category.assoc, yj]
    exact spec_alg_comp Γ ψ
  let v : ob x V ⟶ G := Over.homMk (y ≫ i) (by
    change (y ≫ i) ≫ G.hom = _ ≫ x
    rw [Category.assoc, ht.isOver, ← Category.assoc, y1])
  refine ⟨v, ?_, ?_, y, y1, yj, rfl⟩
  · have e1 : (zsec x : Over.mk x ⟶ ob x V).left ≫ y = η[Γ.G].left := by
      rw [← cancel_mono j, Category.assoc, yj, unit_j Γ hj]
      exact spec_fst_comp Γ ψ
    apply Over.OverMorphism.ext
    rw [one_left_eq, Over.comp_left]
    change (zsec x : Over.mk x ⟶ ob x V).left ≫ y ≫ i = x ≫ _
    rw [← Category.assoc, e1, unit_i' Γ ht]
  · exact (ht.kernel (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R (TrivSqZeroExt R V))))) v).2
      ⟨Over.homMk y y1, rfl⟩

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
Take `⟨y, a, b, c⟩` from `h`. Take `⟨y', a', b', c'⟩` from `h'`. Establish `e : y = y'` using `by rw [← cancel_mono j, b, b']`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[← c, ← c', e]`.
-/
theorem rel_eq [IsOpenImmersion j] {ψ : omega (Γ.btOrder ⊤) →ₗ[R] V} {v v' : ob x V ⟶ G}
    (h : TanRel Γ i j ψ v) (h' : TanRel Γ i j ψ v') : v = v' := by
  obtain ⟨y, a, b, c⟩ := h
  obtain ⟨y', a', b', c'⟩ := h'
  have e : y = y' := by rw [← cancel_mono j, b, b']
  apply Over.OverMorphism.ext
  rw [← c, ← c', e]

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

end GlobalTheory.CompanionTheory.Ar.BT.Tan

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.BT.Tan
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

end GlobalTheory.CompanionTheory.Ar.BT.Tan

namespace GlobalTheory.CompanionTheory.Ar.BT.Tan
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

/- English proof (translation)
Use `letI : Module Rᵐᵒᵖ (omega (Γ.btOrder ⊤)) := opMod R _`. Use `haveI : IsCentralScalar R (omega (Γ.btOrder ⊤)) := opCentral R _`. Take `⟨v₀, hv₀, hvN, hrel⟩` from `rel_exists Γ ht hj (LinearMap.id : omega (Γ.btOrder ⊤) →ₗ[R] omega (Γ.btOrder ⊤))`. Take `⟨θ, hθ, -⟩` from `huniv _ v₀ hv₀`. Establish `nat : ∀ (V : Type) [AddCommGroup V] [Module R V] [Module Rᵐᵒᵖ V] [IsCentralScalar R V] (ψ : omega (Γ.btOrder ⊤) →ₗ[R] V), TanRel Γ i j ψ (hom x (ψ ∘ₗ θ) ≫ u)`.

Introduce `V _ _ _ _ ψ`. Use `rel_map Γ hrel ψ` as an intermediate fact. Rewrite `this` using `[LinearMap.comp_id, ← hθ, ← Category.assoc, LieEx.hom_comp]`. Then use the resulting hypothesis. Establish `zero : ∀ (V : Type) [AddCommGroup V] [Module R V] [Module Rᵐᵒᵖ V] [IsCentralScalar R V] (ψ : omega (Γ.btOrder ⊤) →ₗ[R] V), ψ ∘ₗ θ = 0 → ψ = 0`. Introduce `V _ _ _ _ ψ h`.

Establish `h1` using `nat V ψ`. Establish `h2` using `nat V 0`. Rewrite `h1` using `[h]`. Rewrite `h2` using `[LinearMap.zero_comp]`. Conclude with `rel_unique Γ ht h1 h2`.

Establish `hN : N • θ = 0`. Establish `h1 : hom x (N • θ) ≫ u = 1` using `by rw [hom_nsmul u hu, hθ, hvN]`. Establish `h2 : hom x (0 : P →ₗ[R] omega (Γ.btOrder ⊤)) ≫ u = 1` using `hom_zero_comp u hu`. Establish `hz : zsec x ≫ (1 : ob x (omega (Γ.btOrder ⊤)) ⟶ G) = 1` using `MonObj.comp_one _`. Conclude with `(huniv _ 1 hz).unique h1 h2`.

Use `⟨θ, ?_, hN, ?_⟩` and prove the remaining obligations. Use `letI : Module Rᵐᵒᵖ (omega (Γ.btOrder ⊤) ⧸ LinearMap.range θ) := opMod R _ haveI : IsCentralScalar R (omega (Γ.btOrder ⊤) ⧸ LinearMap.range θ) := opCentral R _`. Use `zero _ (LinearMap.range θ).mkQ (by` as an intermediate fact. Use extensionality with `w`. Use the proof step `simp)`.

Rewrite using `[← LinearMap.range_eq_top, ← Submodule.ker_mkQ (LinearMap.range θ), this, LinearMap.ker_zero]`. Introduce `V _ _ _ _ φ hφ`. Establish `h1 : zsec x ≫ hom x φ ≫ u = 1` using `by rw [← Category.assoc, zsec_hom, hu]`. Establish `h2 : (hom x φ ≫ u) ^ N = 1` using `by rw [← hom_nsmul u hu, hφ, hom_zero_comp u hu]`. Take `⟨ψ, hψ⟩` from `rel_of_torsion Γ ht hj _ h1 h2`.

Establish `h3` using `rel_eq Γ hψ (nat V ψ)`. Use `⟨ψ, (huniv V _ h1).unique h3.symm rfl, hψ⟩` and prove the remaining obligations.
-/
theorem exists_theta (ht : Γ.IsTorsionAlong G x N i) (hj : Γ.IsEmb (Γ.btOrder ⊤) j) [IsOpenImmersion j]
    (u : ob x P ⟶ G) (hu : zsec x ≫ u = 1)
    (huniv : ∀ (V : Type) [AddCommGroup V] [Module R V] [Module Rᵐᵒᵖ V] [IsCentralScalar R V] (v : ob x V ⟶ G),
      zsec x ≫ v = 1 → ∃! φ : P →ₗ[R] V, hom x φ ≫ u = v) :
    ∃ θ : P →ₗ[R] omega (Γ.btOrder ⊤), Function.Surjective θ ∧ N • θ = 0 ∧
      ∀ (V : Type) [AddCommGroup V] [Module R V] [Module Rᵐᵒᵖ V] [IsCentralScalar R V] (φ : P →ₗ[R] V), N • φ = 0 →
        ∃ ψ : omega (Γ.btOrder ⊤) →ₗ[R] V, ψ ∘ₗ θ = φ ∧ TanRel Γ i j ψ (hom x φ ≫ u) := by
  letI : Module Rᵐᵒᵖ (omega (Γ.btOrder ⊤)) := opMod R _
  haveI : IsCentralScalar R (omega (Γ.btOrder ⊤)) := opCentral R _
  obtain ⟨v₀, hv₀, hvN, hrel⟩ := rel_exists Γ ht hj (LinearMap.id : omega (Γ.btOrder ⊤) →ₗ[R] omega (Γ.btOrder ⊤))
  obtain ⟨θ, hθ, -⟩ := huniv _ v₀ hv₀
  have nat : ∀ (V : Type) [AddCommGroup V] [Module R V] [Module Rᵐᵒᵖ V] [IsCentralScalar R V]
      (ψ : omega (Γ.btOrder ⊤) →ₗ[R] V), TanRel Γ i j ψ (hom x (ψ ∘ₗ θ) ≫ u) := by
    intro V _ _ _ _ ψ
    have := rel_map Γ hrel ψ
    rwa [LinearMap.comp_id, ← hθ, ← Category.assoc, LieEx.hom_comp] at this
  have zero : ∀ (V : Type) [AddCommGroup V] [Module R V] [Module Rᵐᵒᵖ V] [IsCentralScalar R V]
      (ψ : omega (Γ.btOrder ⊤) →ₗ[R] V), ψ ∘ₗ θ = 0 → ψ = 0 := by
    intro V _ _ _ _ ψ h
    have h1 := nat V ψ
    have h2 := nat V 0
    rw [h] at h1
    rw [LinearMap.zero_comp] at h2
    exact rel_unique Γ ht h1 h2
  have hN : N • θ = 0 := by
    have h1 : hom x (N • θ) ≫ u = 1 := by rw [hom_nsmul u hu, hθ, hvN]
    have h2 : hom x (0 : P →ₗ[R] omega (Γ.btOrder ⊤)) ≫ u = 1 := hom_zero_comp u hu
    have hz : zsec x ≫ (1 : ob x (omega (Γ.btOrder ⊤)) ⟶ G) = 1 := MonObj.comp_one _
    exact (huniv _ 1 hz).unique h1 h2
  refine ⟨θ, ?_, hN, ?_⟩
  · letI : Module Rᵐᵒᵖ (omega (Γ.btOrder ⊤) ⧸ LinearMap.range θ) := opMod R _
    haveI : IsCentralScalar R (omega (Γ.btOrder ⊤) ⧸ LinearMap.range θ) := opCentral R _
    have := zero _ (LinearMap.range θ).mkQ (by
      ext w
      simp)
    rw [← LinearMap.range_eq_top, ← Submodule.ker_mkQ (LinearMap.range θ), this, LinearMap.ker_zero]
  · intro V _ _ _ _ φ hφ
    have h1 : zsec x ≫ hom x φ ≫ u = 1 := by rw [← Category.assoc, zsec_hom, hu]
    have h2 : (hom x φ ≫ u) ^ N = 1 := by rw [← hom_nsmul u hu, hφ, hom_zero_comp u hu]
    obtain ⟨ψ, hψ⟩ := rel_of_torsion Γ ht hj _ h1 h2
    have h3 := rel_eq Γ hψ (nat V ψ)
    refine ⟨ψ, (huniv V _ h1).unique h3.symm rfl, hψ⟩

end Core

/- English proof (translation)
Introduce `R _ _ _ _ T _ _ Γ S G _ _ x N i ht hsm L _ _ M`. Use `haveI := hsm`. Take `⟨j, hj, -⟩` from `GlobalTheory.T.existsUnique_btOrder_embedding R T Γ`. Take `⟨hop, -⟩` from `GlobalTheory.T.btOrder_embedding_open_immersion R T Γ j hj`. Use `haveI := hop`.

Take `⟨-, hproj, -⟩` from `GlobalTheory.T.lie_model_finite_base_change S G R x L M`. Use `haveI := hproj`. Take `⟨u, hu, hupin, huniv⟩` from `GlobalTheory.T.dual_lattice_point_universal S G R x L M`. Take `⟨θ, hsurj, hNθ, hlift⟩` from `exists_theta Γ ht hj u hu huniv`. Establish `hθN : ∀ w', θ (N • w') = 0` using `fun w' => by`.

Use `LinearMap.congr_fun hNθ w'` as an intermediate fact. Simplify using `using this`. Establish `hker : ∀ w, θ w = 0 ↔ ∃ u', w = N • u'`. Introduce `w`. Prove the components needed by the constructor for the conclusion.

Introduce `hw`. Set `W : Submodule R (Module.Dual R L)` to `LinearMap.range ((N : R) • (LinearMap.id : Module.Dual R L →ₗ[R] Module.Dual R L))`. Establish `h0 : N • W.mkQ = 0`. Use extensionality with `w'`. Simplify using `only [LinearMap.smul_apply, LinearMap.zero_apply, LinearMap.comp_apply]`.

Conclude with `(map_nsmul W.mkQ N w').symm.trans ((Submodule.Quotient.mk_eq_zero W).2 ⟨w', by simp [Nat.cast_smul_eq_nsmul]⟩)`. Take `⟨ψ, hψ, -⟩` from `hlift _ W.mkQ h0`. Establish `h1 : W.mkQ w = 0`. Rewrite using `[← hψ, LinearMap.comp_apply, hw, map_zero]`. Rewrite `h1` using `[Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`.

Take `⟨u', rfl⟩` from `h1`. Conclude with `⟨u', by simp [Nat.cast_smul_eq_nsmul]⟩`. Introduce and unpack `⟨u', rfl⟩`. Conclude with `hθN u'`. Establish `hkey : ∀ e : L, ∃ ψ : omega (Γ.btOrder ⊤) →ₗ[R] (R ⧸ Ideal.span {(N : R)}), (∀ w, ψ (θ w) = Ideal.Quotient.mk (Ideal.span {(N : R)}) (w e)) ∧ ∃ v : Spec (CommRingCat.of (DualNumber (R ⧸ Ideal.span {(N : R)}))) ⟶ Γ.G.left, v ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom ((algebraMap (R …`.

Introduce `e`. Set `mkL : R →ₗ[R] (R ⧸ Ideal.span {(N : R)})` to `(Ideal.Quotient.mkₐ R (Ideal.span {(N : R)})).toLinearMap`. Set `φ : Module.Dual R L →ₗ[R] (R ⧸ Ideal.span {(N : R)})` to `mkL ∘ₗ Module.Dual.eval R L e`. Establish `h0 : N • φ = 0`. Use extensionality with `w'`.

Simplify using `only [φ, mkL, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.zero_apply]`. Rewrite using `[← map_nsmul, ← Nat.cast_smul_eq_nsmul R, AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, smul_eq_mul]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)`. Take `⟨ψ, hψ, y, y1, y2, y3⟩` from `hlift _ φ h0`. Use `⟨ψ, fun w => by simpa [φ, mkL] using LinearMap.congr_fun hψ w, Spec.map (CommRingCat.ofHom (kap _).toRingHom) ≫ y, ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Category.assoc, y1, ← Spec.map_comp]`. Use `congr 1`. Use extensionality with `r : 2`. Conclude with `kap_algebraMap _ r`. Establish `e1 : hom x φ ≫ u = hom x mkL ≫ M.pt e`.

Rewrite using `[← hupin e, ← Category.assoc, LieEx.hom_comp]`. Rewrite using `[Category.assoc, y3, e1]`. Express the relevant statement in the definitionally equal form `_ ≫ Spec.map _ ≫ (M.pt e).left = _`. Establish `e2 : CommRingCat.ofHom (TrivSqZeroExt.map mkL).toRingHom ≫ CommRingCat.ofHom (kap (Ideal.span {(N : R)})).toRingHom = CommRingCat.ofHom (dualMap (Ideal.Quotient.mk (Ideal.span {(N : R)})))`. Apply `CommRingCat.hom_ext` to reduce the goal to its premises.

Apply `RingHom.ext` to reduce the goal to its premises. Introduce `a`. Conclude with `kap_map _ a`. Rewrite using `[← Category.assoc, ← Spec.map_comp, e2]`. Rewrite using `[Category.assoc, y2, ← Spec.map_comp]`.

Both sides reduce to the same expression. Establish `huniq : ∀ (e : L) (v v' : Spec (CommRingCat.of (DualNumber (R ⧸ Ideal.span {(N : R)}))) ⟶ Γ.G.left), v ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom ((algebraMap (R ⧸ Ideal.span {(N : R)}) (DualNumber (R ⧸ Ideal.span {(N : R)}))).comp (Ideal.Quotient.mk _))) → v' ≫ Γ.G.hom = Spec.map ( …`. Introduce `e v v' h1 h1' h2 h2'`. Use `ht.inj (Over.mk (Spec.map (CommRingCat.ofHom ((algebraMap (R ⧸ Ideal.span {(N : R)}) (DualNumber (R ⧸ Ideal.span {(N : R)}))).comp (Ideal.Quotient.mk _))))) (Over.homMk v h1) (Over.homMk v' h1') (by simpa using h2.trans h2'.symm)` as an intermediate fact. Conclude with `congrArg CommaMorphism.left this`.

Use `⟨θ, hsurj, hker, ?_⟩` and prove the remaining obligations. Introduce `f w s hs`. Establish `hval : ∀ (ψ : omega (Γ.btOrder ⊤) →ₗ[R] (R ⧸ Ideal.span {(N : R)})) (v : Spec (CommRingCat.of (DualNumber (R ⧸ Ideal.span {(N : R)}))) ⟶ Γ.G.left), v ≫ j = Spec.map (CommRingCat.ofHom ((kap (Ideal.span {(N : R)})).toRingHom.comp (derRing (ev1 Γ) ψ).toRingHom)) → valAt v ⊤ le_top …`. Introduce `ψ v hv`. Rewrite using `[val_of_emb Γ hj f.1 s hs v _ hv]`.

Express the relevant statement in the definitionally equal form `kap _ (derRing (ev1 Γ) ψ f.1) = _`. Rewrite using `[derRing_of_mem (ev1 Γ) ψ f, kap_inr]`. Both sides reduce to the same expression. Prove the components needed by the constructor for the conclusion. Introduce `hw e v h1 h2`.

Take `⟨ψ, hψ, v', h1', h2', h3'⟩` from `hkey e`. Rewrite using `[huniq e v v' h1 h1' h2 h2', hval ψ v' h3', ← hw, hψ]`. Introduce `H`. Take `⟨w₀, hw₀⟩` from `hsurj ((augIdeal (Γ.btOrder ⊤)).toCotangent f)`. Establish `hd : ∀ e, Ideal.Quotient.mk (Ideal.span {(N : R)}) ((w - w₀) e) = 0`.

Introduce `e`. Take `⟨ψ, hψ, v', h1', h2', h3'⟩` from `hkey e`. Establish `a1` using `H e v' h1' h2'`. Rewrite `a1` using `[hval ψ v' h3', ← hw₀, hψ]`. Establish `a2` using `TrivSqZeroExt.inr_injective a1`.

Rewrite using `[LinearMap.sub_apply, map_sub, a2, sub_self]`. Take `⟨u', hu'⟩` from `dual_eq_smul N (w - w₀) hd`. Establish `: θ (w - w₀) = 0` using `(hker _).2 ⟨u', hu'⟩`. Rewrite `this` using `[map_sub, sub_eq_zero]`. Rewrite using `[this, hw₀]`.
-/
theorem omega_canon : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → Smooth G.hom → ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L), ∃ θ : Module.Dual R L →ₗ[R] omega (Γ.btOrder ⊤), Function.Surjective θ ∧ (∀ w, θ w = 0 ↔ ∃ u, w = N • u) ∧ ∀ (f : augIdeal (Γ.btOrder ⊤)) (w : Module.Dual R L) (s : Γ(Γ.G.left, ⊤)), Γ.HasValues s (f.1.1 : T → R) → (θ w = (augIdeal (Γ.btOrder ⊤)).toCotangent f ↔ ∀ (e : L) (v : Spec (CommRingCat.of (DualNumber (R ⧸ Ideal.span {(N : R)}))) ⟶ Γ.G.left), v ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom ((algebraMap (R ⧸ Ideal.span {(N : R)}) (DualNumber (R ⧸ Ideal.span {(N : R)}))).comp (Ideal.Quotient.mk _))) → v ≫ i = Spec.map (CommRingCat.ofHom (dualMap (Ideal.Quotient.mk (Ideal.span {(N : R)})))) ≫ (M.pt e).left → valAt v ⊤ le_top s = TrivSqZeroExt.inr (Ideal.Quotient.mk (Ideal.span {(N : R)}) (w e))) := by
  intro R _ _ _ _ T _ _ Γ S G _ _ x N i ht hsm L _ _ M
  haveI := hsm
  obtain ⟨j, hj, -⟩ := GlobalTheory.T.existsUnique_btOrder_embedding R T Γ
  obtain ⟨hop, -⟩ := GlobalTheory.T.btOrder_embedding_open_immersion R T Γ j hj
  haveI := hop
  obtain ⟨-, hproj, -⟩ := GlobalTheory.T.lie_model_finite_base_change S G R x L M
  haveI := hproj
  obtain ⟨u, hu, hupin, huniv⟩ := GlobalTheory.T.dual_lattice_point_universal S G R x L M
  obtain ⟨θ, hsurj, hNθ, hlift⟩ := exists_theta Γ ht hj u hu huniv
  have hθN : ∀ w', θ (N • w') = 0 := fun w' => by
    have := LinearMap.congr_fun hNθ w'
    simpa using this
  have hker : ∀ w, θ w = 0 ↔ ∃ u', w = N • u' := by
    intro w
    constructor
    · intro hw
      let W : Submodule R (Module.Dual R L) := LinearMap.range ((N : R) • (LinearMap.id : Module.Dual R L →ₗ[R] Module.Dual R L))
      have h0 : N • W.mkQ = 0 := by
        ext w'
        simp only [LinearMap.smul_apply, LinearMap.zero_apply, LinearMap.comp_apply]
        exact (map_nsmul W.mkQ N w').symm.trans ((Submodule.Quotient.mk_eq_zero W).2 ⟨w', by simp [Nat.cast_smul_eq_nsmul]⟩)
      obtain ⟨ψ, hψ, -⟩ := hlift _ W.mkQ h0
      have h1 : W.mkQ w = 0 := by
        rw [← hψ, LinearMap.comp_apply, hw, map_zero]
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h1
      obtain ⟨u', rfl⟩ := h1
      exact ⟨u', by simp [Nat.cast_smul_eq_nsmul]⟩
    · rintro ⟨u', rfl⟩
      exact hθN u'
  have hkey : ∀ e : L, ∃ ψ : omega (Γ.btOrder ⊤) →ₗ[R] (R ⧸ Ideal.span {(N : R)}),
      (∀ w, ψ (θ w) = Ideal.Quotient.mk (Ideal.span {(N : R)}) (w e)) ∧
      ∃ v : Spec (CommRingCat.of (DualNumber (R ⧸ Ideal.span {(N : R)}))) ⟶ Γ.G.left,
        v ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom ((algebraMap (R ⧸ Ideal.span {(N : R)})
          (DualNumber (R ⧸ Ideal.span {(N : R)}))).comp (Ideal.Quotient.mk _))) ∧
        v ≫ i = Spec.map (CommRingCat.ofHom (dualMap (Ideal.Quotient.mk (Ideal.span {(N : R)})))) ≫ (M.pt e).left ∧
        v ≫ j = Spec.map (CommRingCat.ofHom
          ((kap (Ideal.span {(N : R)})).toRingHom.comp (derRing (ev1 Γ) ψ).toRingHom)) := by
    intro e
    let mkL : R →ₗ[R] (R ⧸ Ideal.span {(N : R)}) := (Ideal.Quotient.mkₐ R (Ideal.span {(N : R)})).toLinearMap
    let φ : Module.Dual R L →ₗ[R] (R ⧸ Ideal.span {(N : R)}) := mkL ∘ₗ Module.Dual.eval R L e
    have h0 : N • φ = 0 := by
      ext w'
      simp only [φ, mkL, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.zero_apply]
      rw [← map_nsmul, ← Nat.cast_smul_eq_nsmul R, AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk,
        Ideal.Quotient.eq_zero_iff_mem, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    obtain ⟨ψ, hψ, y, y1, y2, y3⟩ := hlift _ φ h0
    refine ⟨ψ, fun w => by simpa [φ, mkL] using LinearMap.congr_fun hψ w, Spec.map (CommRingCat.ofHom (kap _).toRingHom) ≫ y, ?_, ?_, ?_⟩
    · rw [Category.assoc, y1, ← Spec.map_comp]
      congr 1
      ext r : 2
      exact kap_algebraMap _ r
    · have e1 : hom x φ ≫ u = hom x mkL ≫ M.pt e := by
        rw [← hupin e, ← Category.assoc, LieEx.hom_comp]
      rw [Category.assoc, y3, e1]
      change _ ≫ Spec.map _ ≫ (M.pt e).left = _
      have e2 : CommRingCat.ofHom (TrivSqZeroExt.map mkL).toRingHom ≫ CommRingCat.ofHom (kap (Ideal.span {(N : R)})).toRingHom =
          CommRingCat.ofHom (dualMap (Ideal.Quotient.mk (Ideal.span {(N : R)}))) := by
        apply CommRingCat.hom_ext
        apply RingHom.ext
        intro a
        exact kap_map _ a
      rw [← Category.assoc, ← Spec.map_comp, e2]
    · rw [Category.assoc, y2, ← Spec.map_comp]
      rfl
  have huniq : ∀ (e : L) (v v' : Spec (CommRingCat.of (DualNumber (R ⧸ Ideal.span {(N : R)}))) ⟶ Γ.G.left),
      v ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom ((algebraMap (R ⧸ Ideal.span {(N : R)})
          (DualNumber (R ⧸ Ideal.span {(N : R)}))).comp (Ideal.Quotient.mk _))) →
      v' ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom ((algebraMap (R ⧸ Ideal.span {(N : R)})
          (DualNumber (R ⧸ Ideal.span {(N : R)}))).comp (Ideal.Quotient.mk _))) →
      v ≫ i = Spec.map (CommRingCat.ofHom (dualMap (Ideal.Quotient.mk (Ideal.span {(N : R)})))) ≫ (M.pt e).left →
      v' ≫ i = Spec.map (CommRingCat.ofHom (dualMap (Ideal.Quotient.mk (Ideal.span {(N : R)})))) ≫ (M.pt e).left →
      v = v' := by
    intro e v v' h1 h1' h2 h2'
    have := ht.inj (Over.mk (Spec.map (CommRingCat.ofHom ((algebraMap (R ⧸ Ideal.span {(N : R)})
          (DualNumber (R ⧸ Ideal.span {(N : R)}))).comp (Ideal.Quotient.mk _)))))
      (Over.homMk v h1) (Over.homMk v' h1') (by simpa using h2.trans h2'.symm)
    exact congrArg CommaMorphism.left this
  refine ⟨θ, hsurj, hker, ?_⟩
  intro f w s hs
  have hval : ∀ (ψ : omega (Γ.btOrder ⊤) →ₗ[R] (R ⧸ Ideal.span {(N : R)}))
      (v : Spec (CommRingCat.of (DualNumber (R ⧸ Ideal.span {(N : R)}))) ⟶ Γ.G.left),
      v ≫ j = Spec.map (CommRingCat.ofHom
          ((kap (Ideal.span {(N : R)})).toRingHom.comp (derRing (ev1 Γ) ψ).toRingHom)) →
      valAt v ⊤ le_top s = TrivSqZeroExt.inr (ψ ((augIdeal (Γ.btOrder ⊤)).toCotangent f)) := by
    intro ψ v hv
    rw [val_of_emb Γ hj f.1 s hs v _ hv]
    change kap _ (derRing (ev1 Γ) ψ f.1) = _
    rw [derRing_of_mem (ev1 Γ) ψ f, kap_inr]
    rfl
  constructor
  · intro hw e v h1 h2
    obtain ⟨ψ, hψ, v', h1', h2', h3'⟩ := hkey e
    rw [huniq e v v' h1 h1' h2 h2', hval ψ v' h3', ← hw, hψ]
  · intro H
    obtain ⟨w₀, hw₀⟩ := hsurj ((augIdeal (Γ.btOrder ⊤)).toCotangent f)
    have hd : ∀ e, Ideal.Quotient.mk (Ideal.span {(N : R)}) ((w - w₀) e) = 0 := by
      intro e
      obtain ⟨ψ, hψ, v', h1', h2', h3'⟩ := hkey e
      have a1 := H e v' h1' h2'
      rw [hval ψ v' h3', ← hw₀, hψ] at a1
      have a2 := TrivSqZeroExt.inr_injective a1
      rw [LinearMap.sub_apply, map_sub, a2, sub_self]
    obtain ⟨u', hu'⟩ := dual_eq_smul N (w - w₀) hd
    have : θ (w - w₀) = 0 := (hker _).2 ⟨u', hu'⟩
    rw [map_sub, sub_eq_zero] at this
    rw [this, hw₀]

end GlobalTheory.CompanionTheory.Ar.BT.Tan
