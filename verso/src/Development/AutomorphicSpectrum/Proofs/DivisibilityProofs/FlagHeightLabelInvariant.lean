import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.RefLinked
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LowerBoundOfBaseSetting
import Development.WeilBound.CoreStatements.FlagImmersions.ExistsWord
import GroundTheory.HeightsAndTheta.Heights.Intersections.PBlockRatioAlg
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHFlProdLinear

noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (FlBlock FlIdx PFl xLine xDeg yFl fsHerm ΩFl refNorm)
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm blockFnField)

namespace GlobalTheory.CompanionTheory.Ar.Top.HhLabel

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

def blockMap (σ : Equiv.Perm Ψ) : FlBlock Ψ N → FlBlock Ψ N := fun q => (σ q.1, q.2)

def coordMap (σ : Equiv.Perm Ψ) : (Σ q : FlBlock Ψ N, FlIdx Ψ N q) → (Σ q : FlBlock Ψ N, FlIdx Ψ N q) :=
  fun p => ⟨(σ p.1.1, p.1.2), p.2⟩

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨τ, i⟩ ⟨τ', i'⟩ h`. Simplify using `only [blockMap, Prod.mk.injEq] at h`. Rewrite using `[σ.injective h.1, h.2]`. Introduce and unpack `⟨τ, i⟩`.

Conclude with `⟨(σ.symm τ, i), by simp [blockMap]⟩`.
-/
theorem blockMap_bijective (σ : Equiv.Perm Ψ) : Function.Bijective (blockMap (N := N) σ) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨τ, i⟩ ⟨τ', i'⟩ h
    simp only [blockMap, Prod.mk.injEq] at h
    rw [σ.injective h.1, h.2]
  · rintro ⟨τ, i⟩
    exact ⟨(σ.symm τ, i), by simp [blockMap]⟩

/- English proof (translation)
Introduce and unpack `⟨⟨τ, i⟩, A⟩ ⟨⟨τ', i'⟩, A'⟩ h`. Simplify using `only [coordMap, Sigma.mk.inj_iff, Prod.mk.injEq] at h`. Take `⟨⟨h1, rfl⟩, h2⟩` from `h`. Take `rfl` from `σ.injective h1`. Consider the cases of `eq_of_heq h2`.

Both sides reduce to the same expression.
-/
theorem coordMap_injective (σ : Equiv.Perm Ψ) : Function.Injective (coordMap (N := N) σ) := by
  rintro ⟨⟨τ, i⟩, A⟩ ⟨⟨τ', i'⟩, A'⟩ h
  simp only [coordMap, Sigma.mk.inj_iff, Prod.mk.injEq] at h
  obtain ⟨⟨h1, rfl⟩, h2⟩ := h
  obtain rfl := σ.injective h1
  cases eq_of_heq h2
  rfl

/- English proof (translation)
Introduce and unpack `⟨⟨τ, i⟩, A⟩`. Use `⟨⟨(σ.symm τ, i), A⟩, Sigma.ext (by simp [coordMap]) HEq.rfl⟩` and prove the remaining obligations.
-/
theorem coordMap_surjective (σ : Equiv.Perm Ψ) : Function.Surjective (coordMap (N := N) σ) := by
  rintro ⟨⟨τ, i⟩, A⟩
  refine ⟨⟨(σ.symm τ, i), A⟩, Sigma.ext (by simp [coordMap]) HEq.rfl⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨(blockMap_bijective σ).1, coordMap_injective σ, fun _ => rfl, fun q _ => coordMap_surjective σ q⟩`.
-/
theorem isBlockMap (σ : Equiv.Perm Ψ) : IsBlockMap (blockMap (N := N) σ) (coordMap σ) :=
  ⟨(blockMap_bijective σ).1, coordMap_injective σ, fun _ => rfl, fun q _ => coordMap_surjective σ q⟩

def matEquiv (N : ℕ) (σ : Equiv.Perm Ψ) : (Ψ × Fin N × Fin N) ≃ (Ψ × Fin N × Fin N) :=
  Equiv.prodCongr σ (Equiv.refl _)

def fieldAut (σ : Equiv.Perm Ψ) : ΩFl Ψ N ≃+* ΩFl Ψ N :=
  IsFractionRing.ringEquivOfRingEquiv (renameEquiv ℚ (matEquiv N σ)).toRingEquiv

/- English proof (translation)
Unfold `yFl fieldAut`. Rewrite using `[IsFractionRing.ringEquivOfRingEquiv_algebraMap]`. Use `congr 1`. Use `show _ = (renameEquiv ℚ (matEquiv N σ)).toRingEquiv.toRingHom _`. Rewrite using `[RingHom.map_det]`.

Use `congr 1`. Use `Matrix.ext fun a b => ?_` and prove the remaining obligations. Conclude with `(rename_X (R := ℚ) (matEquiv N σ) (p.1.1, Fin.castLE (GroundTheory.Heights₂.Heights.LowerBoundFree.step_le p.1.2) a, p.2.1 b)).symm`.
-/
theorem yFl_coordMap (σ : Equiv.Perm Ψ) (p : Σ q : FlBlock Ψ N, FlIdx Ψ N q) :
    yFl Ψ N (coordMap σ p) = fieldAut σ (yFl Ψ N p) := by
  unfold yFl fieldAut
  rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  congr 1
  show _ = (renameEquiv ℚ (matEquiv N σ)).toRingEquiv.toRingHom _
  rw [RingHom.map_det]
  congr 1
  refine Matrix.ext fun a b => ?_
  exact (rename_X (R := ℚ) (matEquiv N σ) (p.1.1, Fin.castLE (GroundTheory.Heights₂.Heights.LowerBoundFree.step_le p.1.2) a, p.2.1 b)).symm

/- English proof (translation)
Establish `key : ∀ f : MRing J, mConeMap (fun p => i (y₀ p)) f = MvPolynomial.map i (mConeMap y₀ f)`. Introduce `f`. Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C a => simp [mConeMap]`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`.

Consider the case `mul_X p n hp => simp only [map_mul, hp]`. Simplify using `[mConeMap]`. Use extensionality with `f`. Use `show mConeMap _ f = 0 ↔ mConeMap _ f = 0`. Rewrite using `[key]`.

Conclude with `map_eq_zero_iff _ (MvPolynomial.map_injective i i.injective)`.
-/
theorem mCoordIdeal_ringHom {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω₀ Ω : Type} [Field Ω₀] [Field Ω]
    (i : Ω₀ →+* Ω) (y₀ : (Σ k, J k) → Ω₀) : mCoordIdeal (fun p => i (y₀ p)) = mCoordIdeal y₀ := by
  have key : ∀ f : MRing J, mConeMap (fun p => i (y₀ p)) f = MvPolynomial.map i (mConeMap y₀ f) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp [mConeMap]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p n hp => simp only [map_mul, hp]; simp [mConeMap]
  ext f
  show mConeMap _ f = 0 ↔ mConeMap _ f = 0
  rw [key]
  exact map_eq_zero_iff _ (MvPolynomial.map_injective i i.injective)

/- English proof (translation)
Unfold `PFl`. Rewrite using `[← GroundTheory.Heights₂.Heights.Inter.BlockRatioAlgebraic.mCoordIdeal_comp_v (isBlockMap σ), ← mCoordIdeal_ringHom (fieldAut (N := N) σ : ΩFl Ψ N →+* ΩFl Ψ N) (yFl Ψ N)]`. Use `congr 1`. Use function extensionality and compare the values at `p`. Conclude with `yFl_coordMap σ p`.
-/
theorem imageZ_PFl (σ : Equiv.Perm Ψ) : imageZ (coordMap σ) (PFl Ψ N) = PFl Ψ N := by
  unfold PFl
  rw [← GroundTheory.Heights₂.Heights.Inter.BlockRatioAlgebraic.mCoordIdeal_comp_v (isBlockMap σ),
    ← mCoordIdeal_ringHom (fieldAut (N := N) σ : ΩFl Ψ N →+* ΩFl Ψ N) (yFl Ψ N)]
  congr 1
  funext p
  exact yFl_coordMap σ p

/- English proof (translation)
Unfold `blockFnField`. Use `congr 1`. Use extensionality with `t`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨p, q, hpq, rfl⟩`.

Conclude with `⟨coordMap σ p, coordMap σ q, by simp [coordMap, hpq], rfl⟩`. Introduce and unpack `⟨p, q, hpq, rfl⟩`. Take `⟨p', rfl⟩` from `coordMap_surjective σ p`. Take `⟨q', rfl⟩` from `coordMap_surjective σ q`. Conclude with `⟨p', q', (blockMap_bijective σ).1 hpq, rfl⟩`.
-/
theorem blockFnField_coordMap (σ : Equiv.Perm Ψ) :
    blockFnField (yFl Ψ N ∘ coordMap σ) = blockFnField (yFl Ψ N) := by
  unfold blockFnField
  congr 1
  ext t
  constructor
  · rintro ⟨p, q, hpq, rfl⟩
    exact ⟨coordMap σ p, coordMap σ q, by simp [coordMap, hpq], rfl⟩
  · rintro ⟨p, q, hpq, rfl⟩
    obtain ⟨p', rfl⟩ := coordMap_surjective σ p
    obtain ⟨q', rfl⟩ := coordMap_surjective σ q
    exact ⟨p', q', (blockMap_bijective σ).1 hpq, rfl⟩

/- English proof (translation)
Apply the tactic sequence `by_cases h : q.1 = p.1 <;> simp [xDeg, blockMap, h]`.
-/
theorem xDeg_blockMap (σ : Equiv.Perm Ψ) (p : Ψ × Fin N) (q : FlBlock Ψ N) :
    xDeg Ψ N (σ p.1, p.2) (blockMap σ q) = xDeg Ψ N p q := by
  by_cases h : q.1 = p.1 <;> simp [xDeg, blockMap, h]

/- English proof (translation)
Use `⟨?_, fun z' => ?_⟩` and prove the remaining obligations. Use `show xDeg Ψ N (σ p.1, p.2) = pullDeg (blockMap σ) (xDeg Ψ N p)`. Use function extensionality and compare the values at `q`. Take `⟨q', rfl⟩` from `(blockMap_bijective σ).2 q`. Unfold `pullDeg`.

Rewrite using `[(blockMap_bijective σ).1.extend_apply, xDeg_blockMap]`. Use `show refNorm (xDeg Ψ N (σ p.1, p.2)) z' = refNorm (xDeg Ψ N p) fun r => z' (coordMap σ r)`. Unfold `refNorm`. Use `(Fintype.prod_bijective (blockMap σ) (blockMap_bijective σ) _ _ fun k => ?_).symm` and prove the remaining obligations. Rewrite using `[xDeg_blockMap]`.

Both sides reduce to the same expression.
-/
theorem isPullHerm_xLine (σ : Equiv.Perm Ψ) (p : Ψ × Fin N) :
    IsPullHerm (blockMap σ) (coordMap σ) (xLine Ψ N p) (xLine Ψ N (σ p.1, p.2)) := by
  refine ⟨?_, fun z' => ?_⟩
  · show xDeg Ψ N (σ p.1, p.2) = pullDeg (blockMap σ) (xDeg Ψ N p)
    funext q
    obtain ⟨q', rfl⟩ := (blockMap_bijective σ).2 q
    unfold pullDeg
    rw [(blockMap_bijective σ).1.extend_apply, xDeg_blockMap]
  · show refNorm (xDeg Ψ N (σ p.1, p.2)) z' = refNorm (xDeg Ψ N p) fun r => z' (coordMap σ r)
    unfold refNorm
    refine (Fintype.prod_bijective (blockMap σ) (blockMap_bijective σ) _ _ fun k => ?_).symm
    rw [xDeg_blockMap]
    rfl

/- English proof (translation)
Proceed by induction on `m using Finsupp.induction_linear with`. Consider the case `zero => simp`. Consider the case `add a b ha hb => rw [Finsupp.mapDomain_add, map_add, map_add, ha, hb]`. Consider the case `single a n => simp [Finsupp.mapDomain_single, Finsupp.degree_single]`.
-/
theorem degree_mapDomain {J J' : Type} (f : J → J') (m : J →₀ ℕ) : (m.mapDomain f).degree = m.degree := by
  induction m using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => rw [Finsupp.mapDomain_add, map_add, map_add, ha, hb]
  | single a n => simp [Finsupp.mapDomain_single, Finsupp.degree_single]

end GlobalTheory.CompanionTheory.Ar.Top.HhLabel

namespace GlobalTheory.CompanionTheory.Ar.Top

open HhLabel in

/- English proof (translation)
Introduce `II hII Ψ _ _ N _ _ hP σ F`. Establish `key : ∀ w : Fin (dimFl Ψ N + 1) → Ψ × Fin N, II (FlBlock Ψ N) (FlIdx Ψ N) (PFl Ψ N) (dimFl Ψ N + 1) (fun k => xLine Ψ N (σ (w k).1, (w k).2)) = II (FlBlock Ψ N) (FlIdx Ψ N) (PFl Ψ N) (dimFl Ψ N + 1) (fun k => xLine Ψ N (w k))`. Introduce `w`. Establish `himg` using `imageZ_PFl (N := N) σ`. Establish `hPF` using `hII.2.2.1 (FlBlock Ψ N) (FlIdx Ψ N) (FlBlock Ψ N) (FlIdx Ψ N) (blockMap σ) (coordMap σ) (ΩFl Ψ N) (yFl Ψ N) (dimFl Ψ N + 1) (fun k => xLine Ψ N (w k)) (fun k => xLine Ψ N (σ (w k).1, (w k).2)) (isBlockMap σ) hP (by show IsArithVar (imageZ (coordMap σ) (PFl Ψ N)) _; rw [himg]; exa …`.

Rewrite `hPF` using `[blockFnField_coordMap, IntermediateField.relfinrank_self, Nat.cast_one, one_mul]`. Conclude with `hPF.trans (congrArg (fun P => II (FlBlock Ψ N) (FlIdx Ψ N) P (dimFl Ψ N + 1) fun k => xLine Ψ N (w k)) himg)`. Proceed by induction on `F using MvPolynomial.induction_on' with`. Consider the case `add p q hp hq => rw [map_add, map_add, map_add, hp, hq]`. Consider the case `monomial m c`.

Rewrite using `[rename_monomial]`. Distinguish the cases in `hm : m.degree = dimFl Ψ N + 1`. Take `⟨w, rfl⟩` from `RootFieldNumerics.HH.exists_word _ m hm`. Establish `hmap : (∑ k, Finsupp.single (w k) (1 : ℕ)).mapDomain (fun x : Ψ × Fin N => (σ x.1, x.2)) = ∑ k, Finsupp.single (σ (w k).1, (w k).2) 1`. Rewrite using `[Finsupp.mapDomain_finset_sum]`.

Simplify using `only [Finsupp.mapDomain_single]`. Establish `hwd` using `RootFieldNumerics.HH.hhFl_word II hII.1 hP (fun k => (σ (w k).1, (w k).2)) c`. Rewrite using `[hmap, hwd, RootFieldNumerics.HH.hhFl_word II hII.1 hP w c, key w]`. Rewrite using `[HhModel.hhFl_monomial_of_ne II _ _ (by rwa [degree_mapDomain]), HhModel.hhFl_monomial_of_ne II _ _ hm]`.
-/
theorem hhFl_labelInv : ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ]
    (N : ℕ) [Nonempty Ψ], 2 ≤ N → IsArithVar (GroundTheory.Heights₂.Heights.LowerBoundFree.PFl Ψ N) (dimFl Ψ N + 1) →
    LabelInv (Ψ := Ψ) (N := N) (hhFl Ψ N II) := by
  intro II hII Ψ _ _ N _ _ hP σ F
  have key : ∀ w : Fin (dimFl Ψ N + 1) → Ψ × Fin N,
      II (FlBlock Ψ N) (FlIdx Ψ N) (PFl Ψ N) (dimFl Ψ N + 1) (fun k => xLine Ψ N (σ (w k).1, (w k).2)) =
        II (FlBlock Ψ N) (FlIdx Ψ N) (PFl Ψ N) (dimFl Ψ N + 1) (fun k => xLine Ψ N (w k)) := by
    intro w
    have himg := imageZ_PFl (N := N) σ
    have hPF := hII.2.2.1 (FlBlock Ψ N) (FlIdx Ψ N) (FlBlock Ψ N) (FlIdx Ψ N) (blockMap σ) (coordMap σ) (ΩFl Ψ N)
      (yFl Ψ N) (dimFl Ψ N + 1) (fun k => xLine Ψ N (w k)) (fun k => xLine Ψ N (σ (w k).1, (w k).2))
      (isBlockMap σ) hP (by show IsArithVar (imageZ (coordMap σ) (PFl Ψ N)) _; rw [himg]; exact hP)
      (fun _ => GroundTheory.Heights₂.Heights.LowerBoundFree.FlagHeightMultilinear.isSmoothHerm_fsHerm _)
      (fun j => isPullHerm_xLine σ (w j))
    rw [blockFnField_coordMap, IntermediateField.relfinrank_self, Nat.cast_one, one_mul] at hPF
    exact hPF.trans (congrArg (fun P => II (FlBlock Ψ N) (FlIdx Ψ N) P (dimFl Ψ N + 1) fun k => xLine Ψ N (w k)) himg)
  induction F using MvPolynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | monomial m c =>
    rw [rename_monomial]
    by_cases hm : m.degree = dimFl Ψ N + 1
    · obtain ⟨w, rfl⟩ := RootFieldNumerics.HH.exists_word _ m hm
      have hmap : (∑ k, Finsupp.single (w k) (1 : ℕ)).mapDomain (fun x : Ψ × Fin N => (σ x.1, x.2)) =
          ∑ k, Finsupp.single (σ (w k).1, (w k).2) 1 := by
        rw [Finsupp.mapDomain_finset_sum]
        simp only [Finsupp.mapDomain_single]
      have hwd := RootFieldNumerics.HH.hhFl_word II hII.1 hP (fun k => (σ (w k).1, (w k).2)) c
      rw [hmap, hwd, RootFieldNumerics.HH.hhFl_word II hII.1 hP w c, key w]
    · rw [HhModel.hhFl_monomial_of_ne II _ _ (by rwa [degree_mapDomain]), HhModel.hhFl_monomial_of_ne II _ _ hm]

end GlobalTheory.CompanionTheory.Ar.Top
