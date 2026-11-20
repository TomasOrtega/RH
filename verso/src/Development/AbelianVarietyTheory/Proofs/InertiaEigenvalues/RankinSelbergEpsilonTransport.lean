import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalLanglandsExists
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroCuspidalLL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalConverseGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInduction
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BrauerDegreeZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousRingEquivLocalFieldPreservesValuationStatement
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.PairEpsTransport

section Maps
variable {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[longElt, GeneralLinearGroup.map]`.
-/
theorem map_longElt (n : ℕ) : GeneralLinearGroup.map f (longElt n R) = longElt n S := by
  ext i j; simp [longElt, GeneralLinearGroup.map]

/- English proof (translation)
Use extensionality with `i j`. Establish `h` using `congrArg (fun h : GL (Fin n) S => (h : Matrix (Fin n) (Fin n) S) j i) (map_inv (GeneralLinearGroup.map f) g)`. Conclude with `h`.
-/
theorem map_invT (n : ℕ) (g : GL (Fin n) R) :
    GeneralLinearGroup.map f (GlobalTheory.CuspRep.invT n R g) = GlobalTheory.CuspRep.invT n S (GeneralLinearGroup.map f g) := by
  ext i j
  have h := congrArg (fun h : GL (Fin n) S => (h : Matrix (Fin n) (Fin n) S) j i)
    (map_inv (GeneralLinearGroup.map f) g)
  exact h

/- English proof (translation)
Rewrite using `[tilde, tilde, map_mul, map_longElt, map_invT]`.
-/
theorem map_tilde {n : ℕ} (g : GL (Fin n) R) :
    GeneralLinearGroup.map f (tilde g) = tilde (GeneralLinearGroup.map f g) := by
  rw [tilde, tilde, map_mul, map_longElt, map_invT]

/- English proof (translation)
Use extensionality with `i j`. Use `show f ((emb₂ R (stdSum (rfl : m + 1 = m + 1)) (g, 1) : Matrix _ _ R) i j) = (emb₂ S (stdSum (rfl : m + 1 = m + 1)) (GeneralLinearGroup.map f g, 1) : Matrix _ _ S) i j`. Rewrite using `[val_emb₂, val_emb₂]`. Take `⟨i, rfl⟩` from `(stdSum (rfl : m + 1 = m + 1)).surjective i`. Take `⟨j, rfl⟩` from `(stdSum (rfl : m + 1 = m + 1)).surjective j`.

Apply the tactic sequence `rcases i with i | i <;> rcases j with j | j <;>`. Apply the tactic sequence `simp [Matrix.one_apply, GeneralLinearGroup.map] <;> split_ifs <;> simp`.
-/
theorem map_corner {m : ℕ} (g : GL (Fin m) R) :
    GeneralLinearGroup.map f (corner g) = corner (GeneralLinearGroup.map f g) := by
  ext i j
  show f ((emb₂ R (stdSum (rfl : m + 1 = m + 1)) (g, 1) : Matrix _ _ R) i j) =
    (emb₂ S (stdSum (rfl : m + 1 = m + 1)) (GeneralLinearGroup.map f g, 1) : Matrix _ _ S) i j
  rw [val_emb₂, val_emb₂]
  obtain ⟨i, rfl⟩ := (stdSum (rfl : m + 1 = m + 1)).surjective i
  obtain ⟨j, rfl⟩ := (stdSum (rfl : m + 1 = m + 1)).surjective j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.one_apply, GeneralLinearGroup.map] <;> split_ifs <;> simp

/- English proof (translation)
Simplify using `[GlobalTheory.Whittaker.superDiag, map_sum, GeneralLinearGroup.map]`.
-/
theorem superDiag_map {n : ℕ} (g : GL (Fin n) R) :
    GlobalTheory.Whittaker.superDiag (GeneralLinearGroup.map f g) = f (GlobalTheory.Whittaker.superDiag g) := by
  simp [GlobalTheory.Whittaker.superDiag, map_sum, GeneralLinearGroup.map]

/- English proof (translation)
Rewrite `hg`, the goal using `[mem_unipB]`. Use `⟨fun i j h => ?_, fun i => ?_⟩` and prove the remaining obligations. Simplify using `[GeneralLinearGroup.map, hg.1 i j h]`. Simplify using `[GeneralLinearGroup.map, hg.2 i]`.
-/
theorem map_mem_unipB {n : ℕ} {g : GL (Fin n) R} (hg : g ∈ unipB R (Fin n)) :
    GeneralLinearGroup.map f g ∈ unipB S (Fin n) := by
  rw [mem_unipB] at hg ⊢
  refine ⟨fun i j h => ?_, fun i => ?_⟩
  · simp [GeneralLinearGroup.map, hg.1 i j h]
  · simp [GeneralLinearGroup.map, hg.2 i]

end Maps

section Core

variable {k k' : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k]
  [Field k'] [TopologicalSpace k'] [IsTopologicalRing k']

/- English proof (translation)
Use extensionality with `a b`. Simplify using `[GeneralLinearGroup.map]`.
-/
theorem map_map_symm {n : ℕ} (i : k ≃+* k') (g : GL (Fin n) k') :
    GeneralLinearGroup.map i.toRingHom (GeneralLinearGroup.map i.symm.toRingHom g) = g := by
  ext a b; simp [GeneralLinearGroup.map]

/- English proof (translation)
Use extensionality with `a b`. Simplify using `[GeneralLinearGroup.map]`.
-/
theorem map_symm_map {n : ℕ} (i : k ≃+* k') (g : GL (Fin n) k) :
    GeneralLinearGroup.map i.symm.toRingHom (GeneralLinearGroup.map i.toRingHom g) = g := by
  ext a b; simp [GeneralLinearGroup.map]

/- English proof (translation)
Use `Units.continuous_iff.2 ⟨?_, ?_⟩` and prove the remaining obligations. Conclude with `Units.continuous_val.matrix_map hi`. Conclude with `Units.continuous_coe_inv.matrix_map hi`.
-/
theorem continuous_mapGL {n : ℕ} (i : k ≃+* k') (hi : Continuous i) :
    Continuous (GeneralLinearGroup.map (n := Fin n) i.toRingHom) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact Units.continuous_val.matrix_map hi
  · exact Units.continuous_coe_inv.matrix_map hi

end Core

section Transport

variable {k k' : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k]
  [Field k'] [TopologicalSpace k'] [IsTopologicalRing k']

/- English proof (translation)
Take `⟨h1, h2, C, hC, h3⟩` from `hf`. Use `⟨fun u hu g => ?_, h2.comp_continuous (continuous_mapGL i.symm hi'), ?_⟩` and prove the remaining obligations. Use `show f (GeneralLinearGroup.map i.symm.toRingHom (u * g)) = f (GeneralLinearGroup.map i.symm.toRingHom g)`. Rewrite using `[map_mul]`. Conclude with `h1 _ (map_mem_unipB _ hu) _`.

Use `⟨GeneralLinearGroup.map i.toRingHom '' C, hC.image (continuous_mapGL i hi), fun g hg => ?_⟩` and prove the remaining obligations. Take `⟨u, hu, c, hc, he⟩` from `h3 _ hg`. Use `⟨GeneralLinearGroup.map i.toRingHom u, map_mem_unipB _ hu, GeneralLinearGroup.map i.toRingHom c, ⟨c, hc, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_mul, ← he, map_map_symm]`.
-/
theorem isTestFun_comp {m : ℕ} (i : k ≃+* k') (hi : Continuous i) (hi' : Continuous i.symm)
    {f : GL (Fin m) k → ℂ} (hf : IsTestFun f) :
    IsTestFun (fun g => f (GeneralLinearGroup.map i.symm.toRingHom g)) := by
  obtain ⟨h1, h2, C, hC, h3⟩ := hf
  refine ⟨fun u hu g => ?_, h2.comp_continuous (continuous_mapGL i.symm hi'), ?_⟩
  · show f (GeneralLinearGroup.map i.symm.toRingHom (u * g)) = f (GeneralLinearGroup.map i.symm.toRingHom g)
    rw [map_mul]
    exact h1 _ (map_mem_unipB _ hu) _
  · refine ⟨GeneralLinearGroup.map i.toRingHom '' C, hC.image (continuous_mapGL i hi), fun g hg => ?_⟩
    obtain ⟨u, hu, c, hc, he⟩ := h3 _ hg
    refine ⟨GeneralLinearGroup.map i.toRingHom u, map_mem_unipB _ hu, GeneralLinearGroup.map i.toRingHom c,
      ⟨c, hc, rfl⟩, ?_⟩
    rw [← map_mul, ← he, map_map_symm]

variable {m : ℕ} {V V' W W' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
  [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

/- English proof (translation)
Introduce `ω' hω' l' L' hl' hL' I' hI' v' w'`. Establish `hψinv : ∀ x, (ψ'⁻¹) (i x) = (ψ⁻¹) x`. Introduce `x`. Simplify using `only [AddChar.inv_apply]`. Rewrite using `[← map_neg, hψ]`.

Establish `hω : HasCentralChar τ (ω'.comp (Units.map i.toRingHom.toMonoidHom))`. Introduce `z w`. Apply `B.injective` to reduce the goal to its premises. Rewrite using `[hB, GeneralLinearGroup.map_scalar, hω', map_smul]`. Both sides reduce to the same expression.

Establish `hl : GlobalTheory.Whittaker.IsFunctional ψ π (l'.comp A.toLinearMap)`. Introduce `u hu v`. Simplify using `only [LinearMap.comp_apply, LinearEquiv.coe_coe]`. Rewrite using `[hA, hl' _ (map_mem_unipB _ hu), superDiag_map]`. Simplify using `[hψ]`.

Establish `hL : GlobalTheory.Whittaker.IsFunctional ψ⁻¹ τ (L'.comp B.toLinearMap)`. Introduce `u hu v`. Simplify using `only [LinearMap.comp_apply, LinearEquiv.coe_coe]`. Rewrite using `[hB, hL' _ (map_mem_unipB _ hu), superDiag_map]`. Use `hψinv (GlobalTheory.Whittaker.superDiag u)` as an intermediate fact.

Simplify using `only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]`. Rewrite using `[this]`. Establish `hI : IsInvIntegral (I'.comp (LinearMap.funLeft ℂ ℂ (GeneralLinearGroup.map (n` using `Fin m) i.symm.toRingHom))) := by`. Introduce `f hf x`. Express the relevant statement in the definitionally equal form `I' (fun g => f (GeneralLinearGroup.map i.symm.toRingHom g * x)) = I' (fun g => f (GeneralLinearGroup.map i.symm.toRingHom g))`.

Use `hI' _ (isTestFun_comp i hi hi' hf) (GeneralLinearGroup.map i.toRingHom x)` as an intermediate fact. Use `Eq.trans ?_ this` and prove the remaining obligations. Use `congr 1`. Use function extensionality and compare the values at `g`. Rewrite using `[map_mul, map_symm_map]`.

Establish `key` using `H _ hω _ _ hl hL _ hI (A.symm v') (B.symm w')`. Establish `e1 : LinearMap.funLeft ℂ ℂ (GeneralLinearGroup.map (n` using `Fin m) i.symm.toRingHom) (fun g => (l'.comp A.toLinearMap) (π (tilde (corner g)) (A.symm v')) * (L'.comp B.toLinearMap) (τ (tilde g) (B.symm w'))) = fun g => l' (π' (tilde (corner g)) v') * L' (τ' (tilde g) w') := by`. Use function extensionality and compare the values at `g`. Simplify using `only [LinearMap.funLeft_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, Function.comp_apply, hA, hB, map_tilde, map_corner, map_map_symm, LinearEquiv.apply_symm_apply]`. Establish `e2 : LinearMap.funLeft ℂ ℂ (GeneralLinearGroup.map (n` using `Fin m) i.symm.toRingHom) (fun g => (l'.comp A.toLinearMap) (π (corner g) (A.symm v')) * (L'.comp B.toLinearMap) (τ g (B.symm w'))) = fun g => l' (π' (corner g) v') * L' (τ' g w') := by`.

Use function extensionality and compare the values at `g`. Simplify using `only [LinearMap.funLeft_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, Function.comp_apply, hA, hB, map_corner, map_map_symm, LinearEquiv.apply_symm_apply]`. Establish `e3 : (ω'.comp (Units.map i.toRingHom.toMonoidHom)) (-1) = ω' (-1)`. Simplify using the standard rewrite rules. Rewrite `key` using `[LinearMap.comp_apply, LinearMap.comp_apply, e1, e2, e3]`.

Conclude with `key`.
-/
theorem hasPairEps_of_equiv (i : k ≃+* k') (hi : Continuous i) (hi' : Continuous i.symm)
    {ψ : AddChar k Circle} {ψ' : AddChar k' Circle} (hψ : ∀ x, ψ' (i x) = ψ x)
    {π : Representation ℂ (GL (Fin (m + 1)) k) V} {π' : Representation ℂ (GL (Fin (m + 1)) k') V'}
    {τ : Representation ℂ (GL (Fin m) k) W} {τ' : Representation ℂ (GL (Fin m) k') W'}
    (A : V ≃ₗ[ℂ] V') (hA : ∀ g v, A (π g v) = π' (GeneralLinearGroup.map i.toRingHom g) (A v))
    (B : W ≃ₗ[ℂ] W') (hB : ∀ g v, B (τ g v) = τ' (GeneralLinearGroup.map i.toRingHom g) (B v))
    {c : ℂ} (H : HasPairEps ψ π τ c) : HasPairEps ψ' π' τ' c := by
  intro ω' hω' l' L' hl' hL' I' hI' v' w'
  have hψinv : ∀ x, (ψ'⁻¹) (i x) = (ψ⁻¹) x := by
    intro x; simp only [AddChar.inv_apply]; rw [← map_neg, hψ]
  have hω : HasCentralChar τ (ω'.comp (Units.map i.toRingHom.toMonoidHom)) := by
    intro z w
    apply B.injective
    rw [hB, GeneralLinearGroup.map_scalar, hω', map_smul]
    rfl
  have hl : GlobalTheory.Whittaker.IsFunctional ψ π (l'.comp A.toLinearMap) := by
    intro u hu v
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hA, hl' _ (map_mem_unipB _ hu), superDiag_map]
    simp [hψ]
  have hL : GlobalTheory.Whittaker.IsFunctional ψ⁻¹ τ (L'.comp B.toLinearMap) := by
    intro u hu v
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hB, hL' _ (map_mem_unipB _ hu), superDiag_map]
    have := hψinv (GlobalTheory.Whittaker.superDiag u)
    simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
    rw [this]
  have hI : IsInvIntegral (I'.comp (LinearMap.funLeft ℂ ℂ (GeneralLinearGroup.map (n := Fin m) i.symm.toRingHom))) := by
    intro f hf x
    change I' (fun g => f (GeneralLinearGroup.map i.symm.toRingHom g * x)) =
      I' (fun g => f (GeneralLinearGroup.map i.symm.toRingHom g))
    have := hI' _ (isTestFun_comp i hi hi' hf) (GeneralLinearGroup.map i.toRingHom x)
    refine Eq.trans ?_ this
    congr 1
    funext g
    rw [map_mul, map_symm_map]
  have key := H _ hω _ _ hl hL _ hI (A.symm v') (B.symm w')
  have e1 : LinearMap.funLeft ℂ ℂ (GeneralLinearGroup.map (n := Fin m) i.symm.toRingHom)
      (fun g => (l'.comp A.toLinearMap) (π (tilde (corner g)) (A.symm v')) *
        (L'.comp B.toLinearMap) (τ (tilde g) (B.symm w'))) =
      fun g => l' (π' (tilde (corner g)) v') * L' (τ' (tilde g) w') := by
    funext g
    simp only [LinearMap.funLeft_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, Function.comp_apply, hA, hB,
      map_tilde, map_corner, map_map_symm, LinearEquiv.apply_symm_apply]
  have e2 : LinearMap.funLeft ℂ ℂ (GeneralLinearGroup.map (n := Fin m) i.symm.toRingHom)
      (fun g => (l'.comp A.toLinearMap) (π (corner g) (A.symm v')) *
        (L'.comp B.toLinearMap) (τ g (B.symm w'))) =
      fun g => l' (π' (corner g) v') * L' (τ' g w') := by
    funext g
    simp only [LinearMap.funLeft_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, Function.comp_apply, hA, hB,
      map_corner, map_map_symm, LinearEquiv.apply_symm_apply]
  have e3 : (ω'.comp (Units.map i.toRingHom.toMonoidHom)) (-1) = ω' (-1) := by
    simp
  rw [LinearMap.comp_apply, LinearMap.comp_apply, e1, e2, e3] at key
  exact key
end Transport

section Main

/- English proof (translation)
The claim follows from `LinearMap.congr_fun (φ.toIntertwiningMap.isIntertwining' g) v`.
-/
theorem equiv_apply_rep {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (φ : ρ.Equiv σ) (g : G) (v : V) :
    φ.toLinearEquiv (ρ g v) = σ g (φ.toLinearEquiv v) :=
  LinearMap.congr_fun (φ.toIntertwiningMap.isIntertwining' g) v

variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']

/- English proof (translation)
Take `⟨n₀, π₀, π₀', e, h1, h2, he⟩` from `h`. Take `⟨rfl, h1⟩` from `Sigma.mk.inj_iff.1 h1`. Take `⟨-, h2⟩` from `Sigma.mk.inj_iff.1 h2`. Take `⟨φ⟩` from `IrrRep.cl_eq_iff.1 (eq_of_heq h1)`. Take `⟨φ'⟩` from `IrrRep.cl_eq_iff.1 (eq_of_heq h2)`.

Use `⟨φ.toLinearEquiv ≪≫ₗ e ≪≫ₗ φ'.toLinearEquiv.symm, fun g v => ?_⟩` and prove the remaining obligations. Apply `φ'.toLinearEquiv.injective` to reduce the goal to its premises. Simplify using `only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]`. Rewrite using `[equiv_apply_rep φ, he, equiv_apply_rep φ', LinearEquiv.apply_symm_apply]`.
-/
theorem exists_equiv_of_repRel (i : k ≃+* k') {n : ℕ} {π : IrrRep (GL (Fin n) k)} {π' : IrrRep (GL (Fin n) k')}
    (h : RepRel i (cls π) (cls π')) :
    ∃ E : π.V ≃ₗ[ℂ] π'.V, ∀ g v, E (π.ρ g v) = π'.ρ (GeneralLinearGroup.map i.toRingHom g) (E v) := by
  obtain ⟨n₀, π₀, π₀', e, h1, h2, he⟩ := h
  obtain ⟨rfl, h1⟩ := Sigma.mk.inj_iff.1 h1
  obtain ⟨-, h2⟩ := Sigma.mk.inj_iff.1 h2
  obtain ⟨φ⟩ := IrrRep.cl_eq_iff.1 (eq_of_heq h1)
  obtain ⟨φ'⟩ := IrrRep.cl_eq_iff.1 (eq_of_heq h2)
  refine ⟨φ.toLinearEquiv ≪≫ₗ e ≪≫ₗ φ'.toLinearEquiv.symm, fun g v => ?_⟩
  apply φ'.toLinearEquiv.injective
  simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rw [equiv_apply_rep φ, he, equiv_apply_rep φ', LinearEquiv.apply_symm_apply]

end Main

end GlobalTheory.PairEpsTransport

open GlobalTheory.PairEpsTransport in

/- English proof (translation)
Introduce `k k' _ _ _ _ _ _ _ _ _ _ i hi ψ ψ' hψ m π π' τ τ' c hπ hτ H`. Establish `hi' : Continuous i.symm` using `(GlobalTheory.T.continuous_ringEquiv_localField_preserves_valuation k k' i hi).1`. Take `⟨A, hA⟩` from `exists_equiv_of_repRel i hπ`. Take `⟨B, hB⟩` from `exists_equiv_of_repRel i hτ`. Conclude with `hasPairEps_of_equiv i hi hi' hψ A hA B hB H`.
-/
theorem GlobalTheory.LocLanglands.hasPairEps_transport : ∀ (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [CharZero k'] (i : k ≃+* k'), Continuous i → ∀ (ψ : AddChar k Circle) (ψ' : AddChar k' Circle), (∀ x, ψ' (i x) = ψ x) → ∀ (m : ℕ) (π : IrrRep (GL (Fin (m + 1)) k)) (π' : IrrRep (GL (Fin (m + 1)) k')) (τ : IrrRep (GL (Fin m) k)) (τ' : IrrRep (GL (Fin m) k')) (c : ℂ), RepRel i (cls π) (cls π') → RepRel i (cls τ) (cls τ') → HasPairEps ψ π.ρ τ.ρ c → HasPairEps ψ' π'.ρ τ'.ρ c := by
  intro k k' _ _ _ _ _ _ _ _ _ _ i hi ψ ψ' hψ m π π' τ τ' c hπ hτ H
  have hi' : Continuous i.symm := (GlobalTheory.T.continuous_ringEquiv_localField_preserves_valuation k k' i hi).1
  obtain ⟨A, hA⟩ := exists_equiv_of_repRel i hπ
  obtain ⟨B, hB⟩ := exists_equiv_of_repRel i hτ
  exact hasPairEps_of_equiv i hi hi' hψ A hA B hB H

end
