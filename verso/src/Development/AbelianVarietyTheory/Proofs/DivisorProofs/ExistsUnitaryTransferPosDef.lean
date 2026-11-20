import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStableComplBot
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoDefiniteUnitaryAdelicUnitaryGroupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteUnitaryPointSelfDualToOrthonormalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteUnitaryLocalPointsTransferIffStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperspecialStabilizerTransferConjSelfDualLatticStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivAtSelfDualLatticeIffHasElementaryDivisorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSameDoubleCosetOfHasElementaryDivisorsDefinitStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR.Mult Formalism.UG GlobalTheory.SphPar GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefTransfer
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.DefTransfer

/- English proof (translation)
Introduce `D _ V c hloc hhyp hdiv hcart P d R hR`. Take `⟨e, f, ϖ, α, -, hef, hϖ1, hϖ2, -, -, -, hαf, hαd, -, hrep⟩` from `hR`. Establish `hK : ∀ k, k ∈ {k | k ∈ KsphC V ∅ ∧ SuppF V f k} ↔ c.symm k ∈ KP V.rank P`. Introduce `k`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨hk1, hk2⟩`. Use `(hhyp P _).1 ?_` and prove the remaining obligations. Rewrite using `[c.apply_symm_apply]`. Conclude with `⟨hk1, e, f, hef, hk2⟩`. Introduce `hk`.

Establish `h1` using `(hhyp P _).2 hk`. Rewrite `h1` using `[c.apply_symm_apply]`. Establish `h2` using `(hloc P e f hef _).1 hk.1`. Rewrite `h2` using `[c.apply_symm_apply]`. Conclude with `⟨h1.1, h2.2⟩`.

Establish `hK1 : (1 : GA D V) ∈ {k | k ∈ KsphC V ∅ ∧ SuppF V f k}`. Use `(hK 1).2 ?_` and prove the remaining obligations. Rewrite using `[map_one]`. Conclude with `⟨Subgroup.one_mem _, by rw [map_one]; exact Subgroup.one_mem _⟩`. Establish `hKG : ∀ k, k ∈ {k | k ∈ KsphC V ∅ ∧ SuppF V f k} → k ∈ GfC V` using `fun k hk => hk.1.1`.

Take `⟨γ0, ⟨hγ0R, -⟩, -⟩` from `hrep.2 α ⟨1, hK1, 1, hK1, by simp⟩`. Take `⟨hγ0G, k₁, hk₁, k₂, hk₂, hγ0⟩` from `hrep.1 γ0 hγ0R`. Establish `hαG : α ∈ GfC V`. Establish `: α = k₁⁻¹ * γ0 * k₂⁻¹` using `by rw [hγ0]; group`. Rewrite using `[this]`.

Conclude with `Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hKG _ hk₁)) hγ0G) (Subgroup.inv_mem _ (hKG _ hk₂))`. Establish `hαloc : c.symm α ∈ locU V.rank P` using `(hloc P e f hef _).2 ⟨by rw [c.apply_symm_apply]; exact hαG, by rw [c.apply_symm_apply]; exact hαf⟩`. Take `⟨-, hαdiv⟩` from `(hdiv P e f ϖ d _ hef hϖ1 hϖ2 hαloc).1 (by rw [c.apply_symm_apply]; exact hαd)`. Establish `hinv : ∀ x k₁ k₂, k₁ ∈ KP V.rank P → k₂ ∈ KP V.rank P → HasDiv (Ov D.host.E P) d (cLoc P x) → HasDiv (Ov D.host.E P) d (cLoc P (k₁ * x * k₂))`. Introduce and unpack `x k₁ k₂ hk₁ hk₂ ⟨u, hu, a, ha, b, hb, h⟩`.

Use `⟨u, hu, cLoc P k₁ * a, Subgroup.mul_mem _ hk₁.2 ha, b * cLoc P k₂, Subgroup.mul_mem _ hb hk₂.2, ?_⟩` and prove the remaining obligations. Simplify using `only [map_mul, Units.val_mul, h, Matrix.mul_assoc]`. Use `⟨fun γ hγ => ?_, fun x hx hxd => ?_⟩` and prove the remaining obligations. Take `⟨-, k₁, hk₁, k₂, hk₂, rfl⟩` from `hrep.1 γ hγ`. Establish `e1 : c.symm (k₁ * α * k₂) = c.symm k₁ * c.symm α * c.symm k₂` using `by simp only [map_mul]`.

Rewrite using `[e1]`. Establish `hk₁'` using `(hK _).1 hk₁`. Establish `hk₂'` using `(hK _).1 hk₂`. Conclude with `⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hk₁'.1 hαloc) hk₂'.1, hinv _ _ _ hk₁' hk₂' hαdiv⟩`. Take `⟨k₁, hk₁, k₂, hk₂, hxe⟩` from `hcart P d _ x hαloc hx hαdiv hxd`.

Establish `hcx : c x = c k₁ * α * c k₂` using `by rw [hxe]; simp only [map_mul, c.apply_symm_apply]`. Establish `hk₁' : c k₁ ∈ {k | k ∈ KsphC V ∅ ∧ SuppF V f k}` using `(hK _).2 (by rwa [c.symm_apply_apply])`. Establish `hk₂' : c k₂ ∈ {k | k ∈ KsphC V ∅ ∧ SuppF V f k}` using `(hK _).2 (by rwa [c.symm_apply_apply])`. Establish `hconv : ∀ γ, γ⁻¹ * c x ∈ {k | k ∈ KsphC V ∅ ∧ SuppF V f k} ↔ (c.symm γ)⁻¹ * x ∈ KP V.rank P`. Introduce `γ`.

Rewrite using `[hK]`. Simplify using `only [map_mul, map_inv, c.symm_apply_apply]`. Take `⟨γ, ⟨hγR, hγK⟩, huniq⟩` from `hrep.2 (c x) ⟨_, hk₁', _, hk₂', hcx⟩`. Conclude with `⟨γ, ⟨hγR, (hconv γ).1 hγK⟩, fun γ' hγ' => huniq γ' ⟨hγ'.1, (hconv γ').2 hγ'.2⟩⟩`.
-/
theorem sphOp_of_local : ∀ (D : D7) [IsCMField D.host.E] (V : HSp D) (c : UA D.host.E V.rank ≃* GA D V),
    (∀ (P : HeightOneSpectrum (𝓞 D.host.E)) e f, IsPrimeIdem P e f → ∀ x,
      x ∈ locU V.rank P ↔ c x ∈ GfC V ∧ SuppF V f (c x)) →
    (∀ (P : HeightOneSpectrum (𝓞 D.host.E)) x, c x ∈ GlobalTheory.Hk3.hyp V P ↔ x ∈ KP V.rank P) →
    (∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (e f : AE D) (ϖ : 𝓞 D.host.E) (d : List ℤ) (x : UA D.host.E V.rank),
      IsPrimeIdem P e f → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → x ∈ locU V.rank P →
      (DivAt V e (ϖ : D.host.E) d (c x) ↔ d.length = V.rank ∧ HasDiv (Ov D.host.E P) d (cLoc P x))) →
    (∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ) (x y : UA D.host.E V.rank), x ∈ locU V.rank P →
      y ∈ locU V.rank P → HasDiv (Ov D.host.E P) d (cLoc P x) → HasDiv (Ov D.host.E P) d (cLoc P y) →
      ∃ k₁ ∈ KP V.rank P, ∃ k₂ ∈ KP V.rank P, y = k₁ * x * k₂) →
    ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) d R, GlobalTheory.Hk3.SphOp V P d R →
      (∀ γ ∈ R, c.symm γ ∈ locU V.rank P ∧ HasDiv (Ov D.host.E P) d (cLoc P (c.symm γ))) ∧
      ∀ x ∈ locU V.rank P, HasDiv (Ov D.host.E P) d (cLoc P x) →
        ∃! γ, γ ∈ R ∧ (c.symm γ)⁻¹ * x ∈ KP V.rank P := by
  intro D _ V c hloc hhyp hdiv hcart P d R hR
  obtain ⟨e, f, ϖ, α, -, hef, hϖ1, hϖ2, -, -, -, hαf, hαd, -, hrep⟩ := hR
  have hK : ∀ k, k ∈ {k | k ∈ KsphC V ∅ ∧ SuppF V f k} ↔ c.symm k ∈ KP V.rank P := by
    intro k
    constructor
    · rintro ⟨hk1, hk2⟩
      refine (hhyp P _).1 ?_
      rw [c.apply_symm_apply]
      exact ⟨hk1, e, f, hef, hk2⟩
    · intro hk
      have h1 := (hhyp P _).2 hk
      rw [c.apply_symm_apply] at h1
      have h2 := (hloc P e f hef _).1 hk.1
      rw [c.apply_symm_apply] at h2
      exact ⟨h1.1, h2.2⟩
  have hK1 : (1 : GA D V) ∈ {k | k ∈ KsphC V ∅ ∧ SuppF V f k} := by
    refine (hK 1).2 ?_
    rw [map_one]
    exact ⟨Subgroup.one_mem _, by rw [map_one]; exact Subgroup.one_mem _⟩
  have hKG : ∀ k, k ∈ {k | k ∈ KsphC V ∅ ∧ SuppF V f k} → k ∈ GfC V := fun k hk => hk.1.1
  obtain ⟨γ0, ⟨hγ0R, -⟩, -⟩ := hrep.2 α ⟨1, hK1, 1, hK1, by simp⟩
  obtain ⟨hγ0G, k₁, hk₁, k₂, hk₂, hγ0⟩ := hrep.1 γ0 hγ0R
  have hαG : α ∈ GfC V := by
    have : α = k₁⁻¹ * γ0 * k₂⁻¹ := by rw [hγ0]; group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hKG _ hk₁)) hγ0G) (Subgroup.inv_mem _ (hKG _ hk₂))
  have hαloc : c.symm α ∈ locU V.rank P :=
    (hloc P e f hef _).2 ⟨by rw [c.apply_symm_apply]; exact hαG, by rw [c.apply_symm_apply]; exact hαf⟩
  obtain ⟨-, hαdiv⟩ := (hdiv P e f ϖ d _ hef hϖ1 hϖ2 hαloc).1 (by rw [c.apply_symm_apply]; exact hαd)
  have hinv : ∀ x k₁ k₂, k₁ ∈ KP V.rank P → k₂ ∈ KP V.rank P → HasDiv (Ov D.host.E P) d (cLoc P x) →
      HasDiv (Ov D.host.E P) d (cLoc P (k₁ * x * k₂)) := by
    rintro x k₁ k₂ hk₁ hk₂ ⟨u, hu, a, ha, b, hb, h⟩
    refine ⟨u, hu, cLoc P k₁ * a, Subgroup.mul_mem _ hk₁.2 ha, b * cLoc P k₂, Subgroup.mul_mem _ hb hk₂.2, ?_⟩
    simp only [map_mul, Units.val_mul, h, Matrix.mul_assoc]
  refine ⟨fun γ hγ => ?_, fun x hx hxd => ?_⟩
  · obtain ⟨-, k₁, hk₁, k₂, hk₂, rfl⟩ := hrep.1 γ hγ
    have e1 : c.symm (k₁ * α * k₂) = c.symm k₁ * c.symm α * c.symm k₂ := by simp only [map_mul]
    rw [e1]
    have hk₁' := (hK _).1 hk₁
    have hk₂' := (hK _).1 hk₂
    exact ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hk₁'.1 hαloc) hk₂'.1, hinv _ _ _ hk₁' hk₂' hαdiv⟩
  · obtain ⟨k₁, hk₁, k₂, hk₂, hxe⟩ := hcart P d _ x hαloc hx hαdiv hxd
    have hcx : c x = c k₁ * α * c k₂ := by rw [hxe]; simp only [map_mul, c.apply_symm_apply]
    have hk₁' : c k₁ ∈ {k | k ∈ KsphC V ∅ ∧ SuppF V f k} := (hK _).2 (by rwa [c.symm_apply_apply])
    have hk₂' : c k₂ ∈ {k | k ∈ KsphC V ∅ ∧ SuppF V f k} := (hK _).2 (by rwa [c.symm_apply_apply])
    have hconv : ∀ γ, γ⁻¹ * c x ∈ {k | k ∈ KsphC V ∅ ∧ SuppF V f k} ↔ (c.symm γ)⁻¹ * x ∈ KP V.rank P := by
      intro γ
      rw [hK]
      simp only [map_mul, map_inv, c.symm_apply_apply]
    obtain ⟨γ, ⟨hγR, hγK⟩, huniq⟩ := hrep.2 (c x) ⟨_, hk₁', _, hk₂', hcx⟩
    exact ⟨γ, ⟨hγR, (hconv γ).1 hγK⟩, fun γ' hγ' => huniq γ' ⟨hγ'.1, (hconv γ').2 hγ'.2⟩⟩

/- English proof (translation)
Introduce `D _ V θ hθ hs hp`. Take `⟨j, M, hM, hrat, hfin, hinf, hA, hform⟩` from `GlobalTheory.T.exists_iso_definiteUnitary_adelicUnitaryGroup D V θ hθ hs hp`. Take `⟨h₀, hh₀, hlat⟩` from `GlobalTheory.T.exists_finite_unitary_point_selfDual_to_orthonormal D V M hM`. Take `⟨hex, hloc⟩` from `GlobalTheory.T.definiteUnitary_localPoints_transfer_iff D V j h₀ M hM hh₀ hfin hform hlat`. Establish `hhyp` using `GlobalTheory.T.hyperspecial_stabilizer_transfer_conj_selfDual_lattice D V j h₀ M hM hh₀ hfin hform hlat hloc`.

Establish `hdiv` using `GlobalTheory.T.divAt_selfDual_lattice_iff_hasElementaryDivisors D V j h₀ M hM hh₀ hfin hform hlat`. Use `⟨j, h₀, hh₀, hrat, hfin, hinf, hA, fun P x => ?_, hhyp, ?_⟩` and prove the remaining obligations. Take `⟨e, f, hef⟩` from `hex P`. Prove the components needed by the constructor for the conclusion. Introduce `hx`.

Take `⟨h1, h2⟩` from `(hloc P e f hef x).1 hx`. Conclude with `⟨h1, e, f, hef, h2⟩`. Introduce and unpack `⟨h1, e', f', hef', h2⟩`. Conclude with `(hloc P e' f' hef' x).2 ⟨h1, h2⟩`. Conclude with `sphOp_of_local D V (cj j h₀) hloc hhyp hdiv (fun P d x y => GlobalTheory.T.mem_sameDoubleCoset_of_hasElementaryDivisors_definiteUnitary D V.rank P d x y)`.
-/
theorem exists_isTransfer : ∀ (D : D7) [IsCMField D.host.E] (V : HSp D) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)),
    IsInfFam θ → V.SigOK → V.IsPosDef → ∃ (j : UA D.host.E V.rank ≃ₜ* GA D V) (h₀ : GA D V), IsTransfer V θ j h₀ := by
  intro D _ V θ hθ hs hp
  obtain ⟨j, M, hM, hrat, hfin, hinf, hA, hform⟩ := GlobalTheory.T.exists_iso_definiteUnitary_adelicUnitaryGroup D V θ hθ hs hp
  obtain ⟨h₀, hh₀, hlat⟩ := GlobalTheory.T.exists_finite_unitary_point_selfDual_to_orthonormal D V M hM
  obtain ⟨hex, hloc⟩ := GlobalTheory.T.definiteUnitary_localPoints_transfer_iff D V j h₀ M hM hh₀ hfin hform hlat
  have hhyp := GlobalTheory.T.hyperspecial_stabilizer_transfer_conj_selfDual_lattice D V j h₀ M hM hh₀ hfin hform hlat hloc
  have hdiv := GlobalTheory.T.divAt_selfDual_lattice_iff_hasElementaryDivisors D V j h₀ M hM hh₀ hfin hform hlat
  refine ⟨j, h₀, hh₀, hrat, hfin, hinf, hA, fun P x => ?_, hhyp, ?_⟩
  · obtain ⟨e, f, hef⟩ := hex P
    constructor
    · intro hx
      obtain ⟨h1, h2⟩ := (hloc P e f hef x).1 hx
      exact ⟨h1, e, f, hef, h2⟩
    · rintro ⟨h1, e', f', hef', h2⟩
      exact (hloc P e' f' hef' x).2 ⟨h1, h2⟩
  · exact sphOp_of_local D V (cj j h₀) hloc hhyp hdiv (fun P d x y => GlobalTheory.T.mem_sameDoubleCoset_of_hasElementaryDivisors_definiteUnitary D V.rank P d x y)

end GlobalTheory.DefTransfer

end
