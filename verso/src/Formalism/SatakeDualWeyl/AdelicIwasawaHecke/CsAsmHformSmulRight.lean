import Formalism.SatakeDualWeyl.DefsCS
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bridge
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.LevelSubgroupFiniteAdelicStandard

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.UG.P

open Formalism.UG Formalism.UG.CS

/- English proof (translation)
Replace the relevant objects with their definitions. Simplify using the standard rewrite rules.
-/
theorem csAsm_hform_smul_right {E : Type} [Field E] (σ : E →+* E) {n : Type} [Fintype n]
    (J : Matrix n n E) (c : E) (y x : n → E) :
    hform σ J y (c • x) = c * hform σ J y x := by
  unfold Formalism.UG.hform
  simp [Matrix.mulVec_smul, dotProduct_smul, Finset.mul_sum, smul_eq_mul, mul_left_comm]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
theorem csAsm_gmap_mul {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
    [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V] (a b : V ≃ₗ[K] V)
    (L : Submodule R V) :
    Formalism.HermitianLatticesTheory.gmap (a * b) L = Formalism.HermitianLatticesTheory.gmap a (Formalism.HermitianLatticesTheory.gmap b L) := by
  unfold Formalism.HermitianLatticesTheory.gmap
  rw [← Submodule.map_comp]
  first
  | rfl
  | (congr 1; ext x; simp [LinearEquiv.mul_apply])

/- English proof (translation)
Replace the relevant objects with their definitions. Simplify using the standard rewrite rules.
-/
theorem csAsm_gmap_one {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
    [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V] (L : Submodule R V) :
    Formalism.HermitianLatticesTheory.gmap (1 : V ≃ₗ[K] V) L = L := by
  unfold Formalism.HermitianLatticesTheory.gmap
  simp

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem csAsm_gmap_inv {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
    [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V] (a : V ≃ₗ[K] V)
    (L : Submodule R V) :
    Formalism.HermitianLatticesTheory.gmap a⁻¹ (Formalism.HermitianLatticesTheory.gmap a L) = L := by
  rw [← csAsm_gmap_mul, inv_mul_cancel, csAsm_gmap_one]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Treat this case separately. Treat this case separately.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Equip the data with the indicated structure. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion.

Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. A detailed English derivation is pending.
-/
theorem classSetFiniteL_of (hSigmaInvol : Formalism.UG.CS.SigmaInvol) (hTracePos : Formalism.UG.CS.TracePos)
    (hFormSymm : Formalism.UG.CS.FormSymm) (hIsomUJ : Formalism.UG.CS.IsomUJ)
    (hGlobLatLattice : Formalism.UG.CS.GlobLatLattice) (hClassInj : Formalism.UG.CS.ClassInj)
    (hScaleBound : Formalism.UG.CS.ScaleBound) (hDualBound : Formalism.UG.CS.DualBound)
    (hClassSetFiniteBdd : Formalism.UG.CS.ClassSetFiniteBdd) (hStdLatFull : Formalism.UG.CS.StdLatFull) :
    Formalism.UG.ClassSetFiniteL := by
  intro F E _ _ _ _ _ n _ _ σ J hσ hJ hdet hdef Λ hfin hspan
  have hinv : ∀ e, (σ : E →+* E) ((σ : E →+* E) e) = e := fun e => hSigmaInvol F E σ hσ e
  obtain ⟨c, hc0, hcpos⟩ := hTracePos F E n σ J hdef
  set cE : E := algebraMap F E (c : F) with hcE
  have hσc : (σ : E →+* E) cE = cE := by
    rw [hcE]
    exact σ.commutes _
  have hcF : ((c : 𝓞 F) : F) ≠ 0 := by
    intro h
    apply hc0
    first
    | exact_mod_cast h
    | exact RingOfIntegers.ext h
  have hcE0 : cE ≠ 0 := by
    rw [hcE]
    exact (map_ne_zero _).mpr hcF
  set cO : 𝓞 E := algebraMap (𝓞 F) (𝓞 E) c with hcO
  have hcOE : algebraMap (𝓞 E) E cO = cE := by
    rw [hcO, hcE, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) F E]
  have hcO0 : cO ≠ 0 := by
    intro h
    apply hcE0
    rw [← hcOE, h, map_zero]
  letI : StarRing E := starOfInv (σ : E →+* E) hinv
  obtain ⟨hsymm, hfe⟩ := hFormSymm E (σ : E →+* E) hinv n J cE hσc hJ
  obtain ⟨d, hd0, hd⟩ := hScaleBound F E n σ J Λ hfin hspan
  obtain ⟨e, he0, he⟩ := hDualBound F E n σ J Λ hdet hfin hspan
  have hpos : ∀ x : n → E, x ≠ 0 → 0 < Algebra.trace ℚ E (formJ (σ : E →+* E) hinv J cE x x) := by
    intro x hx
    rw [hfe]
    exact hcpos x hx
  obtain ⟨s, hs⟩ := hClassSetFiniteBdd E (n → E) (formJ (σ : E →+* E) hinv J cE) hsymm hpos d (e * cO) hd0
    (mul_ne_zero he0 hcO0)
  have key : ∀ g : UPts σ J (FiniteAdeleRing (𝓞 F) F), ∃ N ∈ s, ∃ φ ∈ Formalism.HermitianLatticesTheory.isom (formJ (σ : E →+* E) hinv J cE),
      Formalism.HermitianLatticesTheory.gmap φ N = globLat (g : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) Λ := by
    intro g
    apply hs
    · exact hGlobLatLattice F E n Λ hfin hspan g
    · intro x hx y hy
      rw [hfe, Submodule.mem_one]
      obtain ⟨o, ho⟩ := hd g g.2 x hx y hy
      refine ⟨o * cO, ?_⟩
      rw [map_mul, ho, hcOE]
      show algebraMap (𝓞 E) E d * hform (σ : E →+* E) J x y * cE = algebraMap (𝓞 E) E d * (cE * hform (σ : E →+* E) J x y)
      ring
    · intro x hx
      simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
        LinearMap.restrictScalars_apply, Submodule.mem_one] at hx
      have hx' : ∀ y ∈ globLat (g : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) Λ,
          hform (σ : E →+* E) J y (cE • x) ∈ (algebraMap (𝓞 E) E).range := by
        intro y hy
        obtain ⟨o, ho⟩ := hx y hy
        rw [hfe] at ho
        refine ⟨o, ?_⟩
        rw [csAsm_hform_smul_right]
        exact ho
      have h2 := he g g.2 (cE • x) hx'
      convert h2 using 1
      show algebraMap (𝓞 E) E (e * cO) • x = algebraMap (𝓞 E) E e • cE • x
      rw [map_mul, hcOE, smul_smul]
  classical
  choose N hN φ hφ hφN using key
  let f : ClassSet ((ratPts σ J (FiniteAdeleRing (𝓞 F) F)).subgroupOf (UPts σ J (FiniteAdeleRing (𝓞 F) F)))
      ((levelAfL σ J Λ).subgroupOf (UPts σ J (FiniteAdeleRing (𝓞 F) F))) → s :=
    fun q => ⟨N (Quotient.out q), hN (Quotient.out q)⟩
  have hf : Function.Injective f := by
    intro q1 q2 h12
    have hNN : N (Quotient.out q1) = N (Quotient.out q2) := congrArg Subtype.val h12
    obtain ⟨γ, hγ⟩ : ∃ γ : GL n E, glEquiv γ = φ (Quotient.out q1) * (φ (Quotient.out q2))⁻¹ :=
      ⟨Matrix.GeneralLinearGroup.toLin.symm ((LinearMap.GeneralLinearGroup.generalLinearEquiv E (n → E)).symm
        (φ (Quotient.out q1) * (φ (Quotient.out q2))⁻¹)), by simp [glEquiv]⟩
    have hUJ : γ ∈ UJ (σ : E →+* E) J :=
      (hIsomUJ E (σ : E →+* E) hinv n J cE hcE0 hσc γ).mpr (by
        rw [hγ]
        exact mul_mem (hφ _) (inv_mem (hφ _)))
    have hlat : globLat ((Quotient.out q1 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) Λ =
        Formalism.HermitianLatticesTheory.gmap (glEquiv γ) (globLat ((Quotient.out q2 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) :
          GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) Λ) := by
      rw [hγ, csAsm_gmap_mul, ← hφN (Quotient.out q2), csAsm_gmap_inv, ← hNN, hφN]
    have h3 := hClassInj F E n σ J Λ hfin hspan (Quotient.out q1) (Quotient.out q2) γ hUJ hlat
    rwa [DoubleCoset.out_eq', DoubleCoset.out_eq'] at h3
  exact Finite.of_injective f hf

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments.

Reduce the claim to the hypotheses of an applicable result. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components.

Supply the required witnesses or components. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem classSetFinite_of (hSigmaInvol : Formalism.UG.CS.SigmaInvol) (hTracePos : Formalism.UG.CS.TracePos)
    (hFormSymm : Formalism.UG.CS.FormSymm) (hIsomUJ : Formalism.UG.CS.IsomUJ)
    (hGlobLatLattice : Formalism.UG.CS.GlobLatLattice) (hClassInj : Formalism.UG.CS.ClassInj)
    (hScaleBound : Formalism.UG.CS.ScaleBound) (hDualBound : Formalism.UG.CS.DualBound)
    (hClassSetFiniteBdd : Formalism.UG.CS.ClassSetFiniteBdd) (hStdLatFull : Formalism.UG.CS.StdLatFull) :
    Formalism.UG.ClassSetFinite := by
  intro F E _ _ _ _ _ n _ _ σ J hσ hJ hdet hdef
  have h := classSetFiniteL_of hSigmaInvol hTracePos hFormSymm hIsomUJ hGlobLatLattice hClassInj hScaleBound
    hDualBound hClassSetFiniteBdd hStdLatFull F E n σ J hσ hJ hdet hdef (stdLat (n := n) (A := E) (𝓞 E))
    (hStdLatFull E n).1 (hStdLatFull E n).2
  have heq : levelAfL σ J (stdLat (n := n) (A := E) (𝓞 E)) = levelAf σ J := by
    unfold Formalism.UG.levelAfL Formalism.UG.levelAf
    congr 1
    apply le_antisymm
    · unfold Formalism.UG.latS
      rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      simp only [SetLike.mem_coe, Formalism.UG.stdLat, Submodule.mem_pi, Set.mem_univ, true_implies,
        LinearMap.mem_range] at hx ⊢
      intro i
      obtain ⟨a, ha⟩ := hx i
      exact ⟨⟨inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x i),
        Subring.subset_closure (Or.inl ⟨⟨x i, a, ha⟩, rfl⟩)⟩, rfl⟩
    · intro v hv
      simp only [Formalism.UG.stdLat, Submodule.mem_pi, Set.mem_univ, true_implies,
        LinearMap.mem_range] at hv
      unfold Formalism.UG.latS
      rw [pi_eq_sum_univ v]
      refine Submodule.sum_mem _ (fun i _ => ?_)
      obtain ⟨y, hy⟩ := hv i
      have hy' : (y : E ⊗[F] FiniteAdeleRing (𝓞 F) F) = v i := hy
      have hsm : (v i • fun j => if i = j then (1 : E ⊗[F] FiniteAdeleRing (𝓞 F) F) else 0) =
          y • (fun j => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (if i = j then (1 : E) else 0)) := by
        ext j
        simp only [Pi.smul_apply, smul_eq_mul, Subring.smul_def]
        rw [← hy']
        split_ifs <;> simp
      rw [hsm]
      refine Submodule.smul_mem _ y (Submodule.subset_span ⟨fun j => if i = j then (1 : E) else 0, ?_, rfl⟩)
      simp only [SetLike.mem_coe, Formalism.UG.stdLat, Submodule.mem_pi, Set.mem_univ, true_implies,
        LinearMap.mem_range]
      intro j
      split_ifs
      · exact ⟨1, by simp⟩
      · exact ⟨0, by simp⟩
  rw [heq] at h
  exact h

end Formalism.UG.P
