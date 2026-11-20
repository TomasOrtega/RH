import Formalism.SatakeDualWeyl.DefsCS
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bridge
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.LevelSubgroupFiniteAdelicStandard

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.UG.P

open Formalism.UG Formalism.UG.CS

/- English proof (translation)
Unfold `Formalism.UG.hform`. Simplify using `[Matrix.mulVec_smul, dotProduct_smul, Finset.mul_sum, smul_eq_mul, mul_left_comm]`.
-/
theorem csAsm_hform_smul_right {E : Type} [Field E] (σ : E →+* E) {n : Type} [Fintype n]
    (J : Matrix n n E) (c : E) (y x : n → E) :
    hform σ J y (c • x) = c * hform σ J y x := by
  unfold Formalism.UG.hform
  simp [Matrix.mulVec_smul, dotProduct_smul, Finset.mul_sum, smul_eq_mul, mul_left_comm]

/- English proof (translation)
Unfold `Formalism.HermitianLatticesTheory.gmap`. Rewrite using `[← Submodule.map_comp]`. Use `first`. Consider the case `rfl`. Consider the case `(congr 1; ext x; simp [LinearEquiv.mul_apply])`.
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
Unfold `Formalism.HermitianLatticesTheory.gmap`. Simplify using the standard rewrite rules.
-/
theorem csAsm_gmap_one {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
    [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V] (L : Submodule R V) :
    Formalism.HermitianLatticesTheory.gmap (1 : V ≃ₗ[K] V) L = L := by
  unfold Formalism.HermitianLatticesTheory.gmap
  simp

/- English proof (translation)
Rewrite using `[← csAsm_gmap_mul, inv_mul_cancel, csAsm_gmap_one]`.
-/
theorem csAsm_gmap_inv {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
    [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V] (a : V ≃ₗ[K] V)
    (L : Submodule R V) :
    Formalism.HermitianLatticesTheory.gmap a⁻¹ (Formalism.HermitianLatticesTheory.gmap a L) = L := by
  rw [← csAsm_gmap_mul, inv_mul_cancel, csAsm_gmap_one]

/- English proof (translation)
Introduce `F E _ _ _ _ _ n _ _ σ J hσ hJ hdet hdef Λ hfin hspan`. Establish `hinv : ∀ e, (σ : E →+* E) ((σ : E →+* E) e) = e` using `fun e => hSigmaInvol F E σ hσ e`. Take `⟨c, hc0, hcpos⟩` from `hTracePos F E n σ J hdef`. Use `set cE : E := algebraMap F E (c : F) with hcE`. Establish `hσc : (σ : E →+* E) cE = cE`.

Rewrite using `[hcE]`. Conclude with `σ.commutes _`. Establish `hcF : ((c : 𝓞 F) : F) ≠ 0`. Introduce `h`. Apply `hc0` to reduce the goal to its premises.

Use `first`. Consider the case `exact_mod_cast h`. Consider the case `exact RingOfIntegers.ext h`. Establish `hcE0 : cE ≠ 0`. Rewrite using `[hcE]`.

Conclude with `(map_ne_zero _).mpr hcF`. Use `set cO : 𝓞 E := algebraMap (𝓞 F) (𝓞 E) c with hcO`. Establish `hcOE : algebraMap (𝓞 E) E cO = cE`. Rewrite using `[hcO, hcE, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) F E]`. Establish `hcO0 : cO ≠ 0`.

Introduce `h`. Apply `hcE0` to reduce the goal to its premises. Rewrite using `[← hcOE, h, map_zero]`. Use `letI : StarRing E := starOfInv (σ : E →+* E) hinv`. Take `⟨hsymm, hfe⟩` from `hFormSymm E (σ : E →+* E) hinv n J cE hσc hJ`.

Take `⟨d, hd0, hd⟩` from `hScaleBound F E n σ J Λ hfin hspan`. Take `⟨e, he0, he⟩` from `hDualBound F E n σ J Λ hdet hfin hspan`. Establish `hpos : ∀ x : n → E, x ≠ 0 → 0 < Algebra.trace ℚ E (formJ (σ : E →+* E) hinv J cE x x)`. Introduce `x hx`. Rewrite using `[hfe]`.

Conclude with `hcpos x hx`. Take `⟨s, hs⟩` from `hClassSetFiniteBdd E (n → E) (formJ (σ : E →+* E) hinv J cE) hsymm hpos d (e * cO) hd0 (mul_ne_zero he0 hcO0)`. Establish `key : ∀ g : UPts σ J (FiniteAdeleRing (𝓞 F) F), ∃ N ∈ s, ∃ φ ∈ Formalism.HermitianLatticesTheory.isom (formJ (σ : E →+* E) hinv J cE), Formalism.HermitianLatticesTheory.gmap φ N = globLat (g : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) Λ`. Introduce `g`. Apply `hs` to reduce the goal to its premises.

Conclude with `hGlobLatLattice F E n Λ hfin hspan g`. Introduce `x hx y hy`. Rewrite using `[hfe, Submodule.mem_one]`. Take `⟨o, ho⟩` from `hd g g.2 x hx y hy`. Use `⟨o * cO, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_mul, ho, hcOE]`. Use `show algebraMap (𝓞 E) E d * hform (σ : E →+* E) J x y * cE = algebraMap (𝓞 E) E d * (cE * hform (σ : E →+* E) J x y)`. Expand and normalize the polynomial expressions, which then agree. Introduce `x hx`. Simplify using `only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply, Submodule.mem_one] at hx`.

Establish `hx' : ∀ y ∈ globLat (g : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) Λ, hform (σ : E →+* E) J y (cE • x) ∈ (algebraMap (𝓞 E) E).range`. Introduce `y hy`. Take `⟨o, ho⟩` from `hx y hy`. Rewrite `ho` using `[hfe]`. Use `⟨o, ?_⟩` and prove the remaining obligations.

Rewrite using `[csAsm_hform_smul_right]`. Conclude with `ho`. Establish `h2` using `he g g.2 (cE • x) hx'`. Use `h2 using 1` and compare the differences between its conclusion and the goal. Use `show algebraMap (𝓞 E) E (e * cO) • x = algebraMap (𝓞 E) E e • cE • x`.

Rewrite using `[map_mul, hcOE, smul_smul]`. Use `choose N hN φ hφ hφN using key`. Set `f : ClassSet ((ratPts σ J (FiniteAdeleRing (𝓞 F) F)).subgroupOf (UPts σ J (FiniteAdeleRing (𝓞 F) F))) ((levelAfL σ J Λ).subgroupOf (UPts σ J (FiniteAdeleRing (𝓞 F) F))) → s` to `fun q => ⟨N (Quotient.out q), hN (Quotient.out q)⟩`. Establish `hf : Function.Injective f`. Introduce `q1 q2 h12`.

Establish `hNN : N (Quotient.out q1) = N (Quotient.out q2)` using `congrArg Subtype.val h12`. Take `⟨γ, hγ⟩ : ∃ γ : GL n E, glEquiv γ = φ (Quotient.out q1) * (φ (Quotient.out q2))⁻¹` from `⟨Matrix.GeneralLinearGroup.toLin.symm ((LinearMap.GeneralLinearGroup.generalLinearEquiv E (n → E)).symm (φ (Quotient.out q1) * (φ (Quotient.out q2))⁻¹)), by simp [glEquiv]⟩`. Establish `hUJ : γ ∈ UJ (σ : E →+* E) J` using `(hIsomUJ E (σ : E →+* E) hinv n J cE hcE0 hσc γ).mpr (by`. Rewrite using `[hγ]`. Conclude with `mul_mem (hφ _) (inv_mem (hφ _)))`.

Establish `hlat : globLat ((Quotient.out q1 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) Λ = Formalism.HermitianLatticesTheory.gmap (glEquiv γ) (globLat ((Quotient.out q2 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) Λ)`. Rewrite using `[hγ, csAsm_gmap_mul, ← hφN (Quotient.out q2), csAsm_gmap_inv, ← hNN, hφN]`. Establish `h3` using `hClassInj F E n σ J Λ hfin hspan (Quotient.out q1) (Quotient.out q2) γ hUJ hlat`. Rewrite `h3` using `[DoubleCoset.out_eq', DoubleCoset.out_eq']`. Then use the resulting hypothesis. Conclude with `Finite.of_injective f hf`.
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
Introduce `F E _ _ _ _ _ n _ _ σ J hσ hJ hdet hdef`. Establish `h` using `classSetFiniteL_of hSigmaInvol hTracePos hFormSymm hIsomUJ hGlobLatLattice hClassInj hScaleBound hDualBound hClassSetFiniteBdd hStdLatFull F E n σ J hσ hJ hdet hdef (stdLat (n := n) (A := E) (𝓞 E)) (hStdLatFull E n).1 (hStdLatFull E n).2`. Establish `heq : levelAfL σ J (stdLat (n` using `n) (A := E) (𝓞 E)) = levelAf σ J := by`. Unfold `Formalism.UG.levelAfL Formalism.UG.levelAf`. Use `congr 1`.

Apply `le_antisymm` to reduce the goal to its premises. Unfold `Formalism.UG.latS`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Simplify using `only [SetLike.mem_coe, Formalism.UG.stdLat, Submodule.mem_pi, Set.mem_univ, true_implies, LinearMap.mem_range] at hx ⊢`.

Introduce `i`. Take `⟨a, ha⟩` from `hx i`. Conclude with `⟨⟨inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x i), Subring.subset_closure (Or.inl ⟨⟨x i, a, ha⟩, rfl⟩)⟩, rfl⟩`. Introduce `v hv`. Simplify using `only [Formalism.UG.stdLat, Submodule.mem_pi, Set.mem_univ, true_implies, LinearMap.mem_range] at hv`.

Unfold `Formalism.UG.latS`. Rewrite using `[pi_eq_sum_univ v]`. Use `Submodule.sum_mem _ (fun i _ => ?_)` and prove the remaining obligations. Take `⟨y, hy⟩` from `hv i`. Establish `hy' : (y : E ⊗[F] FiniteAdeleRing (𝓞 F) F) = v i` using `hy`.

Establish `hsm : (v i • fun j => if i = j then (1 : E ⊗[F] FiniteAdeleRing (𝓞 F) F) else 0) = y • (fun j => inclE (F` using `F) (FiniteAdeleRing (𝓞 F) F) (if i = j then (1 : E) else 0)) := by`. Use extensionality with `j`. Simplify using `only [Pi.smul_apply, smul_eq_mul, Subring.smul_def]`. Rewrite using `[← hy']`. Apply the tactic sequence `split_ifs <;> simp`.

Rewrite using `[hsm]`. Use `Submodule.smul_mem _ y (Submodule.subset_span ⟨fun j => if i = j then (1 : E) else 0, ?_, rfl⟩)` and prove the remaining obligations. Simplify using `only [SetLike.mem_coe, Formalism.UG.stdLat, Submodule.mem_pi, Set.mem_univ, true_implies, LinearMap.mem_range]`. Introduce `j`. Use `split_ifs`.

Conclude with `⟨1, by simp⟩`. Conclude with `⟨0, by simp⟩`. Rewrite `h` using `[heq]`. Conclude with `h`.
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
