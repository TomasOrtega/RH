import Mathlib
import GroundTheory.AutomorphicForms.WhittakerLSpace
import GroundTheory.AutomorphicForms.WhittakerOrbit
import GroundTheory.AutomorphicForms.WhittakerGroups
import GroundTheory.AutomorphicForms.WhittakerCells
import GroundTheory.AutomorphicForms.WhittakerRelevance

namespace GroundTheory.Automorphic

namespace Whittaker

open Set Topology MulAction Matrix DoubleCoset ValuativeRel

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] {n : ℕ}

section Action

variable (F n) in

abbrev NN := (Iwasawa.unipotent F n) × (Iwasawa.unipotent F n)

@[instance_reducible]
def biAction : MulAction (NN F n) (GL (Fin n) F) where
  smul h g := (h.1 : GL (Fin n) F) * g * (h.2 : GL (Fin n) F)⁻¹
  one_smul g := by
    show ((1 : NN F n).1 : GL (Fin n) F) * g * ((1 : NN F n).2 : GL (Fin n) F)⁻¹ = g
    simp
  mul_smul h k g := by
    show ((h * k).1 : GL (Fin n) F) * g * ((h * k).2 : GL (Fin n) F)⁻¹ =
      (h.1 : GL (Fin n) F) * ((k.1 : GL (Fin n) F) * g * (k.2 : GL (Fin n) F)⁻¹) *
        (h.2 : GL (Fin n) F)⁻¹
    simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul, _root_.mul_inv_rev]
    group

attribute [local instance] biAction

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem biAction_smul (h : NN F n) (g : GL (Fin n) F) :
    h • g = (h.1 : GL (Fin n) F) * g * (h.2 : GL (Fin n) F)⁻¹ := rfl

/- English proof (translation)
Simplify using `[transl, biAction_smul]`.
-/
theorem transl_apply_biAction (h : NN F n) (f : GL (Fin n) F → ℂ) (x : GL (Fin n) F) :
    transl h f x = f ((h.1 : GL (Fin n) F)⁻¹ * x * (h.2 : GL (Fin n) F)) := by
  simp [transl, biAction_smul]

variable (ψ₀ : AddChar F ℂ)

noncomputable def chi : NN F n →* ℂ where
  toFun h := psiN ψ₀ (h.1 : GL (Fin n) F) * (psiN ψ₀ (h.2 : GL (Fin n) F))⁻¹
  map_one' := by simp [psiN_one]
  map_mul' h k := by
    simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]
    rw [psiN_mul ψ₀ h.1.2 k.1.2, psiN_mul ψ₀ h.2.2 k.2.2, mul_inv]
    ring

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem chi_apply (h : NN F n) :
    chi ψ₀ h = psiN ψ₀ (h.1 : GL (Fin n) F) * (psiN ψ₀ (h.2 : GL (Fin n) F))⁻¹ := rfl

def swapTheta (h : NN F n) : NN F n := (thetaN h.2, thetaN h.1)

/- English proof (translation)
Simplify using `only [chi_apply, swapTheta, coe_thetaN, psiN_theta ψ₀ h.1.2, psiN_theta ψ₀ h.2.2, inv_inv]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem chi_swapTheta (h : NN F n) : chi ψ₀ (swapTheta h) = chi ψ₀ h := by
  simp only [chi_apply, swapTheta, coe_thetaN, psiN_theta ψ₀ h.1.2, psiN_theta ψ₀ h.2.2, inv_inv]
  ring

omit ψ₀ in
/- English proof (translation)
Apply the tactic sequence `refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_) <;> simp [swapTheta, coe_thetaN, theta_theta]`.
-/
theorem swapTheta_swapTheta (h : NN F n) : swapTheta (swapTheta h) = h := by
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_) <;> simp [swapTheta, coe_thetaN, theta_theta]

omit ψ₀ in
/- English proof (translation)
Simplify using `[swapTheta, map_inv]`.
-/
theorem swapTheta_inv (h : NN F n) : swapTheta h⁻¹ = (swapTheta h)⁻¹ := by
  simp [swapTheta, map_inv]

omit ψ₀ in
/- English proof (translation)
Simplify using `only [biAction_smul, swapTheta, coe_thetaN]`. Rewrite using `[sigma_mul_mul_inv]`.
-/
theorem sigma_smul (h : NN F n) (g : GL (Fin n) F) : sigma (h • g) = swapTheta h • sigma g := by
  simp only [biAction_smul, swapTheta, coe_thetaN]
  rw [sigma_mul_mul_inv]

end Action

attribute [local instance] biAction

section Pull

variable [TopologicalSpace F] [IsTopologicalRing F]

def sigmaL : (GL (Fin n) F → ℂ) →ₗ[ℂ] (GL (Fin n) F → ℂ) := LinearMap.funLeft ℂ ℂ sigma

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sigmaL_apply (f : GL (Fin n) F → ℂ) (x : GL (Fin n) F) : sigmaL f x = f (sigma x) := rfl

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `[sigmaL_apply, sigma_sigma]`.
-/
theorem sigmaL_sigmaL (f : GL (Fin n) F → ℂ) : sigmaL (sigmaL f) = f := by
  funext x
  simp [sigmaL_apply, sigma_sigma]

/- English proof (translation)
Use `⟨⟨hf.1.1.comp_continuous continuous_sigma, ?_⟩, fun x hx => hf.2 hx⟩` and prove the remaining obligations. Conclude with `hf.1.2.comp_homeomorph sigmaHomeo`.
-/
theorem sigmaL_mem_supportedIn {U : Set (GL (Fin n) F)} {f : GL (Fin n) F → ℂ}
    (hf : f ∈ supportedIn U) : sigmaL f ∈ supportedIn (sigma ⁻¹' U) := by
  refine ⟨⟨hf.1.1.comp_continuous continuous_sigma, ?_⟩, fun x hx => hf.2 hx⟩
  exact hf.1.2.comp_homeomorph sigmaHomeo

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `only [sigmaL_apply, transl_apply]`. Use `congr 1`. Rewrite using `[sigma_smul, swapTheta_inv, swapTheta_swapTheta]`.
-/
theorem sigmaL_transl (h : NN F n) (f : GL (Fin n) F → ℂ) :
    sigmaL (transl h f) = transl (swapTheta h) (sigmaL f) := by
  funext x
  simp only [sigmaL_apply, transl_apply]
  congr 1
  rw [sigma_smul, swapTheta_inv, swapTheta_swapTheta]

variable (ψ₀ : AddChar F ℂ)

/- English proof (translation)
Use `Submodule.span_mono ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨h, f, hf, rfl⟩`. Conclude with `⟨h, f, supportedIn_mono hUV hf, rfl⟩`.
-/
theorem relSpan_mono {χ : NN F n →* ℂ} {U V : Set (GL (Fin n) F)} (hUV : U ⊆ V) :
    relSpan χ U ≤ relSpan χ V := by
  refine Submodule.span_mono ?_
  rintro _ ⟨h, f, hf, rfl⟩
  exact ⟨h, f, supportedIn_mono hUV hf, rfl⟩

/- English proof (translation)
Establish `key : relSpan (chi (n` using `n) ψ₀) U ≤ (relSpan (chi (n := n) ψ₀) (sigma ⁻¹' U)).comap sigmaL := by`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨h, f, hf, rfl⟩`. Rewrite using `[SetLike.mem_coe, Submodule.mem_comap, map_sub, map_smul, sigmaL_transl, ← chi_swapTheta ψ₀ h]`. Conclude with `sub_mem_relSpan _ _ (sigmaL_mem_supportedIn hf)`.

Conclude with `key hr`.
-/
theorem sigmaL_mem_relSpan {U : Set (GL (Fin n) F)} {r : GL (Fin n) F → ℂ}
    (hr : r ∈ relSpan (chi (n := n) ψ₀) U) : sigmaL r ∈ relSpan (chi (n := n) ψ₀) (sigma ⁻¹' U) := by
  have key : relSpan (chi (n := n) ψ₀) U ≤ (relSpan (chi (n := n) ψ₀) (sigma ⁻¹' U)).comap sigmaL := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨h, f, hf, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, map_sub, map_smul, sigmaL_transl, ← chi_swapTheta ψ₀ h]
    exact sub_mem_relSpan _ _ (sigmaL_mem_supportedIn hf)
  exact key hr

noncomputable abbrev rel (n : ℕ) (ψ₀ : AddChar F ℂ) : Submodule ℂ (GL (Fin n) F → ℂ) := relSpan (chi (n := n) ψ₀) (univ : Set (GL (Fin n) F))

noncomputable def goodSub (n : ℕ) (ψ₀ : AddChar F ℂ) : Submodule ℂ (GL (Fin n) F → ℂ) := (rel n ψ₀).comap (LinearMap.id - sigmaL)

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_goodSub {f : GL (Fin n) F → ℂ} : f ∈ goodSub n ψ₀ ↔ f - sigmaL f ∈ rel n ψ₀ := Iff.rfl

end Pull

section LocalField

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/- English proof (translation)
Rewrite using `[totallyDisconnectedSpace_iff_connectedComponent_singleton]`. Introduce `x`. Use `Set.Subset.antisymm (fun y hy => ?_) (Set.singleton_subset_iff.mpr mem_connectedComponent)` and prove the remaining obligations. Establish `hball : ∀ m : ℕ, valuation F (y - x) ≤ valuation F (GLnLocal.uniformizer F : F) ^ m`. Introduce `m`.

Establish `hγ : valuation F (GLnLocal.uniformizer F : F) ^ m ≠ 0` using `pow_ne_zero _ (GLnLocal.valuation_uniformizer_ne_zero F)`. Set `S : Set F` to `(fun z => z - x) ⁻¹' {z : F | valuation F z ≤ valuation F (GLnLocal.uniformizer F : F) ^ m}`. Establish `hSo : IsOpen S` using `(GLnLocal.isOpen_valuation_le F hγ).preimage (continuous_sub_right x)`. Establish `hSc : IsClosed S` using `(IsNonarchimedeanLocalField.isCompact_closedBall F _).isClosed.preimage (continuous_sub_right x)`. Establish `hxS : x ∈ S` using `by simp [S]`.

Conclude with `IsClopen.connectedComponent_subset ⟨hSc, hSo⟩ hxS hy`. Use `GLnLocal.eq_zero_of_forall_valuation_le F hball` as an intermediate fact. Conclude with `Set.mem_singleton_iff.2 (sub_eq_zero.1 this)`.
-/
theorem totallyDisconnectedSpace_localField : TotallyDisconnectedSpace F := by
  rw [totallyDisconnectedSpace_iff_connectedComponent_singleton]
  intro x
  refine Set.Subset.antisymm (fun y hy => ?_) (Set.singleton_subset_iff.mpr mem_connectedComponent)
  have hball : ∀ m : ℕ, valuation F (y - x) ≤ valuation F (GLnLocal.uniformizer F : F) ^ m := by
    intro m
    have hγ : valuation F (GLnLocal.uniformizer F : F) ^ m ≠ 0 :=
      pow_ne_zero _ (GLnLocal.valuation_uniformizer_ne_zero F)
    let S : Set F := (fun z => z - x) ⁻¹' {z : F | valuation F z ≤
      valuation F (GLnLocal.uniformizer F : F) ^ m}
    have hSo : IsOpen S := (GLnLocal.isOpen_valuation_le F hγ).preimage (continuous_sub_right x)
    have hSc : IsClosed S :=
      (IsNonarchimedeanLocalField.isCompact_closedBall F _).isClosed.preimage
        (continuous_sub_right x)
    have hxS : x ∈ S := by simp [S]
    exact IsClopen.connectedComponent_subset ⟨hSc, hSo⟩ hxS hy
  have := GLnLocal.eq_zero_of_forall_valuation_le F hball
  exact Set.mem_singleton_iff.2 (sub_eq_zero.1 this)

attribute [local instance] totallyDisconnectedSpace_localField

/- English proof (translation)
Use `⟨?_⟩` and prove the remaining obligations. Establish `e : (fun p : NN F n × GL (Fin n) F => p.1 • p.2) = fun p => ((p.1.1 : GL (Fin n) F)) * p.2 * ((p.1.2 : GL (Fin n) F))⁻¹` using `rfl`. Rewrite using `[e]`. Establish `h1 : Continuous fun p : NN F n × GL (Fin n) F => ((p.1.1 : GL (Fin n) F))` using `continuous_subtype_val.comp (continuous_fst.comp continuous_fst)`. Establish `h2 : Continuous fun p : NN F n × GL (Fin n) F => ((p.1.2 : GL (Fin n) F))` using `continuous_subtype_val.comp (continuous_snd.comp continuous_fst)`.

Conclude with `(h1.mul continuous_snd).mul h2.inv`.
-/
theorem continuousSMul_biAction : ContinuousSMul (NN F n) (GL (Fin n) F) := by
  refine ⟨?_⟩
  have e : (fun p : NN F n × GL (Fin n) F => p.1 • p.2) = fun p =>
      ((p.1.1 : GL (Fin n) F)) * p.2 * ((p.1.2 : GL (Fin n) F))⁻¹ := rfl
  rw [e]
  have h1 : Continuous fun p : NN F n × GL (Fin n) F => ((p.1.1 : GL (Fin n) F)) :=
    continuous_subtype_val.comp (continuous_fst.comp continuous_fst)
  have h2 : Continuous fun p : NN F n × GL (Fin n) F => ((p.1.2 : GL (Fin n) F)) :=
    continuous_subtype_val.comp (continuous_snd.comp continuous_fst)
  exact (h1.mul continuous_snd).mul h2.inv

attribute [local instance] continuousSMul_biAction

def cellGe (g : GL (Fin n) F) : Set (GL (Fin n) F) := {h | ∀ i j, llRank i j g ≤ llRank i j h}

def cellLe (g : GL (Fin n) F) : Set (GL (Fin n) F) := {h | ∀ i j, llRank i j h ≤ llRank i j g}

/- English proof (translation)
The claim follows from `isOpen_setOf_forall_le_llRank _`.
-/
theorem isOpen_cellGe (g : GL (Fin n) F) : IsOpen (cellGe g) :=
  isOpen_setOf_forall_le_llRank _

/- English proof (translation)
The claim follows from `isClosed_setOf_forall_llRank_le _`.
-/
theorem isClosed_cellLe (g : GL (Fin n) F) : IsClosed (cellLe g) :=
  isClosed_setOf_forall_llRank_le _

/- English proof (translation)
The claim follows from `bruhatCell_eq_iff_llRank.2 fun i j => le_antisymm (h₂ i j) (h₁ i j)`.
-/
theorem bruhatCell_eq_of_mem {g h : GL (Fin n) F} (h₁ : h ∈ cellGe g) (h₂ : h ∈ cellLe g) :
    bruhatCell h = bruhatCell g :=
  bruhatCell_eq_iff_llRank.2 fun i j => le_antisymm (h₂ i j) (h₁ i j)

/- English proof (translation)
Introduce `i j` and use `(bruhatCell_eq_iff_llRank.1 e i j).ge`.
-/
theorem mem_cellGe_of_eq {g h : GL (Fin n) F} (e : bruhatCell h = bruhatCell g) : h ∈ cellGe g :=
  fun i j => (bruhatCell_eq_iff_llRank.1 e i j).ge

/- English proof (translation)
Introduce `i j` and use `(bruhatCell_eq_iff_llRank.1 e i j).le`.
-/
theorem mem_cellLe_of_eq {g h : GL (Fin n) F} (e : bruhatCell h = bruhatCell g) : h ∈ cellLe g :=
  fun i j => (bruhatCell_eq_iff_llRank.1 e i j).le

/- English proof (translation)
The claim follows from `bruhatCell_mul_mul (unipotent_le_borel k.1.2) (unipotent_le_borel ((Iwasawa.unipotent F n).inv_mem k.2.2)) x`.
-/
theorem bruhatCell_smul (k : NN F n) (x : GL (Fin n) F) : bruhatCell (k • x) = bruhatCell x :=
  bruhatCell_mul_mul (unipotent_le_borel k.1.2)
    (unipotent_le_borel ((Iwasawa.unipotent F n).inv_mem k.2.2)) x

/- English proof (translation)
The claim follows from `llRank_mul_mul (unipotent_le_borel k.1.2) (unipotent_le_borel ((Iwasawa.unipotent F n).inv_mem k.2.2)) i j x`.
-/
theorem llRank_smul (k : NN F n) (x : GL (Fin n) F) (i j : Fin n) :
    llRank i j (k • x) = llRank i j x :=
  llRank_mul_mul (unipotent_le_borel k.1.2)
    (unipotent_le_borel ((Iwasawa.unipotent F n).inv_mem k.2.2)) i j x

/- English proof (translation)
Introduce `i j` and use `by rw [llRank_smul]; exact hx i j`.
-/
theorem smul_mem_cellGe {g x : GL (Fin n) F} (k : NN F n) (hx : x ∈ cellGe g) : k • x ∈ cellGe g :=
  fun i j => by rw [llRank_smul]; exact hx i j

/- English proof (translation)
The claim follows from `cellMinor_mul_mul hx k.1.2 ((Iwasawa.unipotent F n).inv_mem k.2.2)`.
-/
theorem cellMinor_smul {x : GL (Fin n) F} {w : Equiv.Perm (Fin n)} (hx : bruhatCell x = w)
    (k : NN F n) : cellMinor w (k • x) = cellMinor w x :=
  cellMinor_mul_mul hx k.1.2 ((Iwasawa.unipotent F n).inv_mem k.2.2)

/- English proof (translation)
Use `set w := bruhatCell g with hw`. Establish `hxw : bruhatCell x = w` using `bruhatCell_eq_of_mem (hUge hxU) hxC`. Take `⟨t, a, ha, b, hb, hx⟩` from `exists_eq_mul_diag_perm_mul hxw`. Establish `hx0w : bruhatCell (Iwasawa.diagGL F n t * permGL F w) = w` using `bruhatCell_diag_perm t w`. Use `⟨t, Set.Subset.antisymm ?_ ?_⟩` and prove the remaining obligations.

Introduce and unpack `z ⟨hzU, hzC, hzp⟩`. Establish `hzw : bruhatCell z = w` using `bruhatCell_eq_of_mem (hUge hzU) hzC`. Establish `hp : cellMinor w (Iwasawa.diagGL F n t * permGL F w) = cellMinor w z`. Rewrite `hzp` using `[Set.mem_preimage, Set.mem_singleton_iff]`. Rewrite using `[hzp, hx, cellMinor_mul_mul hx0w ha hb]`.

Take `⟨a', ha', b', hb', hz⟩` from `exists_eq_mul_mul_of_cellMinor_eq hx0w hzw hp`. Use `⟨(⟨a', ha'⟩, ⟨b'⁻¹, (Iwasawa.unipotent F n).inv_mem hb'⟩), ?_⟩` and prove the remaining obligations. Use `show (_ : NN F n) • _ = z`. Rewrite using `[biAction_smul, hz]`. Simplify using the standard rewrite rules.

Introduce and unpack `_ ⟨k, rfl⟩`. Establish `hkw : bruhatCell (k • (Iwasawa.diagGL F n t * permGL F w)) = w`. Rewrite using `[bruhatCell_smul, hx0w]`. Use `⟨hcellU _ hkw, mem_cellLe_of_eq hkw, ?_⟩` and prove the remaining obligations. Rewrite using `[Set.mem_preimage, Set.mem_singleton_iff, cellMinor_smul hx0w, hx, cellMinor_mul_mul hx0w ha hb]`.
-/
theorem fiber_eq_orbit {g : GL (Fin n) F} {U : Set (GL (Fin n) F)} (hUge : U ⊆ cellGe g)
    (hcellU : ∀ h, bruhatCell h = bruhatCell g → h ∈ U) {x : GL (Fin n) F} (hxU : x ∈ U)
    (hxC : x ∈ cellLe g) :
    ∃ t : Fin n → Fˣ, U ∩ (cellLe g ∩ cellMinor (bruhatCell g) ⁻¹' {cellMinor (bruhatCell g) x}) =
      orbit (NN F n) (Iwasawa.diagGL F n t * permGL F (bruhatCell g)) := by
  set w := bruhatCell g with hw
  have hxw : bruhatCell x = w := bruhatCell_eq_of_mem (hUge hxU) hxC
  obtain ⟨t, a, ha, b, hb, hx⟩ := exists_eq_mul_diag_perm_mul hxw
  have hx0w : bruhatCell (Iwasawa.diagGL F n t * permGL F w) = w := bruhatCell_diag_perm t w
  refine ⟨t, Set.Subset.antisymm ?_ ?_⟩
  · rintro z ⟨hzU, hzC, hzp⟩
    have hzw : bruhatCell z = w := bruhatCell_eq_of_mem (hUge hzU) hzC
    have hp : cellMinor w (Iwasawa.diagGL F n t * permGL F w) = cellMinor w z := by
      rw [Set.mem_preimage, Set.mem_singleton_iff] at hzp
      rw [hzp, hx, cellMinor_mul_mul hx0w ha hb]
    obtain ⟨a', ha', b', hb', hz⟩ := exists_eq_mul_mul_of_cellMinor_eq hx0w hzw hp
    refine ⟨(⟨a', ha'⟩, ⟨b'⁻¹, (Iwasawa.unipotent F n).inv_mem hb'⟩), ?_⟩
    show (_ : NN F n) • _ = z
    rw [biAction_smul, hz]
    simp
  · rintro _ ⟨k, rfl⟩
    have hkw : bruhatCell (k • (Iwasawa.diagGL F n t * permGL F w)) = w := by
      rw [bruhatCell_smul, hx0w]
    refine ⟨hcellU _ hkw, mem_cellLe_of_eq hkw, ?_⟩
    rw [Set.mem_preimage, Set.mem_singleton_iff, cellMinor_smul hx0w, hx,
      cellMinor_mul_mul hx0w ha hb]

variable (ψ₀ : AddChar F ℂ)

def Irrelevant (w : Equiv.Perm (Fin n)) (t : Fin n → Fˣ) : Prop :=
  ∃ i j : Fin n, i < j ∧ w i < w j ∧ ∃ a : F,
    psiN ψ₀ (rootElt (w i) (w j) ((t (w i) : F) / (t (w j) : F) * a)) ≠ psiN ψ₀ (rootElt i j a)

/- English proof (translation)
Take `⟨K, -, hKo, hKψ⟩` from `exists_compactOpen_psiN_trivial F n hψ`. Use `⟨K.prod K, ?_, fun l hl => ?_⟩` and prove the remaining obligations. Rewrite using `[Subgroup.coe_prod]`. Conclude with `hKo.prod hKo`. Rewrite using `[chi_apply, hKψ _ hl.1, hKψ _ hl.2, inv_one, mul_one]`.
-/
theorem exists_open_chi_trivial (hψ : Continuous ψ₀) :
    ∃ L : Subgroup (NN F n), IsOpen (L : Set (NN F n)) ∧ ∀ l ∈ L, chi ψ₀ l = 1 := by
  obtain ⟨K, -, hKo, hKψ⟩ := exists_compactOpen_psiN_trivial F n hψ
  refine ⟨K.prod K, ?_, fun l hl => ?_⟩
  · rw [Subgroup.coe_prod]
    exact hKo.prod hKo
  · rw [chi_apply, hKψ _ hl.1, hKψ _ hl.2, inv_one, mul_one]

/- English proof (translation)
Take `⟨i, j, hij, hwij, a, ha⟩` from `hirr`. Use `set c : F := (t (w i) : F) / (t (w j) : F) with hc`. Set `φ : Multiplicative F →* NN F n` to `{ toFun := fun b => (⟨rootElt (w i) (w j) (c * b.toAdd), rootElt_mem_unipotent hwij _⟩, ⟨rootElt i j b.toAdd, rootElt_mem_unipotent hij _⟩) map_one' := by`. Apply the tactic sequence `refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_) <;> simp`. Use the proof step `map_mul' := fun b b' => by`.

Apply the tactic sequence `refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_) <;>`. Simplify using `[toAdd_mul, mul_add, rootElt_add] }`. Establish `hφ : Continuous fun b : F => φ (Multiplicative.ofAdd b)`. Use `Continuous.prodMk (Continuous.subtype_mk ?_ _) (Continuous.subtype_mk ?_ _)` and prove the remaining obligations. Conclude with `(continuous_rootElt (w i) (w j)).comp (continuous_const.mul continuous_id)`.

Conclude with `continuous_rootElt i j`. Use `set s : NN F n := φ (Multiplicative.ofAdd a)`. Set `K : Set (NN F n)` to `(fun b : F => φ (Multiplicative.ofAdd b)) '' {b : F | valuation F b ≤ valuation F a}`. Establish `hK : IsCompact K` using `(IsNonarchimedeanLocalField.isCompact_closedBall F _).image hφ`. Establish `hzp : ((Subgroup.zpowers s : Subgroup (NN F n)) : Set (NN F n)) ⊆ K`.

Introduce and unpack `_ ⟨m, rfl⟩`. Use `⟨m • a, ?_, ?_⟩` and prove the remaining obligations. Establish `hmem : m • a ∈ (valuation F).leAddSubgroup (valuation F a)` using `AddSubgroup.zsmul_mem _ (Valuation.mem_leAddSubgroup_iff.2 le_rfl) m`. Conclude with `Valuation.mem_leAddSubgroup_iff.1 hmem`. Use `show φ (Multiplicative.ofAdd (m • a)) = s ^ m`.

Rewrite using `[ofAdd_zsmul, map_zpow]`. Set `S₀ : Subgroup (NN F n)` to `(Subgroup.zpowers s).topologicalClosure`. Establish `hS₀ : IsCompact (S₀ : Set (NN F n))` using `hK.of_isClosed_subset isClosed_closure (closure_minimal hzp hK.isClosed)`. Establish `hs : s ∈ S₀` using `Subgroup.le_topologicalClosure _ (Subgroup.mem_zpowers s)`. Establish `hsx : s • (Iwasawa.diagGL F n t * permGL F w) = Iwasawa.diagGL F n t * permGL F w`.

Rewrite using `[biAction_smul]`. Use `show rootElt (w i) (w j) (c * a) * (Iwasawa.diagGL F n t * permGL F w) * (rootElt i j a)⁻¹ = _`. Rewrite using `[← conj_rootElt]`. Use `group`. Establish `hχs : chi ψ₀ s ≠ 1`.

Rewrite using `[chi_apply]`. Introduce `h`. Apply `ha` to reduce the goal to its premises. Establish `h0` using `psiN_ne_zero ψ₀ (rootElt i j a)`. Conclude with `(mul_inv_eq_one₀ h0).1 h`.

Conclude with `supportedIn_le_of_stabilizer hU hC hO hUinv (chi ψ₀) (exists_open_chi_trivial ψ₀ hψ) hS₀ hs hsx hχs`.
-/
theorem supportedIn_le_of_irrelevant (hψ : Continuous ψ₀) {U C : Set (GL (Fin n) F)}
    (hU : IsOpen U) (hC : IsClosed C) (hUinv : ∀ k : NN F n, ∀ x ∈ U, k • x ∈ U)
    {w : Equiv.Perm (Fin n)} {t : Fin n → Fˣ}
    (hO : U ∩ C = orbit (NN F n) (Iwasawa.diagGL F n t * permGL F w))
    (hirr : Irrelevant ψ₀ w t) :
    supportedIn U ≤ relSpan (chi (n := n) ψ₀) U ⊔ (supportedIn U ⊓ vanishingOn C) := by
  obtain ⟨i, j, hij, hwij, a, ha⟩ := hirr
  set c : F := (t (w i) : F) / (t (w j) : F) with hc
  let φ : Multiplicative F →* NN F n :=
    { toFun := fun b => (⟨rootElt (w i) (w j) (c * b.toAdd), rootElt_mem_unipotent hwij _⟩,
        ⟨rootElt i j b.toAdd, rootElt_mem_unipotent hij _⟩)
      map_one' := by
        refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_) <;> simp
      map_mul' := fun b b' => by
        refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_) <;>
          simp [toAdd_mul, mul_add, rootElt_add] }
  have hφ : Continuous fun b : F => φ (Multiplicative.ofAdd b) := by
    refine Continuous.prodMk (Continuous.subtype_mk ?_ _) (Continuous.subtype_mk ?_ _)
    · exact (continuous_rootElt (w i) (w j)).comp (continuous_const.mul continuous_id)
    · exact continuous_rootElt i j
  set s : NN F n := φ (Multiplicative.ofAdd a)

  let K : Set (NN F n) := (fun b : F => φ (Multiplicative.ofAdd b)) ''
    {b : F | valuation F b ≤ valuation F a}
  have hK : IsCompact K := (IsNonarchimedeanLocalField.isCompact_closedBall F _).image hφ
  have hzp : ((Subgroup.zpowers s : Subgroup (NN F n)) : Set (NN F n)) ⊆ K := by
    rintro _ ⟨m, rfl⟩
    refine ⟨m • a, ?_, ?_⟩
    · have hmem : m • a ∈ (valuation F).leAddSubgroup (valuation F a) :=
        AddSubgroup.zsmul_mem _ (Valuation.mem_leAddSubgroup_iff.2 le_rfl) m
      exact Valuation.mem_leAddSubgroup_iff.1 hmem
    · show φ (Multiplicative.ofAdd (m • a)) = s ^ m
      rw [ofAdd_zsmul, map_zpow]
  let S₀ : Subgroup (NN F n) := (Subgroup.zpowers s).topologicalClosure
  have hS₀ : IsCompact (S₀ : Set (NN F n)) :=
    hK.of_isClosed_subset isClosed_closure (closure_minimal hzp hK.isClosed)
  have hs : s ∈ S₀ := Subgroup.le_topologicalClosure _ (Subgroup.mem_zpowers s)
  have hsx : s • (Iwasawa.diagGL F n t * permGL F w) = Iwasawa.diagGL F n t * permGL F w := by
    rw [biAction_smul]
    show rootElt (w i) (w j) (c * a) * (Iwasawa.diagGL F n t * permGL F w) *
      (rootElt i j a)⁻¹ = _
    rw [← conj_rootElt]
    group
  have hχs : chi ψ₀ s ≠ 1 := by
    rw [chi_apply]
    intro h
    apply ha
    have h0 := psiN_ne_zero ψ₀ (rootElt i j a)
    exact (mul_inv_eq_one₀ h0).1 h
  exact supportedIn_le_of_stabilizer hU hC hO hUinv (chi ψ₀) (exists_open_chi_trivial ψ₀ hψ)
    hS₀ hs hsx hχs

/- English proof (translation)
Establish `key : ∀ i j : Fin n, i < j → w i < w j → ∀ a : F, psiN ψ₀ (rootElt (w i) (w j) ((t (w i) : F) / (t (w j) : F) * a)) = psiN ψ₀ (rootElt i j a)`. Introduce `i j hij hw a`. Assume the negation of the conclusion as `hne`. Conclude with `h ⟨i, j, hij, hw, a, hne⟩`. Choose the witnesses or unpack the hypotheses as in `⟨b, hb⟩ : ∃ b, ψ₀ b ≠ 1 := by`.

Assume the negation of the conclusion as `hall`. Simplify using `only [not_exists, not_not] at hall`. Conclude with `hψ₁ (DFunLike.ext ψ₀ 1 fun x => by rw [hall x, AddChar.one_apply])`. Establish `hψ0 : ∀ x, ψ₀ x ≠ 0` using `fun x hx => by`. Use `AddChar.map_add_eq_mul ψ₀ x (-x)` as an intermediate fact.

Rewrite `this` using `[add_neg_cancel, AddChar.map_zero_eq_one, hx, zero_mul]`. Conclude with `one_ne_zero this`. Establish `hB : ∀ i j : Fin n, i < j → (w j).val = (w i).val + 1 → j.val = i.val + 1`. Introduce `i j hij hwv`. Establish `hw : w i < w j` using `by rw [Fin.lt_def]; omega`.

Assume the negation of the conclusion as `hj`. Establish `hc : ((t (w i) : F) / (t (w j) : F)) ≠ 0` using `div_ne_zero (Units.ne_zero _) (Units.ne_zero _)`. Use `key i j hij hw (b / ((t (w i) : F) / (t (w j) : F)))` as an intermediate fact. Rewrite `this` using `[psiN_rootElt ψ₀ (w.injective.ne (ne_of_lt hij)), psiN_rootElt ψ₀ (ne_of_lt hij), if_pos hwv, if_neg hj, mul_div_cancel₀ _ hc]`. Conclude with `hb this`.

Establish `ht : ∀ (i : Fin n) (h : i.val + 1 < n), w i < w ⟨i.val + 1, h⟩ → t (w i) = t (w ⟨i.val + 1, h⟩)`. Introduce `i hi hw`. Use `set j : Fin n := ⟨i.val + 1, hi⟩ with hj`. Establish `hij : i < j` using `by rw [Fin.lt_def]; simp [j]`. Establish `hjv : j.val = i.val + 1` using `rfl`.

Establish `hwv : (w j).val = (w i).val + 1`. Assume the negation of the conclusion as `hne`. Use `key i j hij hw b` as an intermediate fact. Rewrite `this` using `[psiN_rootElt ψ₀ (w.injective.ne (ne_of_lt hij)), psiN_rootElt ψ₀ (ne_of_lt hij), if_neg hne, if_pos hjv]`. Conclude with `hb this.symm`.

Use `set c : F := (t (w i) : F) / (t (w j) : F) with hc`. Establish `hc1 : c = 1`. Assume the negation of the conclusion as `hc1`. Establish `hsub : c - 1 ≠ 0` using `sub_ne_zero.2 hc1`. Use `key i j hij hw (b / (c - 1))` as an intermediate fact.

Rewrite `this` using `[psiN_rootElt ψ₀ (w.injective.ne (ne_of_lt hij)), psiN_rootElt ψ₀ (ne_of_lt hij), if_pos hwv, if_pos hjv]`. Apply `hb` to reduce the goal to its premises. Establish `e : b = c * (b / (c - 1)) - b / (c - 1)` using `by field_simp`. Rewrite using `[e, AddChar.map_sub_eq_div, this, div_self (hψ0 _)]`. Conclude with `Units.ext ((div_eq_one_iff_eq (Units.ne_zero _)).1 hc1)`.

Conclude with `sigma_diag_mul_permGL_eq t w (relevant_involution hB) (relevant_torus t hB ht)`.
-/
theorem sigma_eq_of_not_irrelevant (hψ₁ : ψ₀ ≠ 1) {w : Equiv.Perm (Fin n)} {t : Fin n → Fˣ}
    (h : ¬ Irrelevant ψ₀ w t) :
    sigma (Iwasawa.diagGL F n t * permGL F w) = Iwasawa.diagGL F n t * permGL F w := by
  have key : ∀ i j : Fin n, i < j → w i < w j → ∀ a : F,
      psiN ψ₀ (rootElt (w i) (w j) ((t (w i) : F) / (t (w j) : F) * a)) =
        psiN ψ₀ (rootElt i j a) := by
    intro i j hij hw a
    by_contra hne
    exact h ⟨i, j, hij, hw, a, hne⟩
  obtain ⟨b, hb⟩ : ∃ b, ψ₀ b ≠ 1 := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    exact hψ₁ (DFunLike.ext ψ₀ 1 fun x => by rw [hall x, AddChar.one_apply])
  have hψ0 : ∀ x, ψ₀ x ≠ 0 := fun x hx => by
    have := AddChar.map_add_eq_mul ψ₀ x (-x)
    rw [add_neg_cancel, AddChar.map_zero_eq_one, hx, zero_mul] at this
    exact one_ne_zero this
  have hB : ∀ i j : Fin n, i < j → (w j).val = (w i).val + 1 → j.val = i.val + 1 := by
    intro i j hij hwv
    have hw : w i < w j := by rw [Fin.lt_def]; omega
    by_contra hj
    have hc : ((t (w i) : F) / (t (w j) : F)) ≠ 0 := div_ne_zero (Units.ne_zero _) (Units.ne_zero _)
    have := key i j hij hw (b / ((t (w i) : F) / (t (w j) : F)))
    rw [psiN_rootElt ψ₀ (w.injective.ne (ne_of_lt hij)), psiN_rootElt ψ₀ (ne_of_lt hij),
      if_pos hwv, if_neg hj, mul_div_cancel₀ _ hc] at this
    exact hb this
  have ht : ∀ (i : Fin n) (h : i.val + 1 < n), w i < w ⟨i.val + 1, h⟩ →
      t (w i) = t (w ⟨i.val + 1, h⟩) := by
    intro i hi hw
    set j : Fin n := ⟨i.val + 1, hi⟩ with hj
    have hij : i < j := by rw [Fin.lt_def]; simp [j]
    have hjv : j.val = i.val + 1 := rfl
    have hwv : (w j).val = (w i).val + 1 := by
      by_contra hne
      have := key i j hij hw b
      rw [psiN_rootElt ψ₀ (w.injective.ne (ne_of_lt hij)), psiN_rootElt ψ₀ (ne_of_lt hij),
        if_neg hne, if_pos hjv] at this
      exact hb this.symm
    set c : F := (t (w i) : F) / (t (w j) : F) with hc
    have hc1 : c = 1 := by
      by_contra hc1
      have hsub : c - 1 ≠ 0 := sub_ne_zero.2 hc1
      have := key i j hij hw (b / (c - 1))
      rw [psiN_rootElt ψ₀ (w.injective.ne (ne_of_lt hij)), psiN_rootElt ψ₀ (ne_of_lt hij),
        if_pos hwv, if_pos hjv] at this
      apply hb
      have e : b = c * (b / (c - 1)) - b / (c - 1) := by field_simp
      rw [e, AddChar.map_sub_eq_div, this, div_self (hψ0 _)]
    exact Units.ext ((div_eq_one_iff_eq (Units.ne_zero _)).1 hc1)
  exact sigma_diag_mul_permGL_eq t w (relevant_involution hB) (relevant_torus t hB ht)

/- English proof (translation)
Use `set w := bruhatCell g`. Use `set A : Set (GL (Fin n) F) := cellMinor w ⁻¹' V`. Establish `hA : IsClopen A` using `hV.preimage (continuous_cellMinor w)`. Use `set φ : GL (Fin n) F → ℂ := A.indicator 1`. Use `set W := relSpan (chi (n := n) ψ₀) U ⊔ (supportedIn U ⊓ vanishingOn (cellLe g))`.

Establish `hmul : ∀ f, (fun x => φ x * f x) = LinearMap.mulLeft ℂ φ f` using `fun f => rfl`. It suffices to establish `h : W ≤ W.comap (LinearMap.mulLeft ℂ φ) by`. Rewrite using `[hmul]`. Conclude with `h hr`. Use `sup_le ?_ ?_` and prove the remaining obligations.

Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨k, f, hf, rfl⟩`. Rewrite using `[SetLike.mem_coe, Submodule.mem_comap, map_sub, map_smul]`. Establish `hφf : (fun x => φ x * f x) ∈ supportedIn U` using `indicator_mul_mem hA hf`. Establish `e : LinearMap.mulLeft ℂ φ (transl k f) - chi ψ₀ k • LinearMap.mulLeft ℂ φ f = (transl k (fun x => φ x * f x) - chi ψ₀ k • (fun x => φ x * f x)) + (LinearMap.mulLeft ℂ φ (transl k f) - transl k (fun x => φ x * f x))`.

Rewrite using `[← hmul]`. Normalize the expressions using the abelian group laws. Rewrite using `[e]`. Use `add_mem (le_sup_left (b := supportedIn U ⊓ vanishingOn (cellLe g)) (sub_mem_relSpan _ k hφf)) (le_sup_right (a := relSpan (chi (n := n) ψ₀) U) ⟨?_, ?_⟩)` and prove the remaining obligations. Conclude with `sub_mem (indicator_mul_mem hA (transl_mem_supportedIn hUinv k hf)) (transl_mem_supportedIn hUinv k hφf)`.

Introduce `x hxC show φ x * transl k f x - transl k (fun x => φ x * f x) x = 0`. Simplify using `only [transl_apply]`. Distinguish the cases in `hxU : x ∈ U`. Establish `hxw : bruhatCell x = w` using `bruhatCell_eq_of_mem (hUge hxU) hxC`. Establish `hp : cellMinor w (k⁻¹ • x) = cellMinor w x` using `cellMinor_smul hxw k⁻¹`.

Establish `hAx : (k⁻¹ • x ∈ A) ↔ (x ∈ A)` using `by show cellMinor w (k⁻¹ • x) ∈ V ↔ cellMinor w x ∈ V`. Rewrite using `[hp]`. Establish `: φ (k⁻¹ • x) = φ x` using `by show A.indicator 1 (k⁻¹ • x) = A.indicator 1 x`. Distinguish the cases in `hxA : x ∈ A`. Rewrite using `[Set.indicator_of_mem (hAx.2 hxA), Set.indicator_of_mem hxA]`.

Both sides reduce to the same expression. Rewrite using `[Set.indicator_of_notMem (fun h => hxA (hAx.1 h)), Set.indicator_of_notMem hxA]`. Rewrite using `[this, sub_self]`. Establish `hk : k⁻¹ • x ∉ U` using `fun h => hxU (by simpa using hUinv k _ h)`. Establish `h0 : f (k⁻¹ • x) = 0` using `Function.notMem_support.1 fun h => hk (hf.2 h)`.

Simplify using `[h0]`. Introduce and unpack `k ⟨hkU, hkC⟩`. Use `le_sup_right (a := relSpan (chi (n := n) ψ₀) U) ⟨indicator_mul_mem hA hkU, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Use `show φ x * k x = 0`.

Rewrite using `[hkC x hx, mul_zero]`.
-/
theorem mul_mem_cellSpace {g : GL (Fin n) F} {U : Set (GL (Fin n) F)}
    (hUinv : ∀ k : NN F n, ∀ x ∈ U, k • x ∈ U) (hUge : U ⊆ cellGe g)
    {V : Set (Fin n → F)} (hV : IsClopen V) {r : GL (Fin n) F → ℂ}
    (hr : r ∈ relSpan (chi (n := n) ψ₀) U ⊔ (supportedIn U ⊓ vanishingOn (cellLe g))) :
    (fun x => (cellMinor (bruhatCell g) ⁻¹' V).indicator 1 x * r x) ∈
      relSpan (chi (n := n) ψ₀) U ⊔ (supportedIn U ⊓ vanishingOn (cellLe g)) := by
  set w := bruhatCell g
  set A : Set (GL (Fin n) F) := cellMinor w ⁻¹' V
  have hA : IsClopen A := hV.preimage (continuous_cellMinor w)
  set φ : GL (Fin n) F → ℂ := A.indicator 1
  set W := relSpan (chi (n := n) ψ₀) U ⊔ (supportedIn U ⊓ vanishingOn (cellLe g))
  have hmul : ∀ f, (fun x => φ x * f x) = LinearMap.mulLeft ℂ φ f := fun f => rfl
  suffices h : W ≤ W.comap (LinearMap.mulLeft ℂ φ) by
    rw [hmul]
    exact h hr
  refine sup_le ?_ ?_
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨k, f, hf, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, map_sub, map_smul]
    have hφf : (fun x => φ x * f x) ∈ supportedIn U := indicator_mul_mem hA hf
    have e : LinearMap.mulLeft ℂ φ (transl k f) - chi ψ₀ k • LinearMap.mulLeft ℂ φ f =
        (transl k (fun x => φ x * f x) - chi ψ₀ k • (fun x => φ x * f x)) +
          (LinearMap.mulLeft ℂ φ (transl k f) - transl k (fun x => φ x * f x)) := by
      rw [← hmul]
      abel
    rw [e]
    refine add_mem (le_sup_left (b := supportedIn U ⊓ vanishingOn (cellLe g))
      (sub_mem_relSpan _ k hφf)) (le_sup_right (a := relSpan (chi (n := n) ψ₀) U) ⟨?_, ?_⟩)
    · exact sub_mem (indicator_mul_mem hA (transl_mem_supportedIn hUinv k hf))
        (transl_mem_supportedIn hUinv k hφf)
    · intro x hxC
      show φ x * transl k f x - transl k (fun x => φ x * f x) x = 0
      simp only [transl_apply]
      by_cases hxU : x ∈ U
      · have hxw : bruhatCell x = w := bruhatCell_eq_of_mem (hUge hxU) hxC
        have hp : cellMinor w (k⁻¹ • x) = cellMinor w x := cellMinor_smul hxw k⁻¹
        have hAx : (k⁻¹ • x ∈ A) ↔ (x ∈ A) := by
          show cellMinor w (k⁻¹ • x) ∈ V ↔ cellMinor w x ∈ V
          rw [hp]
        have : φ (k⁻¹ • x) = φ x := by
          show A.indicator 1 (k⁻¹ • x) = A.indicator 1 x
          by_cases hxA : x ∈ A
          · rw [Set.indicator_of_mem (hAx.2 hxA), Set.indicator_of_mem hxA]
            rfl
          · rw [Set.indicator_of_notMem (fun h => hxA (hAx.1 h)), Set.indicator_of_notMem hxA]
        rw [this, sub_self]
      · have hk : k⁻¹ • x ∉ U := fun h => hxU (by simpa using hUinv k _ h)
        have h0 : f (k⁻¹ • x) = 0 := Function.notMem_support.1 fun h => hk (hf.2 h)
        simp [h0]
  · rintro k ⟨hkU, hkC⟩
    refine le_sup_right (a := relSpan (chi (n := n) ψ₀) U) ⟨indicator_mul_mem hA hkU, ?_⟩
    intro x hx
    show φ x * k x = 0
    rw [hkC x hx, mul_zero]

/- English proof (translation)
Introduce `f hf`. Use `mem_of_forall_fiber (isClosed_cellLe g) (continuous_cellMinor (bruhatCell g)) le_sup_right (fun V hV r hr => mul_mem_cellSpace ψ₀ hUinv hUge hV hr) hf fun y => ?_` and prove the remaining obligations. Distinguish the cases in `hy : ∃ x ∈ U, x ∈ cellLe g ∧ cellMinor (bruhatCell g) x = y`. Take `⟨x, hxU, hxC, rfl⟩` from `hy`. Take `⟨t, ht⟩` from `fiber_eq_orbit hUge hcellU hxU hxC`.

Establish `hC : IsClosed (cellLe g ∩ cellMinor (bruhatCell g) ⁻¹' {cellMinor (bruhatCell g) x})` using `(isClosed_cellLe g).inter (isClosed_singleton.preimage (continuous_cellMinor _))`. Take `⟨a, ha, b, hb, hab⟩` from `Submodule.mem_sup.1 (supportedIn_le_of_irrelevant ψ₀ hψ hU hC hUinv ht (hirr t) hf)`. Rewrite using `[← hab]`. Conclude with `add_mem (Submodule.mem_sup_left (Submodule.mem_sup_left ha)) (Submodule.mem_sup_right hb)`. Use `le_sup_right (a := relSpan (chi (n := n) ψ₀) U ⊔ (supportedIn U ⊓ vanishingOn (cellLe g))) ⟨hf, fun x hx => ?_⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hfx`. Conclude with `hy ⟨x, hf.2 hfx, hx.1, hx.2⟩`.
-/
theorem cell_irrelevant (hψ : Continuous ψ₀) {g : GL (Fin n) F} {U : Set (GL (Fin n) F)}
    (hU : IsOpen U) (hUinv : ∀ k : NN F n, ∀ x ∈ U, k • x ∈ U) (hUge : U ⊆ cellGe g)
    (hcellU : ∀ h, bruhatCell h = bruhatCell g → h ∈ U)
    (hirr : ∀ t, Irrelevant ψ₀ (bruhatCell g) t) :
    supportedIn U ≤ relSpan (chi (n := n) ψ₀) U ⊔ (supportedIn U ⊓ vanishingOn (cellLe g)) := by
  intro f hf
  refine mem_of_forall_fiber (isClosed_cellLe g) (continuous_cellMinor (bruhatCell g))
    le_sup_right (fun V hV r hr => mul_mem_cellSpace ψ₀ hUinv hUge hV hr) hf fun y => ?_
  by_cases hy : ∃ x ∈ U, x ∈ cellLe g ∧ cellMinor (bruhatCell g) x = y
  · obtain ⟨x, hxU, hxC, rfl⟩ := hy
    obtain ⟨t, ht⟩ := fiber_eq_orbit hUge hcellU hxU hxC
    have hC : IsClosed (cellLe g ∩ cellMinor (bruhatCell g) ⁻¹' {cellMinor (bruhatCell g) x}) :=
      (isClosed_cellLe g).inter (isClosed_singleton.preimage (continuous_cellMinor _))
    obtain ⟨a, ha, b, hb, hab⟩ :=
      Submodule.mem_sup.1 (supportedIn_le_of_irrelevant ψ₀ hψ hU hC hUinv ht (hirr t) hf)
    rw [← hab]
    exact add_mem (Submodule.mem_sup_left (Submodule.mem_sup_left ha)) (Submodule.mem_sup_right hb)
  · refine le_sup_right (a := relSpan (chi (n := n) ψ₀) U ⊔ (supportedIn U ⊓ vanishingOn (cellLe g)))
      ⟨hf, fun x hx => ?_⟩
    by_contra hfx
    exact hy ⟨x, hf.2 hfx, hx.1, hx.2⟩

/- English proof (translation)
Take `⟨⟨k, hk, hk1⟩, hl2⟩` from `hl`. Use `⟨⟨l.2, hl2, rfl⟩, ?_⟩` and prove the remaining obligations. Use `show thetaN l.1 ∈ K`. Rewrite using `[← hk1]`. Establish `: thetaN (thetaN k) = k`.

Rewrite using `[← thetaN_symm]`. Conclude with `MulEquiv.symm_apply_apply _ k`. Simplify `hk` using `[this]`.
-/
theorem swapTheta_mem_prod {K : Subgroup (Iwasawa.unipotent F n)} {l : NN F n}
    (hl : l ∈ (K.map (thetaN : Iwasawa.unipotent F n ≃* Iwasawa.unipotent F n).toMonoidHom).prod K) :
    swapTheta l ∈ (K.map (thetaN : Iwasawa.unipotent F n ≃* Iwasawa.unipotent F n).toMonoidHom).prod K := by
  obtain ⟨⟨k, hk, hk1⟩, hl2⟩ := hl
  refine ⟨⟨l.2, hl2, rfl⟩, ?_⟩
  show thetaN l.1 ∈ K
  rw [← hk1]
  have : thetaN (thetaN k) = k := by
    rw [← thetaN_symm]
    exact MulEquiv.symm_apply_apply _ k
  simpa [this] using hk

/- English proof (translation)
Use `set w := bruhatCell g with hw`. Use `set W := relSpan (chi (n := n) ψ₀) U ⊔ (supportedIn U ⊓ vanishingOn (cellLe g)) with hWdef`. Establish `hσU : sigma ⁻¹' U = U` using `Set.ext fun x => hUσ x`. Establish `hsU : ∀ {k : GL (Fin n) F → ℂ}, k ∈ supportedIn U → sigmaL k ∈ supportedIn U` using `fun hk => by`. Use `sigmaL_mem_supportedIn hk` as an intermediate fact.

Rewrite `this` using `[hσU]`. Then use the resulting hypothesis. Establish `hWσ : ∀ r ∈ W, sigmaL r ∈ W`. Introduce `r hr`. Take `⟨r₁, hr₁, r₂, hr₂, rfl⟩` from `Submodule.mem_sup.1 hr`. Rewrite using `[map_add]`.

Use `add_mem (le_sup_left (b := supportedIn U ⊓ vanishingOn (cellLe g)) ?_) (le_sup_right (a := relSpan (chi (n := n) ψ₀) U) ⟨hsU hr₂.1, fun x hx => ?_⟩)` and prove the remaining obligations. Use `sigmaL_mem_relSpan ψ₀ hr₁` as an intermediate fact. Rewrite `this` using `[hσU]`. Then use the resulting hypothesis. Use `show r₂ (sigma x) = 0`. Distinguish the cases in `hxU : x ∈ U`.

Establish `hxw : bruhatCell x = w` using `bruhatCell_eq_of_mem (hUge hxU) hx`. Conclude with `hr₂.2 _ (mem_cellLe_of_eq (hσcell x hxw))`. Conclude with `Function.notMem_support.1 fun h => hxU ((hUσ x).1 (hr₂.1.2 h))`. Establish `hg : f - sigmaL f ∈ supportedIn U` using `sub_mem hf (hsU hf)`. Use `mem_of_forall_fiber (isClosed_cellLe g) (continuous_cellMinor w) le_sup_right (fun V hV r hr => mul_mem_cellSpace ψ₀ hUinv hUge hV hr) hg fun y => ?_` and prove the remaining obligations.

Distinguish the cases in `hy : ∃ x ∈ U, x ∈ cellLe g ∧ cellMinor w x = y`. Use `swap`. Use `le_sup_right (a := W) ⟨hg, fun x hx => ?_⟩` and prove the remaining obligations. Establish `hxU : x ∉ U` using `fun hxU => hy ⟨x, hxU, hx.1, hx.2⟩`. Establish `h1 : f x = 0` using `Function.notMem_support.1 fun h => hxU (hf.2 h)`.

Establish `h2 : f (sigma x) = 0` using `Function.notMem_support.1 fun h => hxU ((hUσ x).1 (hf.2 h))`. Use `show f x - f (sigma x) = 0`. Rewrite using `[h1, h2, sub_zero]`. Take `⟨x, hxU, hxC, rfl⟩` from `hy`. Take `⟨t, hO⟩` from `fiber_eq_orbit hUge hcellU hxU hxC`.

Use `set C : Set (GL (Fin n) F) := cellLe g ∩ cellMinor w ⁻¹' {cellMinor w x} with hCdef`. Establish `hC : IsClosed C` using `(isClosed_cellLe g).inter (isClosed_singleton.preimage (continuous_cellMinor _))`. Use `set x₀ := Iwasawa.diagGL F n t * permGL F w with hx₀`. Distinguish the cases in `hirr : Irrelevant ψ₀ w t`. Establish `h1` using `supportedIn_le_of_irrelevant ψ₀ hψ hU hC hUinv hO hirr`.

Establish `mono : relSpan (chi (n` using `n) ψ₀) U ⊔ (supportedIn U ⊓ vanishingOn C) ≤ W ⊔ (supportedIn U ⊓ vanishingOn C) := sup_le_sup_right le_sup_left _`. Conclude with `sub_mem (mono (h1 hf)) (mono (h1 (hsU hf)))`. Establish `hfix : sigma x₀ = x₀` using `sigma_eq_of_not_irrelevant ψ₀ hψ₁ hirr`. Establish `hσO : ∀ z ∈ orbit (NN F n) x₀, sigma z ∈ orbit (NN F n) x₀`. Introduce and unpack `_ ⟨k, rfl⟩`.

Conclude with `⟨swapTheta k, by rw [sigma_smul, hfix]⟩`. Establish `hOC : ∀ z ∈ orbit (NN F n) x₀, z ∈ U ∧ z ∈ C` using `fun z hz => by`. Rewrite `hz` using `[← hO]`. Conclude with `hz`. Take `⟨K, hKc, hKo, hKψ⟩` from `exists_compactOpen_psiN_trivial F n hψ`.

Use `set L₀ : Subgroup (NN F n) := (K.map (thetaN : Iwasawa.unipotent F n ≃* Iwasawa.unipotent F n).toMonoidHom).prod K`. Establish `hθimg : ((K.map (thetaN : Iwasawa.unipotent F n ≃* Iwasawa.unipotent F n).toMonoidHom : Subgroup (Iwasawa.unipotent F n)) : Set (Iwasawa.unipotent F n)) = thetaN ⁻¹' (K : Set (Iwasawa.unipotent F n))`. Use extensionality with `u`. Simplify using `only [Subgroup.coe_map, MulEquiv.coe_toMonoidHom, Set.mem_image, SetLike.mem_coe, Set.mem_preimage]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨k, hk, rfl⟩`. Establish `: thetaN (thetaN k) = k`. Rewrite using `[← thetaN_symm]`. Conclude with `MulEquiv.symm_apply_apply _ k`. Rewrite using `[this]` and apply the resulting hypothesis.

Introduce `hu`. Use `⟨thetaN u, hu, ?_⟩` and prove the remaining obligations. Rewrite using `[← thetaN_symm]`. Conclude with `MulEquiv.symm_apply_apply _ u`. Establish `hL₀c : IsCompact (L₀ : Set (NN F n))`.

Rewrite using `[Subgroup.coe_prod]`. Use `IsCompact.prod ?_ hKc` and prove the remaining obligations. Rewrite using `[Subgroup.coe_map]`. Conclude with `hKc.image continuous_thetaN`. Establish `hL₀o : IsOpen (L₀ : Set (NN F n))`.

Rewrite using `[Subgroup.coe_prod, hθimg]`. Conclude with `(hKo.preimage continuous_thetaN).prod hKo`. Establish `hχL₀ : ∀ l ∈ L₀, chi ψ₀ l = 1`. Introduce and unpack `l ⟨⟨k, hk, hk1⟩, hl2⟩`. Rewrite using `[chi_apply, ← hk1, hKψ _ hl2]`.

Simplify using `only [MulEquiv.coe_toMonoidHom, coe_thetaN]`. Rewrite using `[psiN_theta ψ₀ k.2, hKψ _ hk]`. Simplify using the standard rewrite rules. Establish `hpiece : ∀ z, z ∈ orbitPiece L₀ x₀ → sigma z ∈ orbitPiece L₀ x₀`. Introduce and unpack `_ ⟨l, hl, rfl⟩`.

Conclude with `⟨swapTheta l, swapTheta_mem_prod hl, by rw [sigma_smul, hfix]⟩`. Take `⟨f₀, hf₀, hf₀O⟩` from `exists_lift_orbit_piece hU hC hO hL₀c hL₀o (mem_orbit_self x₀)`. Use `set W' := W ⊔ Submodule.span ℂ {f₀}`. Establish `hW'U : W' ≤ supportedIn U` using `sup_le (sup_le (relSpan_le_supportedIn _ hUinv) inf_le_left) (Submodule.span_le.2 (Set.singleton_subset_iff.2 hf₀))`. Establish `hmem` using `supportedIn_le_of_base hU hC hO hUinv (chi ψ₀) hW'U (le_sup_left.trans le_sup_left) L₀ hL₀c hL₀o hχL₀ f₀ hf₀O (le_sup_left (b := supportedIn U ⊓ vanishingOn C) (le_sup_right (a := W) (Submodule.mem_span_singleton_self f₀))) hf`.

Take `⟨p, hp, k, hk, hpk⟩` from `Submodule.mem_sup.1 hmem`. Take `⟨r, hr, q, hq, hrq⟩` from `Submodule.mem_sup.1 hp`. Take `⟨c, rfl⟩` from `Submodule.mem_span_singleton.1 hq`. Establish `hvan : ∀ {m : GL (Fin n) F → ℂ}, m ∈ supportedIn U → (∀ z ∈ orbit (NN F n) x₀, m z = m (sigma z)) → m - sigmaL m ∈ supportedIn U ⊓ vanishingOn C`. Introduce `m hm heq`.

Use `⟨sub_mem hm (hsU hm), fun z hz => ?_⟩` and prove the remaining obligations. Use `show m z - m (sigma z) = 0`. Distinguish the cases in `hzU : z ∈ U`. Establish `hzO : z ∈ orbit (NN F n) x₀` using `by rw [← hO]; exact ⟨hzU, hz⟩`. Rewrite using `[heq z hzO, sub_self]`.

Establish `h1 : m z = 0` using `Function.notMem_support.1 fun h => hzU (hm.2 h)`. Establish `h2 : m (sigma z) = 0` using `Function.notMem_support.1 fun h => hzU ((hUσ z).1 (hm.2 h))`. Rewrite using `[h1, h2, sub_zero]`. Establish `hf₀σ : f₀ - sigmaL f₀ ∈ supportedIn U ⊓ vanishingOn C`. Use `hvan hf₀ fun z hz => ?_` and prove the remaining obligations.

Rewrite using `[hf₀O z hz, hf₀O _ (hσO z hz)]`. Distinguish the cases in `hzp : z ∈ orbitPiece L₀ x₀`. Rewrite using `[Set.indicator_of_mem hzp, Set.indicator_of_mem (hpiece z hzp)]`. Both sides reduce to the same expression. Establish `: sigma z ∉ orbitPiece L₀ x₀` using `fun h => hzp (by simpa [sigma_sigma] using hpiece _ h)`.

Rewrite using `[Set.indicator_of_notMem hzp, Set.indicator_of_notMem this]`. Establish `hkσ : k - sigmaL k ∈ supportedIn U ⊓ vanishingOn C`. Use `hvan hk.1 fun z hz => ?_` and prove the remaining obligations. Rewrite using `[hk.2 z (hOC z hz).2, hk.2 _ (hOC _ (hσO z hz)).2]`. Establish `e : f - sigmaL f = (r - sigmaL r) + c • (f₀ - sigmaL f₀) + (k - sigmaL k)`.

Rewrite using `[← hpk, ← hrq, map_add, map_add, map_smul, smul_sub]`. Normalize the expressions using the abelian group laws. Rewrite using `[e]`. Use `add_mem (add_mem (le_sup_left (b := supportedIn U ⊓ vanishingOn C) (sub_mem hr (hWσ r hr))) (Submodule.smul_mem _ _ (le_sup_right (a := W) hf₀σ))) (le_sup_right (a := W) hkσ)` and prove the remaining obligations.
-/
theorem cell_relevant (hψ : Continuous ψ₀) (hψ₁ : ψ₀ ≠ 1) {g : GL (Fin n) F}
    {U : Set (GL (Fin n) F)} (hU : IsOpen U) (hUinv : ∀ k : NN F n, ∀ x ∈ U, k • x ∈ U)
    (hUge : U ⊆ cellGe g) (hcellU : ∀ h, bruhatCell h = bruhatCell g → h ∈ U)
    (hUσ : ∀ x, sigma x ∈ U ↔ x ∈ U)
    (hσcell : ∀ h : GL (Fin n) F, bruhatCell h = bruhatCell g → bruhatCell (sigma h) = bruhatCell g)
    {f : GL (Fin n) F → ℂ} (hf : f ∈ supportedIn U) :
    f - sigmaL f ∈ relSpan (chi (n := n) ψ₀) U ⊔ (supportedIn U ⊓ vanishingOn (cellLe g)) := by
  set w := bruhatCell g with hw
  set W := relSpan (chi (n := n) ψ₀) U ⊔ (supportedIn U ⊓ vanishingOn (cellLe g)) with hWdef
  have hσU : sigma ⁻¹' U = U := Set.ext fun x => hUσ x
  have hsU : ∀ {k : GL (Fin n) F → ℂ}, k ∈ supportedIn U → sigmaL k ∈ supportedIn U := fun hk => by
    have := sigmaL_mem_supportedIn hk
    rwa [hσU] at this
  have hWσ : ∀ r ∈ W, sigmaL r ∈ W := by
    intro r hr
    obtain ⟨r₁, hr₁, r₂, hr₂, rfl⟩ := Submodule.mem_sup.1 hr
    rw [map_add]
    refine add_mem (le_sup_left (b := supportedIn U ⊓ vanishingOn (cellLe g)) ?_)
      (le_sup_right (a := relSpan (chi (n := n) ψ₀) U) ⟨hsU hr₂.1, fun x hx => ?_⟩)
    · have := sigmaL_mem_relSpan ψ₀ hr₁
      rwa [hσU] at this
    · show r₂ (sigma x) = 0
      by_cases hxU : x ∈ U
      · have hxw : bruhatCell x = w := bruhatCell_eq_of_mem (hUge hxU) hx
        exact hr₂.2 _ (mem_cellLe_of_eq (hσcell x hxw))
      · exact Function.notMem_support.1 fun h => hxU ((hUσ x).1 (hr₂.1.2 h))
  have hg : f - sigmaL f ∈ supportedIn U := sub_mem hf (hsU hf)
  refine mem_of_forall_fiber (isClosed_cellLe g) (continuous_cellMinor w)
    le_sup_right (fun V hV r hr => mul_mem_cellSpace ψ₀ hUinv hUge hV hr) hg fun y => ?_
  by_cases hy : ∃ x ∈ U, x ∈ cellLe g ∧ cellMinor w x = y
  swap
  · refine le_sup_right (a := W) ⟨hg, fun x hx => ?_⟩
    have hxU : x ∉ U := fun hxU => hy ⟨x, hxU, hx.1, hx.2⟩
    have h1 : f x = 0 := Function.notMem_support.1 fun h => hxU (hf.2 h)
    have h2 : f (sigma x) = 0 :=
      Function.notMem_support.1 fun h => hxU ((hUσ x).1 (hf.2 h))
    show f x - f (sigma x) = 0
    rw [h1, h2, sub_zero]
  obtain ⟨x, hxU, hxC, rfl⟩ := hy
  obtain ⟨t, hO⟩ := fiber_eq_orbit hUge hcellU hxU hxC
  set C : Set (GL (Fin n) F) := cellLe g ∩ cellMinor w ⁻¹' {cellMinor w x} with hCdef
  have hC : IsClosed C := (isClosed_cellLe g).inter (isClosed_singleton.preimage
    (continuous_cellMinor _))
  set x₀ := Iwasawa.diagGL F n t * permGL F w with hx₀
  by_cases hirr : Irrelevant ψ₀ w t
  · have h1 := supportedIn_le_of_irrelevant ψ₀ hψ hU hC hUinv hO hirr
    have mono : relSpan (chi (n := n) ψ₀) U ⊔ (supportedIn U ⊓ vanishingOn C) ≤
        W ⊔ (supportedIn U ⊓ vanishingOn C) := sup_le_sup_right le_sup_left _
    exact sub_mem (mono (h1 hf)) (mono (h1 (hsU hf)))

  have hfix : sigma x₀ = x₀ := sigma_eq_of_not_irrelevant ψ₀ hψ₁ hirr
  have hσO : ∀ z ∈ orbit (NN F n) x₀, sigma z ∈ orbit (NN F n) x₀ := by
    rintro _ ⟨k, rfl⟩
    exact ⟨swapTheta k, by rw [sigma_smul, hfix]⟩
  have hOC : ∀ z ∈ orbit (NN F n) x₀, z ∈ U ∧ z ∈ C := fun z hz => by
    rw [← hO] at hz
    exact hz
  obtain ⟨K, hKc, hKo, hKψ⟩ := exists_compactOpen_psiN_trivial F n hψ
  set L₀ : Subgroup (NN F n) :=
    (K.map (thetaN : Iwasawa.unipotent F n ≃* Iwasawa.unipotent F n).toMonoidHom).prod K
  have hθimg : ((K.map (thetaN : Iwasawa.unipotent F n ≃* Iwasawa.unipotent F n).toMonoidHom :
      Subgroup (Iwasawa.unipotent F n)) : Set (Iwasawa.unipotent F n)) =
      thetaN ⁻¹' (K : Set (Iwasawa.unipotent F n)) := by
    ext u
    simp only [Subgroup.coe_map, MulEquiv.coe_toMonoidHom, Set.mem_image, SetLike.mem_coe,
      Set.mem_preimage]
    constructor
    · rintro ⟨k, hk, rfl⟩
      have : thetaN (thetaN k) = k := by
        rw [← thetaN_symm]
        exact MulEquiv.symm_apply_apply _ k
      rwa [this]
    · intro hu
      refine ⟨thetaN u, hu, ?_⟩
      rw [← thetaN_symm]
      exact MulEquiv.symm_apply_apply _ u
  have hL₀c : IsCompact (L₀ : Set (NN F n)) := by
    rw [Subgroup.coe_prod]
    refine IsCompact.prod ?_ hKc
    rw [Subgroup.coe_map]
    exact hKc.image continuous_thetaN
  have hL₀o : IsOpen (L₀ : Set (NN F n)) := by
    rw [Subgroup.coe_prod, hθimg]
    exact (hKo.preimage continuous_thetaN).prod hKo
  have hχL₀ : ∀ l ∈ L₀, chi ψ₀ l = 1 := by
    rintro l ⟨⟨k, hk, hk1⟩, hl2⟩
    rw [chi_apply, ← hk1, hKψ _ hl2]
    simp only [MulEquiv.coe_toMonoidHom, coe_thetaN]
    rw [psiN_theta ψ₀ k.2, hKψ _ hk]
    simp
  have hpiece : ∀ z, z ∈ orbitPiece L₀ x₀ → sigma z ∈ orbitPiece L₀ x₀ := by
    rintro _ ⟨l, hl, rfl⟩
    exact ⟨swapTheta l, swapTheta_mem_prod hl, by rw [sigma_smul, hfix]⟩
  obtain ⟨f₀, hf₀, hf₀O⟩ := exists_lift_orbit_piece hU hC hO hL₀c hL₀o (mem_orbit_self x₀)
  set W' := W ⊔ Submodule.span ℂ {f₀}
  have hW'U : W' ≤ supportedIn U :=
    sup_le (sup_le (relSpan_le_supportedIn _ hUinv) inf_le_left)
      (Submodule.span_le.2 (Set.singleton_subset_iff.2 hf₀))
  have hmem := supportedIn_le_of_base hU hC hO hUinv (chi ψ₀) hW'U (le_sup_left.trans le_sup_left)
    L₀ hL₀c hL₀o hχL₀ f₀ hf₀O (le_sup_left (b := supportedIn U ⊓ vanishingOn C)
      (le_sup_right (a := W) (Submodule.mem_span_singleton_self f₀))) hf
  obtain ⟨p, hp, k, hk, hpk⟩ := Submodule.mem_sup.1 hmem
  obtain ⟨r, hr, q, hq, hrq⟩ := Submodule.mem_sup.1 hp
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hq

  have hvan : ∀ {m : GL (Fin n) F → ℂ}, m ∈ supportedIn U →
      (∀ z ∈ orbit (NN F n) x₀, m z = m (sigma z)) → m - sigmaL m ∈ supportedIn U ⊓ vanishingOn C := by
    intro m hm heq
    refine ⟨sub_mem hm (hsU hm), fun z hz => ?_⟩
    show m z - m (sigma z) = 0
    by_cases hzU : z ∈ U
    · have hzO : z ∈ orbit (NN F n) x₀ := by rw [← hO]; exact ⟨hzU, hz⟩
      rw [heq z hzO, sub_self]
    · have h1 : m z = 0 := Function.notMem_support.1 fun h => hzU (hm.2 h)
      have h2 : m (sigma z) = 0 := Function.notMem_support.1 fun h => hzU ((hUσ z).1 (hm.2 h))
      rw [h1, h2, sub_zero]
  have hf₀σ : f₀ - sigmaL f₀ ∈ supportedIn U ⊓ vanishingOn C := by
    refine hvan hf₀ fun z hz => ?_
    rw [hf₀O z hz, hf₀O _ (hσO z hz)]
    by_cases hzp : z ∈ orbitPiece L₀ x₀
    · rw [Set.indicator_of_mem hzp, Set.indicator_of_mem (hpiece z hzp)]
      rfl
    · have : sigma z ∉ orbitPiece L₀ x₀ := fun h => hzp (by simpa [sigma_sigma] using hpiece _ h)
      rw [Set.indicator_of_notMem hzp, Set.indicator_of_notMem this]
  have hkσ : k - sigmaL k ∈ supportedIn U ⊓ vanishingOn C := by
    refine hvan hk.1 fun z hz => ?_
    rw [hk.2 z (hOC z hz).2, hk.2 _ (hOC _ (hσO z hz)).2]
  have e : f - sigmaL f = (r - sigmaL r) + c • (f₀ - sigmaL f₀) + (k - sigmaL k) := by
    rw [← hpk, ← hrq, map_add, map_add, map_smul, smul_sub]
    abel
  rw [e]
  refine add_mem (add_mem (le_sup_left (b := supportedIn U ⊓ vanishingOn C)
    (sub_mem hr (hWσ r hr))) (Submodule.smul_mem _ _ (le_sup_right (a := W) hf₀σ)))
    (le_sup_right (a := W) hkσ)

/- English proof (translation)
Assume the negation of the conclusion as `hx`. Use `set S : Set (GL (Fin n) F) := {y | ¬ ∃ V : Set (GL (Fin n) F), IsOpen V ∧ y ∈ V ∧ supportedIn V ≤ goodSub n ψ₀}`. Use `set Φ : GL (Fin n) F → ℕ := fun y => ∑ i, ∑ j, llRank i j y`. Establish `hS : S.Nonempty` using `⟨x, hx⟩`. Establish `hbdd : BddAbove (Φ '' S)`.

Use `⟨n * (n * n), ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨y, -, rfl⟩`. Combine the equalities or inequalities in the displayed calculation. Choose the witnesses or unpack the hypotheses as in `⟨g, hgS, hgmax⟩ : ∃ g ∈ S, ∀ y ∈ S, Φ y ≤ Φ g := by`. Take `⟨g, hg, hgeq⟩` from `Nat.sSup_mem (hS.image Φ) hbdd`.

Conclude with `⟨g, hg, fun y hy => hgeq ▸ le_csSup hbdd ⟨y, hy, rfl⟩⟩`. Apply `hgS` to reduce the goal to its premises. Use `set w := bruhatCell g with hw`. Establish `hlarger : ∀ y ∈ cellGe g, y ∉ cellLe g → ∃ V : Set (GL (Fin n) F), IsOpen V ∧ y ∈ V ∧ supportedIn V ≤ goodSub n ψ₀`. Introduce `y hy1 hy2`.

Assume the negation of the conclusion as `hyS`. Establish `hle` using `hgmax y hyS`. Simplify using `only [cellLe, Set.mem_ofPred_eq, not_forall, not_le] at hy2`. Take `⟨i, j, hij⟩` from `hy2`. Establish `hlt : Φ g < Φ y` using `Finset.sum_lt_sum (fun i _ => Finset.sum_le_sum fun j _ => hy1 i j) ⟨i, Finset.mem_univ _, Finset.sum_lt_sum (fun j _ => hy1 i j) ⟨j, Finset.mem_univ _, hij⟩⟩`.

Use linear arithmetic over natural numbers and integers. Establish `hinvGe : ∀ k : NN F n, ∀ y ∈ cellGe g, k • y ∈ cellGe g` using `fun k y hy => smul_mem_cellGe k hy`. Establish `hRR : ∀ {r : GL (Fin n) F → ℂ} {U : Set (GL (Fin n) F)}, r ∈ relSpan (chi (n` using `n) ψ₀) U → r ∈ rel n ψ₀ := fun hr => relSpan_mono (subset_univ _) hr`. Establish `hσR : ∀ {r : GL (Fin n) F → ℂ} {U : Set (GL (Fin n) F)}, r ∈ relSpan (chi (n` using `n) ψ₀) U → sigmaL r ∈ rel n ψ₀ := fun hr => relSpan_mono (subset_univ _) (sigmaL_mem_relSpan ψ₀ hr)`. Distinguish the cases in `hA : ∀ h : GL (Fin n) F, bruhatCell h = w → bruhatCell (sigma h) = w`.

Use `set U := cellGe g ∩ sigma ⁻¹' cellGe g with hUdef`. Establish `hUo : IsOpen U` using `(isOpen_cellGe g).inter ((isOpen_cellGe g).preimage continuous_sigma)`. Establish `hUinv : ∀ k : NN F n, ∀ y ∈ U, k • y ∈ U` using `fun k y hy => ⟨smul_mem_cellGe k hy.1, by show sigma (k • y) ∈ cellGe g`. Rewrite using `[sigma_smul]`. Conclude with `smul_mem_cellGe _ hy.2⟩`.

Establish `hcellU : ∀ h, bruhatCell h = bruhatCell g → h ∈ U` using `fun h hh => ⟨mem_cellGe_of_eq hh, mem_cellGe_of_eq (hA h hh)⟩`. Establish `hUσ : ∀ y, sigma y ∈ U ↔ y ∈ U` using `fun y => by show sigma y ∈ cellGe g ∧ sigma (sigma y) ∈ cellGe g ↔ y ∈ cellGe g ∧ sigma y ∈ cellGe g`. Rewrite using `[sigma_sigma, and_comm]`. Use `⟨U, hUo, hcellU g rfl, ?_⟩` and prove the remaining obligations. Establish `hgood : supportedIn (U \ cellLe g) ≤ goodSub n ψ₀` using `supportedIn_le_of_local fun y hy => hlarger y hy.1.1 hy.2`.

Introduce `f hf`. Establish `hmem` using `cell_relevant ψ₀ hψ hψ₁ hUo hUinv inter_subset_left hcellU hUσ hA hf`. Take `⟨r, hr, k, hk, hrk⟩` from `Submodule.mem_sup.1 hmem`. Establish `hk' : k ∈ supportedIn (U \ cellLe g)` using `⟨hk.1.1, fun y hy => ⟨hk.1.2 hy, fun hyC => hy (hk.2 y hyC)⟩⟩`. Establish `hkgood` using `(mem_goodSub ψ₀).1 (hgood hk')`.

Establish `hneg : sigmaL r + sigmaL k = -(r + k)`. Rewrite using `[← map_add, hrk, map_sub, sigmaL_sigmaL]`. Normalize the expressions using the abelian group laws. Establish `hsum : k + sigmaL k ∈ rel n ψ₀`. Establish `e : k + sigmaL k = -(r + sigmaL r)`.

Rewrite using `[← sub_eq_zero]`. Rewrite `hneg` using `[← sub_eq_zero]`. Establish `h2 : k + sigmaL k - -(r + sigmaL r) = sigmaL r + sigmaL k - -(r + k)` using `by abel`. Rewrite using `[h2, hneg]`. Rewrite using `[e]`.

Conclude with `neg_mem (add_mem (hRR hr) (hσR hr))`. Establish `hk2 : (2 : ℂ) • k ∈ rel n ψ₀`. Establish `e : (2 : ℂ) • k = (k + sigmaL k) + (k - sigmaL k)`. Rewrite using `[two_smul]`. Normalize the expressions using the abelian group laws.

Rewrite using `[e]`. Conclude with `add_mem hsum hkgood`. Establish `hkR : k ∈ rel n ψ₀`. Use `(rel n ψ₀).smul_mem (1 / 2 : ℂ) hk2` as an intermediate fact. Rewrite `this` using `[smul_smul, one_div, inv_mul_cancel₀ two_ne_zero, one_smul]`. Then use the resulting hypothesis.

Rewrite using `[mem_goodSub, ← hrk]`. Conclude with `add_mem (hRR hr) hkR`. Use `push Not at hA`. Take `⟨h₀, hh₀, hσh₀⟩` from `hA`. Establish `hirr : ∀ t, Irrelevant ψ₀ w t`.

Introduce `t`. Assume the negation of the conclusion as `hrel`. Establish `hfix` using `sigma_eq_of_not_irrelevant ψ₀ hψ₁ hrel`. Apply `hσh₀` to reduce the goal to its premises. Establish `e₁ : bruhatCell (sigma h₀) = Fin.revPerm * w⁻¹ * Fin.revPerm` using `bruhatCell_eq_iff.2 (sigma_mem_doubleCoset_permGL (bruhatCell_eq_iff.1 hh₀))`.

Establish `e₂ : bruhatCell (sigma (Iwasawa.diagGL F n t * permGL F w)) = Fin.revPerm * w⁻¹ * Fin.revPerm` using `bruhatCell_eq_iff.2 (sigma_mem_doubleCoset_permGL (bruhatCell_eq_iff.1 (bruhatCell_diag_perm t w)))`. Rewrite `e₂` using `[hfix, bruhatCell_diag_perm]`. Rewrite using `[e₁, ← e₂]`. Use `⟨cellGe g, isOpen_cellGe g, mem_cellGe_of_eq rfl, ?_⟩` and prove the remaining obligations. Establish `hgood : supportedIn (cellGe g \ cellLe g) ≤ goodSub n ψ₀` using `supportedIn_le_of_local fun y hy => hlarger y hy.1 hy.2`.

Introduce `f hf`. Establish `hmem` using `cell_irrelevant ψ₀ hψ (isOpen_cellGe g) hinvGe subset_rfl (fun h hh => mem_cellGe_of_eq hh) hirr hf`. Take `⟨r, hr, k, hk, rfl⟩` from `Submodule.mem_sup.1 hmem`. Establish `hk' : k ∈ supportedIn (cellGe g \ cellLe g)` using `⟨hk.1.1, fun y hy => ⟨hk.1.2 hy, fun hyC => hy (hk.2 y hyC)⟩⟩`. Rewrite using `[mem_goodSub]`.

Establish `e : r + k - sigmaL (r + k) = (r - sigmaL r) + (k - sigmaL k)`. Rewrite using `[map_add]`. Normalize the expressions using the abelian group laws. Rewrite using `[e]`. Conclude with `add_mem (sub_mem (hRR hr) (hσR hr)) ((mem_goodSub ψ₀).1 (hgood hk'))`.
-/
theorem exists_good_nhds (hψ : Continuous ψ₀) (hψ₁ : ψ₀ ≠ 1) (x : GL (Fin n) F) :
    ∃ V : Set (GL (Fin n) F), IsOpen V ∧ x ∈ V ∧ supportedIn V ≤ goodSub n ψ₀ := by
  by_contra hx
  set S : Set (GL (Fin n) F) :=
    {y | ¬ ∃ V : Set (GL (Fin n) F), IsOpen V ∧ y ∈ V ∧ supportedIn V ≤ goodSub n ψ₀}
  set Φ : GL (Fin n) F → ℕ := fun y => ∑ i, ∑ j, llRank i j y
  have hS : S.Nonempty := ⟨x, hx⟩
  have hbdd : BddAbove (Φ '' S) := by
    refine ⟨n * (n * n), ?_⟩
    rintro _ ⟨y, -, rfl⟩
    calc Φ y ≤ ∑ _i : Fin n, ∑ _j : Fin n, n :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => llRank_le i j y
      _ = n * (n * n) := by simp
  obtain ⟨g, hgS, hgmax⟩ : ∃ g ∈ S, ∀ y ∈ S, Φ y ≤ Φ g := by
    obtain ⟨g, hg, hgeq⟩ := Nat.sSup_mem (hS.image Φ) hbdd
    exact ⟨g, hg, fun y hy => hgeq ▸ le_csSup hbdd ⟨y, hy, rfl⟩⟩
  apply hgS
  set w := bruhatCell g with hw
  have hlarger : ∀ y ∈ cellGe g, y ∉ cellLe g →
      ∃ V : Set (GL (Fin n) F), IsOpen V ∧ y ∈ V ∧ supportedIn V ≤ goodSub n ψ₀ := by
    intro y hy1 hy2
    by_contra hyS
    have hle := hgmax y hyS
    simp only [cellLe, Set.mem_ofPred_eq, not_forall, not_le] at hy2
    obtain ⟨i, j, hij⟩ := hy2
    have hlt : Φ g < Φ y :=
      Finset.sum_lt_sum (fun i _ => Finset.sum_le_sum fun j _ => hy1 i j)
        ⟨i, Finset.mem_univ _, Finset.sum_lt_sum (fun j _ => hy1 i j) ⟨j, Finset.mem_univ _, hij⟩⟩
    omega
  have hinvGe : ∀ k : NN F n, ∀ y ∈ cellGe g, k • y ∈ cellGe g := fun k y hy => smul_mem_cellGe k hy
  have hRR : ∀ {r : GL (Fin n) F → ℂ} {U : Set (GL (Fin n) F)}, r ∈ relSpan (chi (n := n) ψ₀) U →
      r ∈ rel n ψ₀ := fun hr => relSpan_mono (subset_univ _) hr
  have hσR : ∀ {r : GL (Fin n) F → ℂ} {U : Set (GL (Fin n) F)}, r ∈ relSpan (chi (n := n) ψ₀) U →
      sigmaL r ∈ rel n ψ₀ := fun hr => relSpan_mono (subset_univ _) (sigmaL_mem_relSpan ψ₀ hr)
  by_cases hA : ∀ h : GL (Fin n) F, bruhatCell h = w → bruhatCell (sigma h) = w
  ·
    set U := cellGe g ∩ sigma ⁻¹' cellGe g with hUdef
    have hUo : IsOpen U := (isOpen_cellGe g).inter ((isOpen_cellGe g).preimage continuous_sigma)
    have hUinv : ∀ k : NN F n, ∀ y ∈ U, k • y ∈ U := fun k y hy =>
      ⟨smul_mem_cellGe k hy.1, by
        show sigma (k • y) ∈ cellGe g
        rw [sigma_smul]
        exact smul_mem_cellGe _ hy.2⟩
    have hcellU : ∀ h, bruhatCell h = bruhatCell g → h ∈ U := fun h hh =>
      ⟨mem_cellGe_of_eq hh, mem_cellGe_of_eq (hA h hh)⟩
    have hUσ : ∀ y, sigma y ∈ U ↔ y ∈ U := fun y => by
      show sigma y ∈ cellGe g ∧ sigma (sigma y) ∈ cellGe g ↔ y ∈ cellGe g ∧ sigma y ∈ cellGe g
      rw [sigma_sigma, and_comm]
    refine ⟨U, hUo, hcellU g rfl, ?_⟩
    have hgood : supportedIn (U \ cellLe g) ≤ goodSub n ψ₀ :=
      supportedIn_le_of_local fun y hy => hlarger y hy.1.1 hy.2
    intro f hf
    have hmem := cell_relevant ψ₀ hψ hψ₁ hUo hUinv inter_subset_left hcellU hUσ hA hf
    obtain ⟨r, hr, k, hk, hrk⟩ := Submodule.mem_sup.1 hmem
    have hk' : k ∈ supportedIn (U \ cellLe g) :=
      ⟨hk.1.1, fun y hy => ⟨hk.1.2 hy, fun hyC => hy (hk.2 y hyC)⟩⟩
    have hkgood := (mem_goodSub ψ₀).1 (hgood hk')
    have hneg : sigmaL r + sigmaL k = -(r + k) := by
      rw [← map_add, hrk, map_sub, sigmaL_sigmaL]
      abel
    have hsum : k + sigmaL k ∈ rel n ψ₀ := by
      have e : k + sigmaL k = -(r + sigmaL r) := by
        rw [← sub_eq_zero]
        rw [← sub_eq_zero] at hneg
        have h2 : k + sigmaL k - -(r + sigmaL r) = sigmaL r + sigmaL k - -(r + k) := by abel
        rw [h2, hneg]
      rw [e]
      exact neg_mem (add_mem (hRR hr) (hσR hr))
    have hk2 : (2 : ℂ) • k ∈ rel n ψ₀ := by
      have e : (2 : ℂ) • k = (k + sigmaL k) + (k - sigmaL k) := by
        rw [two_smul]
        abel
      rw [e]
      exact add_mem hsum hkgood
    have hkR : k ∈ rel n ψ₀ := by
      have := (rel n ψ₀).smul_mem (1 / 2 : ℂ) hk2
      rwa [smul_smul, one_div, inv_mul_cancel₀ two_ne_zero, one_smul] at this
    rw [mem_goodSub, ← hrk]
    exact add_mem (hRR hr) hkR
  ·
    push Not at hA
    obtain ⟨h₀, hh₀, hσh₀⟩ := hA
    have hirr : ∀ t, Irrelevant ψ₀ w t := by
      intro t
      by_contra hrel
      have hfix := sigma_eq_of_not_irrelevant ψ₀ hψ₁ hrel
      apply hσh₀
      have e₁ : bruhatCell (sigma h₀) = Fin.revPerm * w⁻¹ * Fin.revPerm :=
        bruhatCell_eq_iff.2 (sigma_mem_doubleCoset_permGL (bruhatCell_eq_iff.1 hh₀))
      have e₂ : bruhatCell (sigma (Iwasawa.diagGL F n t * permGL F w)) =
          Fin.revPerm * w⁻¹ * Fin.revPerm :=
        bruhatCell_eq_iff.2 (sigma_mem_doubleCoset_permGL
          (bruhatCell_eq_iff.1 (bruhatCell_diag_perm t w)))
      rw [hfix, bruhatCell_diag_perm] at e₂
      rw [e₁, ← e₂]
    refine ⟨cellGe g, isOpen_cellGe g, mem_cellGe_of_eq rfl, ?_⟩
    have hgood : supportedIn (cellGe g \ cellLe g) ≤ goodSub n ψ₀ :=
      supportedIn_le_of_local fun y hy => hlarger y hy.1 hy.2
    intro f hf
    have hmem := cell_irrelevant ψ₀ hψ (isOpen_cellGe g) hinvGe subset_rfl
      (fun h hh => mem_cellGe_of_eq hh) hirr hf
    obtain ⟨r, hr, k, hk, rfl⟩ := Submodule.mem_sup.1 hmem
    have hk' : k ∈ supportedIn (cellGe g \ cellLe g) :=
      ⟨hk.1.1, fun y hy => ⟨hk.1.2 hy, fun hyC => hy (hk.2 y hyC)⟩⟩
    rw [mem_goodSub]
    have e : r + k - sigmaL (r + k) = (r - sigmaL r) + (k - sigmaL k) := by
      rw [map_add]
      abel
    rw [e]
    exact add_mem (sub_mem (hRR hr) (hσR hr)) ((mem_goodSub ψ₀).1 (hgood hk'))

/- English proof (translation)
Establish `key : supportedIn (univ : Set (GL (Fin n) F)) ≤ goodSub n ψ₀` using `supportedIn_le_of_local fun x _ => exists_good_nhds ψ₀ hψ hψ₁ x`. Conclude with `key ⟨hf, subset_univ _⟩`.
-/
theorem sub_sigma_mem_rel (hψ : Continuous ψ₀) (hψ₁ : ψ₀ ≠ 1) {f : GL (Fin n) F → ℂ}
    (hf : f ∈ locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ) :
    f - sigmaL f ∈ rel n ψ₀ := by
  have key : supportedIn (univ : Set (GL (Fin n) F)) ≤ goodSub n ψ₀ :=
    supportedIn_le_of_local fun x _ => exists_good_nhds ψ₀ hψ hψ₁ x
  exact key ⟨hf, subset_univ _⟩

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] in

/- English proof (translation)
Use `⟨hf.1.comp_continuous (by fun_prop), ?_⟩` and prove the remaining obligations. Conclude with `hf.2.comp_homeomorph ((Homeomorph.mulLeft a⁻¹).trans (Homeomorph.mulRight b))`.
-/
theorem twoSided_mem [IsTopologicalRing F] {f : GL (Fin n) F → ℂ}
    (hf : f ∈ locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ) (a b : GL (Fin n) F) :
    (fun x => f (a⁻¹ * x * b)) ∈ locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ := by
  refine ⟨hf.1.comp_continuous (by fun_prop), ?_⟩
  exact hf.2.comp_homeomorph ((Homeomorph.mulLeft a⁻¹).trans (Homeomorph.mulRight b))

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] in

/- English proof (translation)
The claim follows from `(sigmaL_mem_supportedIn (U := univ) ⟨hf, subset_univ _⟩).1`.
-/
theorem comp_sigma_mem [IsTopologicalRing F] {f : GL (Fin n) F → ℂ}
    (hf : f ∈ locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ) :
    (fun x => f (sigma x)) ∈ locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ :=
  (sigmaL_mem_supportedIn (U := univ) ⟨hf, subset_univ _⟩).1

/- English proof (translation)
Introduce `_ hr` and use `(relSpan_le_supportedIn (chi ψ₀) (fun _ _ _ => mem_univ _) hr).1`.
-/
theorem rel_le : rel n ψ₀ ≤ locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ :=
  fun _ hr => (relSpan_le_supportedIn (chi ψ₀) (fun _ _ _ => mem_univ _) hr).1

/- English proof (translation)
Establish `hrel : ∀ r (hr : r ∈ rel n ψ₀), D ⟨r, rel_le ψ₀ hr⟩ = 0`. Introduce `r hr`. Proceed by induction on `hr using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨k, g, hg, rfl⟩` from `hx`.

Establish `e : (⟨transl k g - chi ψ₀ k • g, rel_le ψ₀ (Submodule.subset_span ⟨k, g, hg, rfl⟩)⟩ : locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ) = ⟨fun x => g ((k.1 : GL (Fin n) F)⁻¹ * x * (k.2 : GL (Fin n) F)), twoSided_mem hg.1 _ _⟩ - chi ψ₀ k • ⟨g, hg.1⟩`. Use `Subtype.ext ?_` and prove the remaining obligations. Use function extensionality and compare the values at `x`. Simplify using `[biAction_smul]`. Rewrite using `[e, map_sub, map_smul, hD ⟨g, hg.1⟩ _ _ k.1.2 k.2.2, chi_apply, smul_eq_mul, sub_self]`.

Consider the case `zero`. Establish `: (⟨0, rel_le ψ₀ (zero_mem _)⟩ : locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ) = 0`. Both sides reduce to the same expression. Rewrite using `[this, map_zero]`. Consider the case `add x y hx hy ihx ihy`.

Establish `: (⟨x + y, rel_le ψ₀ (add_mem hx hy)⟩ : locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ) = ⟨x, rel_le ψ₀ hx⟩ + ⟨y, rel_le ψ₀ hy⟩` using `rfl`. Rewrite using `[this, map_add, ihx, ihy, add_zero]`. Consider the case `smul c x hx ihx`. Establish `: (⟨c • x, rel_le ψ₀ (Submodule.smul_mem _ c hx)⟩ : locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ) = c • ⟨x, rel_le ψ₀ hx⟩` using `rfl`. Rewrite using `[this, map_smul, ihx, smul_zero]`.

Establish `h` using `hrel _ (sub_sigma_mem_rel ψ₀ hψ hψ₁ f.2)`. Establish `e : (⟨(f : GL (Fin n) F → ℂ) - sigmaL f, rel_le ψ₀ (sub_sigma_mem_rel ψ₀ hψ hψ₁ f.2)⟩ : locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ) = f - ⟨fun x => (f : GL (Fin n) F → ℂ) (sigma x), comp_sigma_mem f.2⟩` using `rfl`. Rewrite `h` using `[e, map_sub, sub_eq_zero]`. Conclude with `h.symm`.
-/
theorem distribution_sigma_invariant (hψ : Continuous ψ₀) (hψ₁ : ψ₀ ≠ 1)
    (D : Module.Dual ℂ (locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ))
    (hD : ∀ (f : locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ) (u₁ u₂ : GL (Fin n) F)
      (_ : u₁ ∈ Iwasawa.unipotent F n) (_ : u₂ ∈ Iwasawa.unipotent F n),
      D ⟨fun x => (f : GL (Fin n) F → ℂ) (u₁⁻¹ * x * u₂), twoSided_mem f.2 u₁ u₂⟩ =
        psiN ψ₀ u₁ * (psiN ψ₀ u₂)⁻¹ * D f)
    (f : locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ) :
    D ⟨fun x => (f : GL (Fin n) F → ℂ) (sigma x), comp_sigma_mem f.2⟩ = D f := by
  have hrel : ∀ r (hr : r ∈ rel n ψ₀), D ⟨r, rel_le ψ₀ hr⟩ = 0 := by
    intro r hr
    induction hr using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, g, hg, rfl⟩ := hx
      have e : (⟨transl k g - chi ψ₀ k • g, rel_le ψ₀ (Submodule.subset_span ⟨k, g, hg, rfl⟩)⟩ :
          locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ) =
          ⟨fun x => g ((k.1 : GL (Fin n) F)⁻¹ * x * (k.2 : GL (Fin n) F)),
            twoSided_mem hg.1 _ _⟩ - chi ψ₀ k • ⟨g, hg.1⟩ := by
        refine Subtype.ext ?_
        funext x
        simp [biAction_smul]
      rw [e, map_sub, map_smul, hD ⟨g, hg.1⟩ _ _ k.1.2 k.2.2, chi_apply, smul_eq_mul, sub_self]
    | zero =>
      have : (⟨0, rel_le ψ₀ (zero_mem _)⟩ : locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ) = 0 :=
        rfl
      rw [this, map_zero]
    | add x y hx hy ihx ihy =>
      have : (⟨x + y, rel_le ψ₀ (add_mem hx hy)⟩ :
          locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ) =
          ⟨x, rel_le ψ₀ hx⟩ + ⟨y, rel_le ψ₀ hy⟩ := rfl
      rw [this, map_add, ihx, ihy, add_zero]
    | smul c x hx ihx =>
      have : (⟨c • x, rel_le ψ₀ (Submodule.smul_mem _ c hx)⟩ :
          locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ) = c • ⟨x, rel_le ψ₀ hx⟩ := rfl
      rw [this, map_smul, ihx, smul_zero]
  have h := hrel _ (sub_sigma_mem_rel ψ₀ hψ hψ₁ f.2)
  have e : (⟨(f : GL (Fin n) F → ℂ) - sigmaL f, rel_le ψ₀ (sub_sigma_mem_rel ψ₀ hψ hψ₁ f.2)⟩ :
      locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ) =
      f - ⟨fun x => (f : GL (Fin n) F → ℂ) (sigma x), comp_sigma_mem f.2⟩ := rfl
  rw [e, map_sub, sub_eq_zero] at h
  exact h.symm

end LocalField

end Whittaker

end GroundTheory.Automorphic
