import Mathlib
import GroundTheory.AutomorphicForms.SmoothRep

noncomputable section

namespace GroundTheory.Automorphic

open Set Filter Topology

section General

variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ G V)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem dual_apply_apply (g : G) (f : Module.Dual ℂ V) (v : V) :
    Representation.dual ρ g f v = f (ρ g⁻¹ v) := rfl

variable {ρ} in

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hf h hh v`. Use `LinearMap.congr_fun (hf h⁻¹ (inv_mem hh)) v` as an intermediate fact. Rewrite `this` using `[dual_apply_apply, inv_inv]`. Then use the resulting hypothesis. Introduce `hf h hh`.

Use extensionality with `v`. Rewrite using `[dual_apply_apply]`. Conclude with `hf _ (inv_mem hh) v`.
-/
theorem mem_fixedVectors_dual {H : Subgroup G} {f : Module.Dual ℂ V} :
    f ∈ fixedVectors (Representation.dual ρ) H ↔ ∀ h ∈ H, ∀ v, f (ρ h v) = f v := by
  constructor
  · intro hf h hh v
    have := LinearMap.congr_fun (hf h⁻¹ (inv_mem hh)) v
    rwa [dual_apply_apply, inv_inv] at this
  · intro hf h hh
    ext v
    rw [dual_apply_apply]
    exact hf _ (inv_mem hh) v

variable [TopologicalSpace G] [IsTopologicalGroup G]

variable {ρ} in

/- English proof (translation)
The claim follows from `Subgroup.isOpen_mono (mem_fixedVectors_iff_le.1 hv) hH`.
-/
theorem mem_smoothVectors_of_mem_fixedVectors {H : Subgroup G} (hH : IsOpen (H : Set G))
    {v : V} (hv : v ∈ fixedVectors ρ H) : v ∈ smoothVectors ρ :=
  Subgroup.isOpen_mono (mem_fixedVectors_iff_le.1 hv) hH

variable {ρ} in
/- English proof (translation)
Simplify using `only [mem_fixedVectors, Subtype.ext_iff, coe_smoothPart_apply]`.
-/
theorem mem_fixedVectors_smoothPart {H : Subgroup G} {x : smoothVectors ρ} :
    x ∈ fixedVectors (smoothPart ρ) H ↔ (x : V) ∈ fixedVectors ρ H := by
  simp only [mem_fixedVectors, Subtype.ext_iff, coe_smoothPart_apply]

def contragredient : Representation ℂ G (smoothVectors (Representation.dual ρ)) :=
  smoothPart (Representation.dual ρ)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem contragredient_apply_apply (g : G) (x : smoothVectors (Representation.dual ρ)) (v : V) :
    ((contragredient ρ g x : smoothVectors (Representation.dual ρ)) : Module.Dual ℂ V) v =
      (x : Module.Dual ℂ V) (ρ g⁻¹ v) := rfl

/- English proof (translation)
The claim follows from `isSmooth_smoothPart _`.
-/
theorem isSmooth_contragredient : IsSmooth (contragredient ρ) :=
  isSmooth_smoothPart _

variable {ρ} in
/- English proof (translation)
The claim follows from `mem_fixedVectors_smoothPart.trans mem_fixedVectors_dual`.
-/
theorem mem_fixedVectors_contragredient {H : Subgroup G}
    {x : smoothVectors (Representation.dual ρ)} :
    x ∈ fixedVectors (contragredient ρ) H ↔
      ∀ h ∈ H, ∀ v, (x : Module.Dual ℂ V) (ρ h v) = (x : Module.Dual ℂ V) v :=
  mem_fixedVectors_smoothPart.trans mem_fixedVectors_dual

def restrictFixed (H : Subgroup G) :
    fixedVectors (contragredient ρ) H →ₗ[ℂ] Module.Dual ℂ (fixedVectors ρ H) :=
  (fixedVectors ρ H).subtype.dualMap ∘ₗ (smoothVectors (Representation.dual ρ)).subtype ∘ₗ
    (fixedVectors (contragredient ρ) H).subtype

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem restrictFixed_apply (H : Subgroup G) (x : fixedVectors (contragredient ρ) H)
    (v : fixedVectors ρ H) :
    restrictFixed ρ H x v =
      ((x : smoothVectors (Representation.dual ρ)) : Module.Dual ℂ V) v := rfl

def evalSmooth : V →ₗ[ℂ] Module.Dual ℂ (smoothVectors (Representation.dual ρ)) :=
  (smoothVectors (Representation.dual ρ)).subtype.dualMap ∘ₗ Module.Dual.eval ℂ V

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem evalSmooth_apply (v : V) (x : smoothVectors (Representation.dual ρ)) :
    evalSmooth ρ v x = (x : Module.Dual ℂ V) v := rfl

variable {ρ} in

/- English proof (translation)
Use `Subgroup.isOpen_mono (H₁ := stabilizerOf ρ v) (fun g hg => ?_) hv` and prove the remaining obligations. Rewrite `hg`, the goal using `[mem_stabilizerOf]`. Use extensionality with `x`. Rewrite using `[dual_apply_apply, evalSmooth_apply, evalSmooth_apply, contragredient_apply_apply, inv_inv, hg]`.
-/
theorem evalSmooth_mem {v : V} (hv : v ∈ smoothVectors ρ) :
    evalSmooth ρ v ∈ smoothVectors (Representation.dual (contragredient ρ)) := by
  refine Subgroup.isOpen_mono (H₁ := stabilizerOf ρ v) (fun g hg => ?_) hv
  rw [mem_stabilizerOf] at hg ⊢
  ext x
  rw [dual_apply_apply, evalSmooth_apply, evalSmooth_apply, contragredient_apply_apply, inv_inv,
    hg]

variable {ρ} in

def toDoubleContragredient (hρ : IsSmooth ρ) :
    Representation.IntertwiningMap ρ (contragredient (contragredient ρ)) where
  toLinearMap := (evalSmooth ρ).codRestrict _ fun v => evalSmooth_mem (hρ v)
  isIntertwining' g := by
    refine LinearMap.ext fun v => Subtype.ext (LinearMap.ext fun x => ?_)
    change (x : Module.Dual ℂ V) (ρ g v) = (x : Module.Dual ℂ V) (ρ g⁻¹⁻¹ v)
    rw [inv_inv]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem toDoubleContragredient_apply_apply (hρ : IsSmooth ρ) (v : V)
    (x : smoothVectors (Representation.dual ρ)) :
    ((toDoubleContragredient hρ v : smoothVectors (Representation.dual (contragredient ρ))) :
      Module.Dual ℂ (smoothVectors (Representation.dual ρ))) x = (x : Module.Dual ℂ V) v := rfl

end General

section LocallyProfinite

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} {K : Subgroup G}

def extendFixed (hρ : IsSmooth ρ) (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))
    (μ : Module.Dual ℂ (fixedVectors ρ K)) : fixedVectors (contragredient ρ) K :=
  have hinv : ∀ k ∈ K, ∀ v, (μ ∘ₗ fixedProj ρ hρ hKc hKo) (ρ k v) =
      (μ ∘ₗ fixedProj ρ hρ hKc hKo) v := fun k hk v => by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, fixedProj_apply_act hρ hKc hKo hk]
  ⟨⟨μ ∘ₗ fixedProj ρ hρ hKc hKo,
    mem_smoothVectors_of_mem_fixedVectors hKo (mem_fixedVectors_dual.2 hinv)⟩,
    mem_fixedVectors_contragredient.2 hinv⟩

variable (hρ : IsSmooth ρ) (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))
include hρ hKc hKo

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Establish `hx' : ((x : smoothVectors (Representation.dual ρ)) : Module.Dual ℂ V) = 0` using `eq_of_invariant_of_eqOn hρ hKc hKo (mem_fixedVectors_contragredient.1 x.2) (fun _ _ _ => rfl) fun v hv => LinearMap.congr_fun hx ⟨v, hv⟩`. Conclude with `Subtype.ext (Subtype.ext hx')`.

Introduce `μ`. Use `⟨extendFixed hρ hKc hKo μ, LinearMap.ext fun v => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `μ (fixedProj ρ hρ hKc hKo v) = μ v`. Rewrite using `[Subtype.ext (fixedProj_apply_of_mem hρ hKc hKo v.2)]`.
-/
theorem restrictFixed_bijective : Function.Bijective (restrictFixed ρ K) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have hx' : ((x : smoothVectors (Representation.dual ρ)) : Module.Dual ℂ V) = 0 :=
      eq_of_invariant_of_eqOn hρ hKc hKo (mem_fixedVectors_contragredient.1 x.2)
        (fun _ _ _ => rfl) fun v hv => LinearMap.congr_fun hx ⟨v, hv⟩
    exact Subtype.ext (Subtype.ext hx')
  · intro μ
    refine ⟨extendFixed hρ hKc hKo μ, LinearMap.ext fun v => ?_⟩
    change μ (fixedProj ρ hρ hKc hKo v) = μ v
    rw [Subtype.ext (fixedProj_apply_of_mem hρ hKc hKo v.2)]

def fixedContragredientEquiv :
    fixedVectors (contragredient ρ) K ≃ₗ[ℂ] Module.Dual ℂ (fixedVectors ρ K) :=
  LinearEquiv.ofBijective (restrictFixed ρ K) (restrictFixed_bijective hρ hKc hKo)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem fixedContragredientEquiv_apply (x : fixedVectors (contragredient ρ) K) :
    fixedContragredientEquiv hρ hKc hKo x = restrictFixed ρ K x := rfl

end LocallyProfinite

section Admissible

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

/- English proof (translation)
Use `⟨isSmooth_contragredient ρ, fun K hKc hKo => ?_⟩` and prove the remaining obligations. Use `h.2 K hKc hKo` as an intermediate fact. Conclude with `LinearEquiv.finiteDimensional (fixedContragredientEquiv h.1 hKc hKo).symm`.
-/
theorem isAdmissible_contragredient (h : IsAdmissible ρ) : IsAdmissible (contragredient ρ) := by
  refine ⟨isSmooth_contragredient ρ, fun K hKc hKo => ?_⟩
  have := h.2 K hKc hKo
  exact LinearEquiv.finiteDimensional (fixedContragredientEquiv h.1 hKc hKo).symm

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `v hv`. Take `⟨K, hKc, hKo, hvK⟩` from `(isSmooth_iff_forall_exists ρ).1 h.1 v`. Use `set e := fixedContragredientEquiv h.1 hKc hKo`.

Establish `hzero : (⟨v, hvK⟩ : fixedVectors ρ K) = 0`. Use `(Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun μ => ?_` and prove the remaining obligations. Establish `h1 : (((e.symm μ : fixedVectors (contragredient ρ) K) : smoothVectors (Representation.dual ρ)) : Module.Dual ℂ V) v = 0`. Use `congrArg (fun Φ : smoothVectors (Representation.dual (contragredient ρ)) => (Φ : Module.Dual ℂ (smoothVectors (Representation.dual ρ))) (e.symm μ : fixedVectors (contragredient ρ) K)) hv` as an intermediate fact. Conclude with `this`.

Establish `h2 : e (e.symm μ) = μ` using `e.apply_symm_apply μ`. Rewrite using `[← h2, fixedContragredientEquiv_apply, restrictFixed_apply]`. Conclude with `h1`. Simplify using `using congrArg Subtype.val hzero`. Introduce `Φ`.

Take `⟨K, hKc, hKo, hΦK⟩` from `(mem_smoothVectors_iff _).1 Φ.2`. Use `set e := fixedContragredientEquiv h.1 hKc hKo`. Use `h.2 K hKc hKo` as an intermediate fact. Set `ψ : Module.Dual ℂ (Module.Dual ℂ (fixedVectors ρ K))` to `(Φ : Module.Dual ℂ (smoothVectors (Representation.dual ρ))) ∘ₗ (fixedVectors (contragredient ρ) K).subtype ∘ₗ e.symm.toLinearMap`. Use `set w := (Module.evalEquiv ℂ (fixedVectors ρ K)).symm ψ`.

Establish `hw : ∀ μ : Module.Dual ℂ (fixedVectors ρ K), μ w = ψ μ` using `fun μ => LinearMap.congr_fun ((Module.evalEquiv ℂ (fixedVectors ρ K)).apply_symm_apply ψ) μ`. Use `⟨(w : V), Subtype.ext ?_⟩` and prove the remaining obligations. Use `eq_of_invariant_of_eqOn (isSmooth_contragredient ρ) hKc hKo (fun k hk x => ?_) (mem_fixedVectors_dual.1 hΦK) fun x hx => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(x : Module.Dual ℂ V) (ρ k⁻¹ w) = (x : Module.Dual ℂ V) w`. Rewrite using `[w.2 _ (inv_mem hk)]`.

Establish `h1 : (Φ : Module.Dual ℂ (smoothVectors (Representation.dual ρ))) x = ψ (e ⟨x, hx⟩)`. Simplify using `[ψ]`. Rewrite using `[h1, ← hw]`. Both sides reduce to the same expression.
-/
theorem toDoubleContragredient_bijective (h : IsAdmissible ρ) :
    Function.Bijective (toDoubleContragredient h.1) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro v hv
    obtain ⟨K, hKc, hKo, hvK⟩ := (isSmooth_iff_forall_exists ρ).1 h.1 v
    set e := fixedContragredientEquiv h.1 hKc hKo
    have hzero : (⟨v, hvK⟩ : fixedVectors ρ K) = 0 := by
      refine (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun μ => ?_
      have h1 : (((e.symm μ : fixedVectors (contragredient ρ) K) :
          smoothVectors (Representation.dual ρ)) : Module.Dual ℂ V) v = 0 := by
        have := congrArg (fun Φ : smoothVectors (Representation.dual (contragredient ρ)) =>
          (Φ : Module.Dual ℂ (smoothVectors (Representation.dual ρ)))
            (e.symm μ : fixedVectors (contragredient ρ) K)) hv
        exact this
      have h2 : e (e.symm μ) = μ := e.apply_symm_apply μ
      rw [← h2, fixedContragredientEquiv_apply, restrictFixed_apply]
      exact h1
    simpa using congrArg Subtype.val hzero
  · intro Φ
    obtain ⟨K, hKc, hKo, hΦK⟩ := (mem_smoothVectors_iff _).1 Φ.2
    set e := fixedContragredientEquiv h.1 hKc hKo
    have := h.2 K hKc hKo
    let ψ : Module.Dual ℂ (Module.Dual ℂ (fixedVectors ρ K)) :=
      (Φ : Module.Dual ℂ (smoothVectors (Representation.dual ρ))) ∘ₗ
        (fixedVectors (contragredient ρ) K).subtype ∘ₗ e.symm.toLinearMap
    set w := (Module.evalEquiv ℂ (fixedVectors ρ K)).symm ψ
    have hw : ∀ μ : Module.Dual ℂ (fixedVectors ρ K), μ w = ψ μ := fun μ =>
      LinearMap.congr_fun ((Module.evalEquiv ℂ (fixedVectors ρ K)).apply_symm_apply ψ) μ
    refine ⟨(w : V), Subtype.ext ?_⟩
    refine eq_of_invariant_of_eqOn (isSmooth_contragredient ρ) hKc hKo (fun k hk x => ?_)
      (mem_fixedVectors_dual.1 hΦK) fun x hx => ?_
    · change (x : Module.Dual ℂ V) (ρ k⁻¹ w) = (x : Module.Dual ℂ V) w
      rw [w.2 _ (inv_mem hk)]
    · have h1 : (Φ : Module.Dual ℂ (smoothVectors (Representation.dual ρ))) x =
          ψ (e ⟨x, hx⟩) := by
        simp [ψ]
      rw [h1, ← hw]
      rfl

end Admissible

end GroundTheory.Automorphic
