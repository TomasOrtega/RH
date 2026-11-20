import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHecke
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.LevCmp

section Glue

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

def compHom (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) :
    GAf L n →* GL (Fin n) (L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L)) :=
  (Matrix.GeneralLinearGroup.map (compAt L v)).comp (ReciprocityTheory.Aut.GA L n).subtype

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `congrArg Units.val h` as an intermediate fact. Simplify `this` using `[compHom]`. Introduce `h`.

Use extensionality with `i j`. Use `congrFun (congrFun h i) j` as an intermediate fact. Simplify `this` using `[compHom]`.
-/
theorem compHom_eq_one_iff (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (x : GAf L n) :
    compHom v x = 1 ↔ (x.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L v) = 1 := by
  constructor
  · intro h
    have := congrArg Units.val h
    simpa [compHom] using this
  · intro h
    ext i j
    have := congrFun (congrFun h i) j
    simpa [compHom] using this

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `congrArg Units.val h` as an intermediate fact. Simplify `this` using `[compHom]`. Introduce `h`.

Use extensionality with `i j`. Use `congrFun (congrFun h i) j` as an intermediate fact. Simplify `this` using `[compHom]`.
-/
theorem compHom_eq_iff (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (x y : GAf L n) :
    compHom v x = compHom v y ↔
      (x.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L v) = (y.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L v) := by
  constructor
  · intro h
    have := congrArg Units.val h
    simpa [compHom] using this
  · intro h
    ext i j
    have := congrFun (congrFun h i) j
    simpa [compHom] using this

/- English proof (translation)
Establish `hone : ∀ u κ, TrivOutside {u} κ → ∀ hκ : κ ∈ J, ∃ h' : κ ∈ J', χ ⟨κ, hκ⟩ = χ' ⟨κ, h'⟩`. Introduce `u κ hu hκ`. Distinguish the cases in `huS : u ∈ S`. Take `⟨h1, h2⟩` from `hloc u huS κ hu`. Conclude with `⟨h1.mp hκ, h2 hκ (h1.mp hκ)⟩`.

Establish `ht : TrivOutside Sᶜ κ`. Introduce `v hv`. Apply `hu v` to reduce the goal to its premises. Introduce and unpack `rfl`. Conclude with `huS (not_not.mp hv)`.

Take `⟨a1, a2⟩` from `hO κ ht`. Take `⟨b1, b2⟩` from `hO' κ ht`. Establish `h' : κ ∈ J'` using `b1.mpr (a1.mp hκ)`. Conclude with `⟨h', by rw [a2 hκ, b2 h']⟩`. Establish `key : ∀ T : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield L))), ∀ κ (hκ : κ ∈ J), TrivOutside (Sᶜ ∪ (T : Set _)) κ → ∃ h' : κ ∈ J', χ ⟨κ, hκ⟩ = χ' ⟨κ, h'⟩`.

Introduce `T`. Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty`. Introduce `κ hκ ht`. Establish `ht' : TrivOutside Sᶜ κ`.

Introduce `v hv`. Conclude with `ht v (by simpa using hv)`. Take `⟨a1, a2⟩` from `hO κ ht'`. Take `⟨b1, b2⟩` from `hO' κ ht'`. Establish `h' : κ ∈ J'` using `b1.mpr (a1.mp hκ)`.

Conclude with `⟨h', by rw [a2 hκ, b2 h']⟩`. Consider the case `insert u T huT ih`. Introduce `κ hκ ht`. Take `⟨κu, hκu, hu, hcomp⟩` from `hJ κ hκ u`. Establish `hκ1 : κ * κu⁻¹ ∈ J` using `J.mul_mem hκ (J.inv_mem hκu)`.

Establish `ht1 : TrivOutside (Sᶜ ∪ (T : Set _)) (κ * κu⁻¹)`. Introduce `v hv`. Rewrite using `[← compHom_eq_one_iff, map_mul, map_inv, mul_inv_eq_one]`. Distinguish the cases in `hvu : v = u`. Substitute `hvu` using the available equality.

Conclude with `((compHom_eq_iff v κ κu).mpr hcomp.symm)`. Establish `e1 : compHom v κ = 1`. Rewrite using `[compHom_eq_one_iff]`. Apply `ht v` to reduce the goal to its premises. Simplify using `only [Finset.coe_insert, Set.mem_union, Set.mem_insert_iff, not_or] at hv ⊢`.

Conclude with `⟨hv.1, hvu, hv.2⟩`. Establish `e2 : compHom v κu = 1`. Rewrite using `[compHom_eq_one_iff]`. Conclude with `hu v (by simpa using hvu)`. Rewrite using `[e1, e2]`.

Take `⟨h1', e1⟩` from `ih (κ * κu⁻¹) hκ1 ht1`. Take `⟨h2', e2⟩` from `hone u κu hu hκu`. Establish `hprod : κ = κ * κu⁻¹ * κu` using `by group`. Establish `h' : κ ∈ J'`. Rewrite using `[hprod]`.

Conclude with `J'.mul_mem h1' h2'`. Use `⟨h', ?_⟩` and prove the remaining obligations. Establish `s1 : (⟨κ, hκ⟩ : J) = ⟨κ * κu⁻¹, hκ1⟩ * ⟨κu, hκu⟩` using `Subtype.ext hprod`. Establish `s2 : (⟨κ, h'⟩ : J') = ⟨κ * κu⁻¹, h1'⟩ * ⟨κu, h2'⟩` using `Subtype.ext hprod`. Rewrite using `[s1, s2, map_mul, map_mul, e1, e2]`.

Apply `key hS.toFinset κ hκ` to reduce the goal to its premises. Introduce `v hv`. It suffices to derive a contradiction. Apply `hv` to reduce the goal to its premises. Distinguish the cases in `h : v ∈ S`.

Use `right`. Simplify using `using h`. Use `left`. Conclude with `h`.
-/
theorem mem_of_agree {J J' : Subgroup (GAf L n)} {χ : J →* ℂˣ} {χ' : J' →* ℂˣ}
    {S : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))} (hS : S.Finite) (hJ : NG.IsProdLevel J)
    (hO : NG.HypOutside J χ S) (hO' : NG.HypOutside J' χ' S)
    (hloc : ∀ u ∈ S, ∀ κ, TrivOutside {u} κ → (κ ∈ J ↔ κ ∈ J') ∧ ∀ (h : κ ∈ J) (h' : κ ∈ J'), χ ⟨κ, h⟩ = χ' ⟨κ, h'⟩)
    (κ : GAf L n) (hκ : κ ∈ J) : ∃ h' : κ ∈ J', χ ⟨κ, hκ⟩ = χ' ⟨κ, h'⟩ := by

  have hone : ∀ u κ, TrivOutside {u} κ → ∀ hκ : κ ∈ J, ∃ h' : κ ∈ J', χ ⟨κ, hκ⟩ = χ' ⟨κ, h'⟩ := by
    intro u κ hu hκ
    by_cases huS : u ∈ S
    · obtain ⟨h1, h2⟩ := hloc u huS κ hu
      exact ⟨h1.mp hκ, h2 hκ (h1.mp hκ)⟩
    · have ht : TrivOutside Sᶜ κ := by
        intro v hv
        apply hu v
        rintro rfl
        exact huS (not_not.mp hv)
      obtain ⟨a1, a2⟩ := hO κ ht
      obtain ⟨b1, b2⟩ := hO' κ ht
      have h' : κ ∈ J' := b1.mpr (a1.mp hκ)
      exact ⟨h', by rw [a2 hκ, b2 h']⟩
  have key : ∀ T : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield L))), ∀ κ (hκ : κ ∈ J),
      TrivOutside (Sᶜ ∪ (T : Set _)) κ → ∃ h' : κ ∈ J', χ ⟨κ, hκ⟩ = χ' ⟨κ, h'⟩ := by
    intro T
    classical
    induction T using Finset.induction_on with
    | empty =>
      intro κ hκ ht
      have ht' : TrivOutside Sᶜ κ := by
        intro v hv
        exact ht v (by simpa using hv)
      obtain ⟨a1, a2⟩ := hO κ ht'
      obtain ⟨b1, b2⟩ := hO' κ ht'
      have h' : κ ∈ J' := b1.mpr (a1.mp hκ)
      exact ⟨h', by rw [a2 hκ, b2 h']⟩
    | insert u T huT ih =>
      intro κ hκ ht
      obtain ⟨κu, hκu, hu, hcomp⟩ := hJ κ hκ u
      have hκ1 : κ * κu⁻¹ ∈ J := J.mul_mem hκ (J.inv_mem hκu)
      have ht1 : TrivOutside (Sᶜ ∪ (T : Set _)) (κ * κu⁻¹) := by
        intro v hv
        rw [← compHom_eq_one_iff, map_mul, map_inv, mul_inv_eq_one]
        by_cases hvu : v = u
        · subst hvu
          exact ((compHom_eq_iff v κ κu).mpr hcomp.symm)
        · have e1 : compHom v κ = 1 := by
            rw [compHom_eq_one_iff]
            apply ht v
            simp only [Finset.coe_insert, Set.mem_union, Set.mem_insert_iff, not_or] at hv ⊢
            exact ⟨hv.1, hvu, hv.2⟩
          have e2 : compHom v κu = 1 := by
            rw [compHom_eq_one_iff]
            exact hu v (by simpa using hvu)
          rw [e1, e2]
      obtain ⟨h1', e1⟩ := ih (κ * κu⁻¹) hκ1 ht1
      obtain ⟨h2', e2⟩ := hone u κu hu hκu
      have hprod : κ = κ * κu⁻¹ * κu := by group
      have h' : κ ∈ J' := by
        rw [hprod]; exact J'.mul_mem h1' h2'
      refine ⟨h', ?_⟩
      have s1 : (⟨κ, hκ⟩ : J) = ⟨κ * κu⁻¹, hκ1⟩ * ⟨κu, hκu⟩ := Subtype.ext hprod
      have s2 : (⟨κ, h'⟩ : J') = ⟨κ * κu⁻¹, h1'⟩ * ⟨κu, h2'⟩ := Subtype.ext hprod
      rw [s1, s2, map_mul, map_mul, e1, e2]
  apply key hS.toFinset κ hκ
  intro v hv
  exfalso
  apply hv
  by_cases h : v ∈ S
  · right; simpa using h
  · left; exact h

/- English proof (translation)
Introduce `L _ _ _ n J J' χ χ' S hS hJ hJ' hO hO' hloc`. Establish `hloc' : ∀ u ∈ S, ∀ κ, TrivOutside {u} κ → (κ ∈ J' ↔ κ ∈ J) ∧ ∀ (h : κ ∈ J') (h' : κ ∈ J), χ' ⟨κ, h⟩ = χ ⟨κ, h'⟩` using `fun u hu κ hκ => ⟨(hloc u hu κ hκ).1.symm, fun h h' => ((hloc u hu κ hκ).2 h' h).symm⟩`. Use `⟨le_antisymm (fun κ hκ => (mem_of_agree hS hJ hO hO' hloc κ hκ).1) (fun κ hκ => (mem_of_agree hS hJ' hO' hO hloc' κ hκ).1), fun κ h h' => ?_⟩` and prove the remaining obligations. Take `⟨h'', e⟩` from `mem_of_agree hS hJ hO hO' hloc κ h`. Conclude with `e`.
-/
theorem levEq_of_agree : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (J J' : Subgroup (GAf L n)) (χ : J →* ℂˣ) (χ' : J' →* ℂˣ) (S : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))), S.Finite → NG.IsProdLevel J → NG.IsProdLevel J' → NG.HypOutside J χ S → NG.HypOutside J' χ' S → (∀ u ∈ S, ∀ κ, TrivOutside {u} κ → (κ ∈ J ↔ κ ∈ J') ∧ ∀ (h : κ ∈ J) (h' : κ ∈ J'), χ ⟨κ, h⟩ = χ' ⟨κ, h'⟩) → LevEq J χ J' χ' := by
  intro L _ _ _ n J J' χ χ' S hS hJ hJ' hO hO' hloc
  have hloc' : ∀ u ∈ S, ∀ κ, TrivOutside {u} κ → (κ ∈ J' ↔ κ ∈ J) ∧ ∀ (h : κ ∈ J') (h' : κ ∈ J), χ' ⟨κ, h⟩ = χ ⟨κ, h'⟩ :=
    fun u hu κ hκ => ⟨(hloc u hu κ hκ).1.symm, fun h h' => ((hloc u hu κ hκ).2 h' h).symm⟩
  refine ⟨le_antisymm (fun κ hκ => (mem_of_agree hS hJ hO hO' hloc κ hκ).1)
    (fun κ hκ => (mem_of_agree hS hJ' hO' hO hloc' κ hκ).1), fun κ h h' => ?_⟩
  obtain ⟨h'', e⟩ := mem_of_agree hS hJ hO hO' hloc κ h
  exact e

end Glue

end GlobalTheory.LevCmp

end
