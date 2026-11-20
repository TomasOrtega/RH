import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernSum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.FinPart

open GlobalTheory.DefU.ClassFin

section Ring

variable {R S : Type} [CommRing R] [CommRing S] {n : ℕ}

def tw (n : ℕ) (c : R →+* R) : GL (Fin n) R →* GL (Fin n) R := (invT n R).comp (GeneralLinearGroup.map c)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem tw_inv_val (c : R →+* R) (g : GL (Fin n) R) : ((tw n c g)⁻¹).val = cT c g.val := rfl

/- English proof (translation)
Rewrite using `[← tw_inv_val, ← Units.val_mul, Units.val_eq_one, inv_mul_eq_one]`.
-/
theorem tw_eq_iff (c : R →+* R) (g : GL (Fin n) R) : tw n c g = g ↔ cT c g.val * g.val = 1 := by
  rw [← tw_inv_val, ← Units.val_mul, Units.val_eq_one, inv_mul_eq_one]

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Conclude with `h _`.
-/
theorem map_tw (p : R →+* S) (c : R →+* R) (d : S →+* S) (h : ∀ y, p (c y) = d (p y)) (g : GL (Fin n) R) :
    GeneralLinearGroup.map p (tw n c g) = tw n d (GeneralLinearGroup.map p g) := by
  apply Units.ext
  ext i j
  exact h _

end Ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def pU : finU E n →* GL (Fin n) (Af E) :=
  ((GeneralLinearGroup.map (pFin E)).comp (UA E n).subtype).comp (finU E n).subtype

/- English proof (translation)
The claim follows from `finGL_pFin k`.
-/
theorem finGL_pU (k : finU E n) : finGL E n (pU k) = k.1.1 := finGL_pFin k

/- English proof (translation)
Introduce `a b h` and use `Subtype.ext (Subtype.ext (by rw [← finGL_pU, h, finGL_pU]))`.
-/
theorem pU_injective : Function.Injective (pU (E := E) (n := n)) := fun a b h =>
  Subtype.ext (Subtype.ext (by rw [← finGL_pU, h, finGL_pU]))

/- English proof (translation)
The claim follows from `(tw_eq_iff _ _).2 (cT_pFin k.1)`.
-/
theorem tw_pU (k : finU E n) : tw n (conjFin (cc E)) (pU k) = pU k := (tw_eq_iff _ _).2 (cT_pFin k.1)

def sU (g : GL (Fin n) (Af E)) (h : tw n (conjFin (cc E)) g = g) : finU E n :=
  ⟨⟨finGL E n g, finGL_mem_UA _ ((tw_eq_iff _ _).1 h)⟩, pInf_finGL _⟩

/- English proof (translation)
The claim follows from `pFin_finGL g`.
-/
theorem pU_sU (g : GL (Fin n) (Af E)) (h : tw n (conjFin (cc E)) g = g) : pU (sU g h) = g := pFin_finGL g

/- English proof (translation)
The claim follows from `map_tw _ _ _ (fun y => (conjFin_algebraMap (cc E) y).symm) g`.
-/
theorem ratF_tw (g : GL (Fin n) E) :
    ratF E n (tw n (cc E).toRingHom g) = tw n (conjFin (cc E)) (ratF E n g) :=
  map_tw _ _ _ (fun y => (conjFin_algebraMap (cc E) y).symm) g

/- English proof (translation)
Rewrite using `[tw_eq_iff]`. Express the relevant statement in the definitionally equal form `cT _ g.val * 1 * g.val = 1 ↔ _`. Rewrite using `[mul_one]`.
-/
theorem mem_UE (g : GL (Fin n) E) : g ∈ UE E n ↔ tw n (cc E).toRingHom g = g := by
  rw [tw_eq_iff]
  change cT _ g.val * 1 * g.val = 1 ↔ _
  rw [mul_one]

/- English proof (translation)
Introduce `a b h` and use `by apply Units.ext ext i j obtain ⟨w⟩ : Nonempty (HeightOneSpectrum (𝓞 E)) := by obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 E) exact ⟨⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField E)⟩⟩ haveI : Nontrivial (Af E) := (pLoc E w).domain_nontrivi …`.
-/
theorem ratF_injective : Function.Injective (ratF E n) := fun a b h => by
  apply Units.ext
  ext i j
  obtain ⟨w⟩ : Nonempty (HeightOneSpectrum (𝓞 E)) := by
    obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 E)
    exact ⟨⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField E)⟩⟩
  haveI : Nontrivial (Af E) := (pLoc E w).domain_nontrivial
  have h' : (ratF E n a).val = (ratF E n b).val := congrArg Units.val h
  exact (algebraMap E (Af E)).injective (congrFun₂ h' i j)

/- English proof (translation)
Establish `h : tw n (conjFin (cc E)) (ratF E n γ.1) = ratF E n γ.1` using `by rw [← ratF_tw, (mem_UE _).1 γ.2]`. Establish `e : finPt γ = sU _ h`. Establish `h1 : toSub (UA E n) (finGL E n (ratF E n γ.1)) = (sU _ h).1` using `dif_pos (sU _ h).1.2`. Rewrite using `[finPt, h1]`. Conclude with `dif_pos (sU _ h).2`.

Rewrite using `[e, pU_sU]`.
-/
theorem pU_finPt (γ : UE E n) : pU (finPt γ) = ratF E n γ.1 := by
  have h : tw n (conjFin (cc E)) (ratF E n γ.1) = ratF E n γ.1 := by rw [← ratF_tw, (mem_UE _).1 γ.2]
  have e : finPt γ = sU _ h := by
    have h1 : toSub (UA E n) (finGL E n (ratF E n γ.1)) = (sU _ h).1 := dif_pos (sU _ h).1.2
    rw [finPt, h1]
    exact dif_pos (sU _ h).2
  rw [e, pU_sU]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨g, -, hg⟩`. Conclude with `⟨g, (pFin_finGL _).symm.trans (congrArg (GeneralLinearGroup.map (pFin E)) hg)⟩`. Introduce and unpack `⟨g, hg⟩`. Use `⟨g, (mem_UE g).2 (ratF_injective ?_), (congrArg (finGL E n) hg).trans (finGL_pU k)⟩` and prove the remaining obligations.

Rewrite using `[ratF_tw, hg, tw_pU]`.
-/
theorem mem_ratFinU (k : finU E n) : k ∈ ratFinU E n ↔ pU k ∈ (ratF E n).range := by
  constructor
  · rintro ⟨g, -, hg⟩
    exact ⟨g, (pFin_finGL _).symm.trans (congrArg (GeneralLinearGroup.map (pFin E)) hg)⟩
  · rintro ⟨g, hg⟩
    refine ⟨g, (mem_UE g).2 (ratF_injective ?_), (congrArg (finGL E n) hg).trans (finGL_pU k)⟩
    rw [ratF_tw, hg, tw_pU]

/- English proof (translation)
Introduce `E _ _ _ n`. Use `⟨fun a b => pU_injective ?_, fun a b h => Subtype.ext (ratF_injective ?_), fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, pU_finPt, pU_finPt, pU_finPt, Subgroup.coe_mul, map_mul]`. Rewrite using `[← pU_finPt, ← pU_finPt, h]`. Rewrite using `[mem_ratFinU]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨g, hg⟩`. Establish `hU : g ∈ UE E n` using `(mem_UE g).2 (ratF_injective (by rw [ratF_tw, hg, tw_pU]))`. Conclude with `⟨⟨g, hU⟩, pU_injective (by rw [pU_finPt, hg])⟩`. Introduce and unpack `⟨γ, rfl⟩`.

Conclude with `⟨γ.1, (pU_finPt γ).symm⟩`.
-/
theorem finPt_props : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), (∀ a b : UE E n, finPt (a * b) = finPt a * finPt b) ∧ Function.Injective (finPt : UE E n → finU E n) ∧ ∀ x : finU E n, x ∈ ratFinU E n ↔ ∃ γ : UE E n, finPt γ = x := by
  intro E _ _ _ n
  refine ⟨fun a b => pU_injective ?_, fun a b h => Subtype.ext (ratF_injective ?_), fun x => ?_⟩
  · rw [map_mul, pU_finPt, pU_finPt, pU_finPt, Subgroup.coe_mul, map_mul]
  · rw [← pU_finPt, ← pU_finPt, h]
  · rw [mem_ratFinU]
    constructor
    · rintro ⟨g, hg⟩
      have hU : g ∈ UE E n := (mem_UE g).2 (ratF_injective (by rw [ratF_tw, hg, tw_pU]))
      exact ⟨⟨g, hU⟩, pU_injective (by rw [pU_finPt, hg])⟩
    · rintro ⟨γ, rfl⟩
      exact ⟨γ.1, (pU_finPt γ).symm⟩

end GlobalTheory.BCT.FinPart
