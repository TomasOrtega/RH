import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ExponentSeparation
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S

namespace GlobalTheory.TrUnion

/- English proof (translation)
Introduce `G _ _ m W _ _ σ i₀`. Set `R : Fin m → Fin m → Prop` to `fun i j => Nonempty ((σ i).Equiv (σ j))`. Establish `hrefl : ∀ i, R i i` using `fun i => ⟨Representation.Equiv.refl _⟩`. Establish `hsymm : ∀ {i j}, R i j → R j i` using `fun ⟨e⟩ => ⟨e.symm⟩`. Establish `htrans : ∀ {i j k}, R i j → R j k → R i k` using `fun ⟨e⟩ ⟨e'⟩ => ⟨e.trans e'⟩`.

Set `S : Setoid (Fin m)` to `⟨R, ⟨hrefl, hsymm, htrans⟩⟩`. Set `f : Fin m → Fin m` to `fun i => if R i i₀ then i₀ else (Quotient.mk S i).out`. Establish `hf : ∀ i, R (f i) i`. Introduce `i`. Distinguish the cases in `h : R i i₀`.

Simplify using `only [f, if_pos h]`. Conclude with `hsymm h`. Simplify using `only [f, if_neg h]`. Conclude with `Quotient.mk_out (s := S) i`. Establish `hfc : ∀ i j, R i j → f i = f j`.

Introduce `i j hij`. Distinguish the cases in `h : R i i₀`. Establish `h' : R j i₀` using `htrans (hsymm hij) h`. Simplify using `only [f, if_pos h, if_pos h']`. Establish `h' : ¬ R j i₀` using `fun h' => h (htrans hij h')`.

Simplify using `only [f, if_neg h, if_neg h']`. Rewrite using `[Quotient.sound (s := S) hij]`. Set `T : Finset (Fin m)` to `Finset.univ.image f`. Set `e : T ≃ Fin T.card` to `T.equivFin`. Use `⟨T.card, fun k => (e.symm k).1, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `k l hkl`. Use `⟨fun hR => ?_⟩` and prove the remaining obligations. Apply `hkl` to reduce the goal to its premises. Take `⟨x, -, hx⟩` from `Finset.mem_image.1 (e.symm k).2`. Take `⟨y, -, hy⟩` from `Finset.mem_image.1 (e.symm l).2`.

Establish `hxy : R x y`. Establish `h1 : R (f x) (f y)` using `by rw [hx, hy]; exact ⟨hR⟩`. Conclude with `htrans (hsymm (hf x)) (htrans h1 (hf y))`. Establish `: (e.symm k).1 = (e.symm l).1` using `by rw [← hx, ← hy]; exact hfc x y hxy`. Conclude with `e.symm.injective (Subtype.ext this)`.

Establish `hmem : i₀ ∈ T` using `Finset.mem_image.2 ⟨i₀, Finset.mem_univ _, by simp only [f, if_pos (hrefl i₀)]⟩`. Conclude with `⟨e ⟨i₀, hmem⟩, by simp⟩`. Introduce `i`. Establish `hmem : f i ∈ T` using `Finset.mem_image_of_mem f (Finset.mem_univ i)`. Use `⟨e ⟨f i, hmem⟩, ?_⟩` and prove the remaining obligations.

Use `show R i (e.symm (e ⟨f i, hmem⟩)).1`. Rewrite using `[Equiv.symm_apply_apply]`. Conclude with `hsymm (hf i)`.
-/
theorem exists_reps_through : ∀ (G : Type) [Group G] [TopologicalSpace G] (m : ℕ) (W : Fin m → Type) [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)] (σ : ∀ i, Representation ℂ G (W i)), ∀ i₀ : Fin m, ∃ (n : ℕ) (s : Fin n → Fin m), (∀ i j, i ≠ j → IsEmpty ((σ (s i)).Equiv (σ (s j)))) ∧ (∃ j, s j = i₀) ∧ ∀ i, ∃ j, Nonempty ((σ i).Equiv (σ (s j))) := by
  intro G _ _ m W _ _ σ i₀
  classical
  let R : Fin m → Fin m → Prop := fun i j => Nonempty ((σ i).Equiv (σ j))
  have hrefl : ∀ i, R i i := fun i => ⟨Representation.Equiv.refl _⟩
  have hsymm : ∀ {i j}, R i j → R j i := fun ⟨e⟩ => ⟨e.symm⟩
  have htrans : ∀ {i j k}, R i j → R j k → R i k := fun ⟨e⟩ ⟨e'⟩ => ⟨e.trans e'⟩
  let S : Setoid (Fin m) := ⟨R, ⟨hrefl, hsymm, htrans⟩⟩
  let f : Fin m → Fin m := fun i => if R i i₀ then i₀ else (Quotient.mk S i).out
  have hf : ∀ i, R (f i) i := by
    intro i
    by_cases h : R i i₀
    · simp only [f, if_pos h]; exact hsymm h
    · simp only [f, if_neg h]; exact Quotient.mk_out (s := S) i
  have hfc : ∀ i j, R i j → f i = f j := by
    intro i j hij
    by_cases h : R i i₀
    · have h' : R j i₀ := htrans (hsymm hij) h
      simp only [f, if_pos h, if_pos h']
    · have h' : ¬ R j i₀ := fun h' => h (htrans hij h')
      simp only [f, if_neg h, if_neg h']
      rw [Quotient.sound (s := S) hij]
  let T : Finset (Fin m) := Finset.univ.image f
  let e : T ≃ Fin T.card := T.equivFin
  refine ⟨T.card, fun k => (e.symm k).1, ?_, ?_, ?_⟩
  · intro k l hkl
    refine ⟨fun hR => ?_⟩
    apply hkl
    obtain ⟨x, -, hx⟩ := Finset.mem_image.1 (e.symm k).2
    obtain ⟨y, -, hy⟩ := Finset.mem_image.1 (e.symm l).2
    have hxy : R x y := by
      have h1 : R (f x) (f y) := by rw [hx, hy]; exact ⟨hR⟩
      exact htrans (hsymm (hf x)) (htrans h1 (hf y))
    have : (e.symm k).1 = (e.symm l).1 := by rw [← hx, ← hy]; exact hfc x y hxy
    exact e.symm.injective (Subtype.ext this)
  · have hmem : i₀ ∈ T := Finset.mem_image.2 ⟨i₀, Finset.mem_univ _, by simp only [f, if_pos (hrefl i₀)]⟩
    exact ⟨e ⟨i₀, hmem⟩, by simp⟩
  · intro i
    have hmem : f i ∈ T := Finset.mem_image_of_mem f (Finset.mem_univ i)
    refine ⟨e ⟨f i, hmem⟩, ?_⟩
    show R i (e.symm (e ⟨f i, hmem⟩)).1
    rw [Equiv.symm_apply_apply]
    exact hsymm (hf i)

end GlobalTheory.TrUnion
