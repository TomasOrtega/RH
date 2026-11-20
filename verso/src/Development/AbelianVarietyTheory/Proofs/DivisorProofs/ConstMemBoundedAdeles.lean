import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisZero
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.QhtUnip

noncomputable section
namespace GlobalTheory.ConstBdd

/- English proof (translation)
Use `set z := inclR (F := F) (AF F) e with hz`. Establish `hfin` using `Filter.eventually_cofinite.1 (eventually_absFin_le_one (E := E) F z)`. Use `haveI : ∀ w : InfinitePlace F, Fintype (EmbOver E w) := fun w => Fintype.ofFinite _`. Set `a : InfinitePlace F → ℝ≥0` to `fun w => Finset.univ.sup fun τ : EmbOver E w => ‖infEmb τ (compInf F E w z)‖₊`. Set `S : Finset (Pl F)` to `hfin.toFinset`.

Set `c : ℝ≥0` to `max 1 (max (S.sup fun v => absFin F v (compFin F E v z)) (Finset.univ.sup a))`. Use `⟨S, c, fun _ => ⟨fun v => ?_, fun w τ => ?_⟩⟩` and prove the remaining obligations. Use `split_ifs with hv`. Conclude with `(Finset.le_sup (f := fun v => absFin F v (compFin F E v z)) hv).trans (le_max_left _ _ |>.trans (le_max_right _ _))`. Assume the negation of the conclusion as `h`.

Conclude with `hv (hfin.mem_toFinset.2 h)`. Establish `h1 : ‖infEmb τ (compInf F E w z)‖₊ ≤ a w` using `Finset.le_sup (f := fun τ : EmbOver E w => ‖infEmb τ (compInf F E w z)‖₊) (Finset.mem_univ τ)`. Establish `h2 : a w ≤ Finset.univ.sup a` using `Finset.le_sup (Finset.mem_univ w)`. Conclude with `h1.trans (h2.trans ((le_max_right _ _).trans (le_max_right _ _)))`.
-/
theorem const_mem_Bdd (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (ι : Type)
    (e : E) : (fun _ : ι => inclR (F := F) (AF F) e) ∈ Bdd F E ι := by
  classical
  set z := inclR (F := F) (AF F) e with hz
  have hfin := Filter.eventually_cofinite.1 (eventually_absFin_le_one (E := E) F z)
  haveI : ∀ w : InfinitePlace F, Fintype (EmbOver E w) := fun w => Fintype.ofFinite _
  let a : InfinitePlace F → ℝ≥0 := fun w => Finset.univ.sup fun τ : EmbOver E w => ‖infEmb τ (compInf F E w z)‖₊
  let S : Finset (Pl F) := hfin.toFinset
  let c : ℝ≥0 := max 1 (max (S.sup fun v => absFin F v (compFin F E v z)) (Finset.univ.sup a))
  refine ⟨S, c, fun _ => ⟨fun v => ?_, fun w τ => ?_⟩⟩
  · split_ifs with hv
    · exact (Finset.le_sup (f := fun v => absFin F v (compFin F E v z)) hv).trans
        (le_max_left _ _ |>.trans (le_max_right _ _))
    · by_contra h
      exact hv (hfin.mem_toFinset.2 h)
  · have h1 : ‖infEmb τ (compInf F E w z)‖₊ ≤ a w :=
      Finset.le_sup (f := fun τ : EmbOver E w => ‖infEmb τ (compInf F E w z)‖₊) (Finset.mem_univ τ)
    have h2 : a w ≤ Finset.univ.sup a := Finset.le_sup (Finset.mem_univ w)
    exact h1.trans (h2.trans ((le_max_right _ _).trans (le_max_right _ _)))

end GlobalTheory.ConstBdd
