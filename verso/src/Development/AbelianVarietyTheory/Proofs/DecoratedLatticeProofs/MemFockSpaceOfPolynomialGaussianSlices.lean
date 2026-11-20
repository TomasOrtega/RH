import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUniqueAdelicMatrixRealComponentsFinitePartStatement
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn.FockSlice

/- English proof (translation)
Establish `hex : ∃ n, ∃ F : Finset I, Module.finrank K ((F.inf U : Submodule K V)) = n` using `⟨_, ∅, rfl⟩`. Take `⟨F, hF⟩` from `Nat.find_spec hex`. Use `⟨F, le_antisymm (le_iInf fun i => ?_) (Finset.le_inf fun i _ => iInf_le U i)⟩` and prove the remaining obligations. Establish `hle : (insert i F).inf U ≤ F.inf U` using `Finset.inf_mono (Finset.subset_insert i F)`. Establish `hmin : Nat.find hex ≤ Module.finrank K (((insert i F).inf U : Submodule K V))` using `Nat.find_min' hex ⟨_, rfl⟩`.

Establish `heq : (insert i F).inf U = F.inf U` using `Submodule.eq_of_le_of_finrank_le hle (by omega)`. Rewrite using `[← heq]`. Conclude with `Finset.inf_le (Finset.mem_insert_self i F)`.
-/
theorem exists_finset_inf_eq_iInf {K V I : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (U : I → Submodule K V) : ∃ F : Finset I, F.inf U = ⨅ i, U i := by
  classical
  have hex : ∃ n, ∃ F : Finset I, Module.finrank K ((F.inf U : Submodule K V)) = n := ⟨_, ∅, rfl⟩
  obtain ⟨F, hF⟩ := Nat.find_spec hex
  refine ⟨F, le_antisymm (le_iInf fun i => ?_) (Finset.le_inf fun i _ => iInf_le U i)⟩
  have hle : (insert i F).inf U ≤ F.inf U := Finset.inf_mono (Finset.subset_insert i F)
  have hmin : Nat.find hex ≤ Module.finrank K (((insert i F).inf U : Submodule K V)) := Nat.find_min' hex ⟨_, rfl⟩
  have heq : (insert i F).inf U = F.inf U := Submodule.eq_of_le_of_finrank_le hle (by omega)
  rw [← heq]
  exact Finset.inf_le (Finset.mem_insert_self i F)

/- English proof (translation)
Set `U : Y → Submodule ℂ W` to `fun y => LinearMap.ker ((LinearMap.proj y : (Y → ℂ) →ₗ[ℂ] ℂ).comp W.subtype)`. Take `⟨S, hS⟩` from `exists_finset_inf_eq_iInf U`. Set `R : W →ₗ[ℂ] (S → ℂ)` to `LinearMap.pi fun s => (LinearMap.proj (s : Y) : (Y → ℂ) →ₗ[ℂ] ℂ).comp W.subtype`. Establish `hR : LinearMap.ker R = ⊥`. Rewrite using `[LinearMap.ker_eq_bot']`.

Introduce `w hw`. Establish `hmem : w ∈ S.inf U`. Rewrite using `[Submodule.mem_finsetInf]`. Introduce `y hy`. Use `congrFun hw ⟨y, hy⟩` as an intermediate fact.

Simplify `this` using `[U, R]`. Rewrite `hmem` using `[hS, Submodule.mem_iInf]`. Use extensionality with `y`. Simplify `hmem y` using `[U]`. Take `⟨L, hL⟩` from `LinearMap.exists_leftInverse_of_injective R hR`.

Use `⟨S, fun y => if h : y ∈ S then (L (Pi.single ⟨y, h⟩ 1) : Y → ℂ) else 0, fun y => ?_, fun g hg => ?_⟩` and prove the remaining obligations. Distinguish the cases in `h : y ∈ S`. Simplify using `only [h, dite_true]`. Conclude with `(L _).2`. Simplify using `only [h, dite_false]`.

Conclude with `W.zero_mem`. Establish `h1 : (⟨g, hg⟩ : W) = L (R ⟨g, hg⟩)` using `by rw [← LinearMap.comp_apply, hL, LinearMap.id_apply]`. Establish `h2 : R ⟨g, hg⟩ = ∑ s : S, g s • (Pi.single s 1 : S → ℂ)`. Use extensionality with `t`. Simplify using `[R, Finset.sum_apply, Pi.single_apply]`.

Establish `h3` using `congrArg Subtype.val h1`. Rewrite `h3` using `[h2, map_sum]`. Simplify using `only [map_smul, Submodule.coe_sum, Submodule.coe_smul] at h3`. Use `h3.trans ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_coe_sort S]`.

Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Simplify using `[s.2]`.
-/
theorem exists_eval_recon {Y : Type} (W : Submodule ℂ (Y → ℂ)) [FiniteDimensional ℂ W] :
    ∃ (S : Finset Y) (g' : Y → Y → ℂ), (∀ y, g' y ∈ W) ∧ ∀ g ∈ W, g = ∑ y ∈ S, g y • g' y := by
  classical
  let U : Y → Submodule ℂ W := fun y => LinearMap.ker ((LinearMap.proj y : (Y → ℂ) →ₗ[ℂ] ℂ).comp W.subtype)
  obtain ⟨S, hS⟩ := exists_finset_inf_eq_iInf U
  let R : W →ₗ[ℂ] (S → ℂ) := LinearMap.pi fun s => (LinearMap.proj (s : Y) : (Y → ℂ) →ₗ[ℂ] ℂ).comp W.subtype
  have hR : LinearMap.ker R = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro w hw
    have hmem : w ∈ S.inf U := by
      rw [Submodule.mem_finsetInf]
      intro y hy
      have := congrFun hw ⟨y, hy⟩
      simpa [U, R] using this
    rw [hS, Submodule.mem_iInf] at hmem
    ext y
    simpa [U] using hmem y
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective R hR
  refine ⟨S, fun y => if h : y ∈ S then (L (Pi.single ⟨y, h⟩ 1) : Y → ℂ) else 0, fun y => ?_, fun g hg => ?_⟩
  · by_cases h : y ∈ S
    · simp only [h, dite_true]; exact (L _).2
    · simp only [h, dite_false]; exact W.zero_mem
  · have h1 : (⟨g, hg⟩ : W) = L (R ⟨g, hg⟩) := by rw [← LinearMap.comp_apply, hL, LinearMap.id_apply]
    have h2 : R ⟨g, hg⟩ = ∑ s : S, g s • (Pi.single s 1 : S → ℂ) := by
      ext t
      simp [R, Finset.sum_apply, Pi.single_apply]
    have h3 := congrArg Subtype.val h1
    rw [h2, map_sum] at h3
    simp only [map_smul, Submodule.coe_sum, Submodule.coe_smul] at h3
    refine h3.trans ?_
    rw [← Finset.sum_coe_sort S]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp [s.2]

end GlobalTheory.StdUnn.FockSlice

namespace GlobalTheory.StdUnn.FockSlice

/- English proof (translation)
Introduce `D θ hθ V n l s φ hφ hslice`. Take `⟨k, c, t, rfl⟩` from `Submodule.mem_span_set'.1 hφ`. Use `choose F G hG hFG using fun i => (t i).2`. Set `fin : Mx D V.rank n → (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E)` to `fun x i j => finPart D (x i j)`. Set `Pre : ((Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ) →ₗ[ℂ] (Mx D V.rank n → ℂ)` to `LinearMap.funLeft ℂ ℂ fin`.

Set `W : Submodule ℂ (Mx D V.rank n → ℂ)` to `Submodule.span ℂ (Set.range fun i => Pre (G i))`. Use `haveI : FiniteDimensional ℂ W := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)`. Take `⟨S, g', hg'W, hrec⟩` from `exists_eval_recon W`. Establish `hWle : W ≤ (WeilM.SB _).map Pre` using `Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact ⟨G i, hG i, rfl⟩)`. Use `choose g'' hg''SB hg''eq using fun y => hWle (hg'W y)`.

Use `choose pt hpt _ using fun x y : Mx D V.rank n => GlobalTheory.T.existsUnique_adelicMatrix_realComponents_finitePart D θ hθ V.rank n (fun τ => compAt θ τ x) y`. Use `choose p hp using hslice`. Use `set Φ : Mx D V.rank n → ℂ := ∑ i, c i • (t i : Mx D V.rank n → ℂ) with hΦ`. Establish `hΦx : ∀ x, Φ x = ∑ i, c i * (F i (fun τ a b => compAt θ τ x a b) * G i (fin x))`. Introduce `x`.

Simplify using `only [hΦ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hFG i]`. Establish `hpt' : ∀ x y, Φ (pt x y) = ∑ i, c i * (F i (fun τ a b => compAt θ τ x a b) * G i (fin y))`. Introduce `x y`.

Rewrite using `[hΦx]`. Establish `e1 : (fun τ a b => compAt θ τ (pt x y) a b) = (fun τ a b => compAt θ τ x a b)`. Use function extensionality and compare the values at `τ a b`. Rewrite using `[(hpt x y).1 τ]`. Establish `e2 : fin (pt x y) = fin y`.

Use function extensionality and compare the values at `a b`. Use `congrFun (congrFun (hpt x y).2 a) b` as an intermediate fact. Simplify `this` using `[fin, Matrix.map_apply]`. Rewrite using `[e1, e2]`. Establish `hG' : ∀ i x, G i (fin x) = ∑ y ∈ S, G i (fin y) * g' y x`.

Introduce `i x`. Use `congrFun (hrec (Pre (G i)) (Submodule.subset_span ⟨i, rfl⟩)) x` as an intermediate fact. Simplify `this` using `[Pre, LinearMap.funLeft_apply, Finset.sum_apply, smul_eq_mul]`. Establish `key : ∀ x, Φ x = ∑ y ∈ S, Φ (pt x y) * g' y x`. Introduce `x`.

Rewrite using `[hΦx]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hG' i x, Finset.mul_sum, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun y _ => by ring`. Use `_ = ∑ y ∈ S, ∑ i, c i * (F i (fun τ a b => compAt θ τ x a b) * G i (fin y)) * g' y x := Finset.sum_comm`.

Use `_ = ∑ y ∈ S, Φ (pt x y) * g' y x := Finset.sum_congr rfl fun y _ => by rw [hpt', Finset.sum_mul]`. Establish `hfin : ∀ x y, (pt x y).map (finPart D) = y.map (finPart D)` using `fun x y => (hpt x y).2`. Establish `hcomp : ∀ x y, (fun τ => compAt θ τ (pt x y)) = (fun τ => compAt θ τ x)` using `fun x y => funext (hpt x y).1`. Establish `hEq : Φ = ∑ y ∈ S, (fun x => evalPoly (p y) (fun τ => compAt θ τ x) * gauss V l s (fun τ => compAt θ τ x) * g'' y (fun i j => finPart D (x i j)))`. Use function extensionality and compare the values at `x`.

Rewrite using `[key x, Finset.sum_apply]`. Use `Finset.sum_congr rfl fun y _ => ?_` and prove the remaining obligations. Rewrite using `[hp y (pt x y) (hfin x y), hcomp x y]`. Use `congr 1`. Rewrite using `[← hg''eq y]`.

Both sides reduce to the same expression. Rewrite using `[hEq]`. Conclude with `Submodule.sum_mem _ fun y _ => Submodule.subset_span ⟨p y, g'' y, hg''SB y, rfl⟩`.
-/
theorem mem_fockA_of_slices : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (n : ℕ) (l : D.what₂.Tau → ℝ) (s : RealMat V), ∀ φ ∈ schwartzA θ V.rank n, (∀ x₀ : Mx D V.rank n, ∃ p : MvPolynomial (D.what₂.Tau × Fin V.rank × Fin n × Bool) ℂ, ∀ x : Mx D V.rank n, x.map (finPart D) = x₀.map (finPart D) → φ x = evalPoly p (fun τ => compAt θ τ x) * gauss V l s (fun τ => compAt θ τ x)) → φ ∈ fockA θ V n l s := by
  intro D θ hθ V n l s φ hφ hslice
  classical
  obtain ⟨k, c, t, rfl⟩ := Submodule.mem_span_set'.1 hφ
  choose F G hG hFG using fun i => (t i).2
  let fin : Mx D V.rank n → (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) :=
    fun x i j => finPart D (x i j)
  let Pre : ((Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ) →ₗ[ℂ] (Mx D V.rank n → ℂ) :=
    LinearMap.funLeft ℂ ℂ fin
  let W : Submodule ℂ (Mx D V.rank n → ℂ) := Submodule.span ℂ (Set.range fun i => Pre (G i))
  haveI : FiniteDimensional ℂ W := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  obtain ⟨S, g', hg'W, hrec⟩ := exists_eval_recon W
  have hWle : W ≤ (WeilM.SB _).map Pre := Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact ⟨G i, hG i, rfl⟩)
  choose g'' hg''SB hg''eq using fun y => hWle (hg'W y)
  choose pt hpt _ using fun x y : Mx D V.rank n => GlobalTheory.T.existsUnique_adelicMatrix_realComponents_finitePart D θ hθ V.rank n (fun τ => compAt θ τ x) y
  choose p hp using hslice
  set Φ : Mx D V.rank n → ℂ := ∑ i, c i • (t i : Mx D V.rank n → ℂ) with hΦ
  have hΦx : ∀ x, Φ x = ∑ i, c i * (F i (fun τ a b => compAt θ τ x a b) * G i (fin x)) := by
    intro x
    simp only [hΦ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hFG i]
  have hpt' : ∀ x y, Φ (pt x y) = ∑ i, c i * (F i (fun τ a b => compAt θ τ x a b) * G i (fin y)) := by
    intro x y
    rw [hΦx]
    have e1 : (fun τ a b => compAt θ τ (pt x y) a b) = (fun τ a b => compAt θ τ x a b) := by
      funext τ a b; rw [(hpt x y).1 τ]
    have e2 : fin (pt x y) = fin y := by
      funext a b
      have := congrFun (congrFun (hpt x y).2 a) b
      simpa [fin, Matrix.map_apply] using this
    rw [e1, e2]
  have hG' : ∀ i x, G i (fin x) = ∑ y ∈ S, G i (fin y) * g' y x := by
    intro i x
    have := congrFun (hrec (Pre (G i)) (Submodule.subset_span ⟨i, rfl⟩)) x
    simpa [Pre, LinearMap.funLeft_apply, Finset.sum_apply, smul_eq_mul] using this
  have key : ∀ x, Φ x = ∑ y ∈ S, Φ (pt x y) * g' y x := by
    intro x
    rw [hΦx]
    calc ∑ i, c i * (F i (fun τ a b => compAt θ τ x a b) * G i (fin x))
        = ∑ i, ∑ y ∈ S, c i * (F i (fun τ a b => compAt θ τ x a b) * G i (fin y)) * g' y x :=
          Finset.sum_congr rfl fun i _ => by
            rw [hG' i x, Finset.mul_sum, Finset.mul_sum]
            exact Finset.sum_congr rfl fun y _ => by ring
      _ = ∑ y ∈ S, ∑ i, c i * (F i (fun τ a b => compAt θ τ x a b) * G i (fin y)) * g' y x := Finset.sum_comm
      _ = ∑ y ∈ S, Φ (pt x y) * g' y x := Finset.sum_congr rfl fun y _ => by rw [hpt', Finset.sum_mul]
  have hfin : ∀ x y, (pt x y).map (finPart D) = y.map (finPart D) := fun x y => (hpt x y).2
  have hcomp : ∀ x y, (fun τ => compAt θ τ (pt x y)) = (fun τ => compAt θ τ x) := fun x y => funext (hpt x y).1
  have hEq : Φ = ∑ y ∈ S, (fun x => evalPoly (p y) (fun τ => compAt θ τ x) * gauss V l s (fun τ => compAt θ τ x) *
      g'' y (fun i j => finPart D (x i j))) := by
    funext x
    rw [key x, Finset.sum_apply]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [hp y (pt x y) (hfin x y), hcomp x y]
    congr 1
    rw [← hg''eq y]
    rfl
  rw [hEq]
  exact Submodule.sum_mem _ fun y _ => Submodule.subset_span ⟨p y, g'' y, hg''SB y, rfl⟩

end GlobalTheory.StdUnn.FockSlice
