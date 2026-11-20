import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHolRepOfIsTau
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemUJsetOfKset
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOperatorLowestWeightHolomorphicKTypeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeLeSmoothVectorsStatement

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.JointHarm.MultiOp

section Alg

variable {ι : Type} [Fintype ι] {R : Type} [Ring R] [Algebra ℂ R] {L : ι → Type} [∀ i, AddCommGroup (L i)]
  [∀ i, Module ℂ (L i)]

omit [Fintype ι] in
/- English proof (translation)
Introduce `i _ j _ hij`. Conclude with `hU i j hij (v i) (v j)`.
-/
theorem pw (U : ∀ i, L i →ₗ[ℂ] R) (hU : ∀ i j, i ≠ j → ∀ a b, Commute (U i a) (U j b))
    (v : ∀ i, L i) (s : Finset ι) : (s : Set ι).Pairwise (Function.onFun Commute fun j => U j (v j)) := by
  intro i _ j _ hij
  exact hU i j hij (v i) (v j)

/- English proof (translation)
Rewrite using `[← Finset.noncommProd_erase_mul Finset.univ (Finset.mem_univ i)]`. Use `congr 1`. Apply `Finset.noncommProd_congr rfl` to reduce the goal to its premises. Introduce `j hj`. Rewrite using `[Function.update_of_ne (Finset.ne_of_mem_erase hj)]`.

Rewrite using `[Function.update_self]`.
-/
theorem prod_update (U : ∀ i, L i →ₗ[ℂ] R) (hU : ∀ i j, i ≠ j → ∀ a b, Commute (U i a) (U j b))
    (v : ∀ i, L i) (i : ι) (u : L i) :
    Finset.univ.noncommProd (fun j => U j (Function.update v i u j)) (pw U hU _ _) =
      (Finset.univ.erase i).noncommProd (fun j => U j (v j)) (pw U hU _ _) * U i u := by
  rw [← Finset.noncommProd_erase_mul Finset.univ (Finset.mem_univ i)]
  congr 1
  · apply Finset.noncommProd_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  · rw [Function.update_self]

/- English proof (translation)
Use `⟨PiTensorProduct.lift { toFun := fun v => Finset.univ.noncommProd (fun j => U j (v j)) (pw U hU _ _) map_update_add' := ?_ map_update_smul' := ?_ }, fun v => ?_⟩` and prove the remaining obligations. Introduce `inst v i x y`. Take `rfl : inst = (fun a b => Classical.propDecidable (a = b))` from `Subsingleton.elim _ _`. Simplify using `only [prod_update U hU, map_add, mul_add]`. Introduce `inst v i c x`.

Take `rfl : inst = (fun a b => Classical.propDecidable (a = b))` from `Subsingleton.elim _ _`. Simplify using `only [prod_update U hU, map_smul, mul_smul_comm]`. Rewrite using `[PiTensorProduct.lift.tprod]`. Both sides reduce to the same expression.
-/
theorem exists_multi (U : ∀ i, L i →ₗ[ℂ] R) (hU : ∀ i j, i ≠ j → ∀ a b, Commute (U i a) (U j b)) :
    ∃ m : (⨂[ℂ] i, L i) →ₗ[ℂ] R, ∀ v, m (PiTensorProduct.tprod ℂ v) =
      Finset.univ.noncommProd (fun j => U j (v j)) (pw U hU _ _) := by
  refine ⟨PiTensorProduct.lift
    { toFun := fun v => Finset.univ.noncommProd (fun j => U j (v j)) (pw U hU _ _)
      map_update_add' := ?_
      map_update_smul' := ?_ }, fun v => ?_⟩
  · intro inst v i x y
    obtain rfl : inst = (fun a b => Classical.propDecidable (a = b)) := Subsingleton.elim _ _
    simp only [prod_update U hU, map_add, mul_add]
  · intro inst v i c x
    obtain rfl : inst = (fun a b => Classical.propDecidable (a = b)) := Subsingleton.elim _ _
    simp only [prod_update U hU, map_smul, mul_smul_comm]
  · rw [PiTensorProduct.lift.tprod]
    rfl

end Alg

section Grp

variable {n : ℕ}

/- English proof (translation)
Take `⟨hu, hc⟩` from `hk`. Establish `hJ : (Formalism.REAL.Jm ε).map star = Formalism.REAL.Jm ε`. Use extensionality with `a b`. Simplify using `only [Formalism.REAL.Jm, Matrix.map_apply, Matrix.diagonal_apply]`. Apply the tactic sequence `split_ifs <;> simp`.

Establish `e : ∀ M : Matrix (Fin n) (Fin n) ℂ, M.map star = M.map (starRingEnd ℂ)` using `fun M => rfl`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite `hu`, the goal using `[Matrix.mem_unitaryGroup_iff]`. Use extensionality with `i j`. Establish `h2` using `congrArg star (congrFun (congrFun hu i) j)`.

Simplify using `only [Matrix.mul_apply, Matrix.star_apply, Matrix.map_apply, star_sum, star_mul', star_star, Matrix.one_apply] at h2 ⊢`. Rewrite using `[h2]`. Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[← hJ]`. Simplify using `only [e]`.

Rewrite using `[← Matrix.map_mul, ← Matrix.map_mul, hc]`.
-/
theorem conj_mem {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Formalism.REAL.Kset ε) :
    k.map star ∈ Formalism.REAL.Kset ε := by
  obtain ⟨hu, hc⟩ := hk
  have hJ : (Formalism.REAL.Jm ε).map star = Formalism.REAL.Jm ε := by
    ext a b
    simp only [Formalism.REAL.Jm, Matrix.map_apply, Matrix.diagonal_apply]
    split_ifs <;> simp
  have e : ∀ M : Matrix (Fin n) (Fin n) ℂ, M.map star = M.map (starRingEnd ℂ) := fun M => rfl
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff] at hu ⊢
    ext i j
    have h2 := congrArg star (congrFun (congrFun hu i) j)
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.map_apply, star_sum, star_mul', star_star,
      Matrix.one_apply] at h2 ⊢
    rw [h2]
    split_ifs <;> simp
  · rw [← hJ]
    simp only [e]
    rw [← Matrix.map_mul, ← Matrix.map_mul, hc]

/- English proof (translation)
Take `⟨hu, hc⟩` from `hk`. Conclude with `⟨⟨Unitary.toUnits ⟨k, hu⟩, rfl⟩, hc⟩`.
-/
theorem mem_KC {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Formalism.REAL.Kset ε) :
    k ∈ GlobalTheory.Dec.KC ε := by
  obtain ⟨hu, hc⟩ := hk
  exact ⟨⟨Unitary.toUnits ⟨k, hu⟩, rfl⟩, hc⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨one_mem _, by simp⟩`.
-/
theorem one_mem_K {ε : Fin n → Bool} : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ Formalism.REAL.Kset ε := ⟨one_mem _, by simp⟩

variable {ι : Type} {P : Type} [AddCommGroup P] [Module ℂ P] {ε : ι → Fin n → Bool}

/- English proof (translation)
Distinguish the cases in `h : ρ = τ`. Substitute `h` using the available equality. Simplify using `using hk`. Rewrite using `[Pi.mulSingle_eq_of_ne h]`. Conclude with `one_mem_K`.
-/
theorem single_mem {τ : ι} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Formalism.REAL.Kset (ε τ)) (ρ : ι) :
    (Pi.mulSingle τ k : ι → Matrix (Fin n) (Fin n) ℂ) ρ ∈ Formalism.REAL.Kset (ε ρ) := by
  by_cases h : ρ = τ
  · subst h
    simpa using hk
  · rw [Pi.mulSingle_eq_of_ne h]
    exact one_mem_K

/- English proof (translation)
Proceed by induction on `hX using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨g, hg, rfl⟩` from `hx`. Conclude with `hA g hg`. Consider the case `zero => exact Commute.zero_right A`.

Consider the case `add x y _ _ hx hy => exact hx.add_right hy`. Consider the case `smul c x _ hx => exact hx.smul_right c`.
-/
theorem commute_span {ϖ : (ι → Matrix (Fin n) (Fin n) ℂ) → Module.End ℂ P} {τ : ι} {A X : Module.End ℂ P}
    (hA : ∀ k ∈ Formalism.REAL.Kset (ε τ), Commute A (ϖ (Pi.mulSingle τ k)))
    (hX : X ∈ Submodule.span ℂ ((fun g => ϖ (Pi.mulSingle τ g)) '' Formalism.REAL.Kset (ε τ))) : Commute A X := by
  induction hX using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, hg, rfl⟩ := hx
    exact hA g hg
  | zero => exact Commute.zero_right A
  | add x y _ _ hx hy => exact hx.add_right hy
  | smul c x _ hx => exact hx.smul_right c

/- English proof (translation)
Use `commute_span (fun k hk => ?_) hX` and prove the remaining obligations. Establish `hs : ∀ ρ, (Pi.mulSingle τ k : ι → Matrix (Fin n) (Fin n) ℂ) ρ ∈ GlobalTheory.Dec.KC (ε ρ)` using `fun ρ => mem_KC (single_mem hk ρ)`. Establish `hg' : ∀ ρ, g ρ ∈ GlobalTheory.Dec.KC (ε ρ)` using `fun ρ => mem_KC (hg ρ)`. Establish `hcomm : g * Pi.mulSingle τ k = Pi.mulSingle τ k * g`. Use function extensionality and compare the values at `ρ`.

Distinguish the cases in `hρ : ρ = τ`. Substitute `hρ` using the available equality. Simplify using `[h1]`. Simplify using `[Pi.mulSingle_eq_of_ne hρ]`. Use `show ϖ g * ϖ (Pi.mulSingle τ k) = ϖ (Pi.mulSingle τ k) * ϖ g`.

Rewrite using `[← h.2.2.1 _ _ hg' hs, ← h.2.2.1 _ _ hs hg', hcomm]`.
-/
theorem commute_away {B : P →ₗ⋆[ℂ] P →ₗ[ℂ] ℂ} {ϖ : (ι → Matrix (Fin n) (Fin n) ℂ) → Module.End ℂ P}
    (h : IsHolFam ε B ϖ) {τ : ι} {g : ι → Matrix (Fin n) (Fin n) ℂ} (hg : ∀ ρ, g ρ ∈ Formalism.REAL.Kset (ε ρ))
    (h1 : g τ = 1) {X : Module.End ℂ P}
    (hX : X ∈ Submodule.span ℂ ((fun g => ϖ (Pi.mulSingle τ g)) '' Formalism.REAL.Kset (ε τ))) :
    Commute (ϖ g) X := by
  refine commute_span (fun k hk => ?_) hX
  have hs : ∀ ρ, (Pi.mulSingle τ k : ι → Matrix (Fin n) (Fin n) ℂ) ρ ∈ GlobalTheory.Dec.KC (ε ρ) := fun ρ => mem_KC (single_mem hk ρ)
  have hg' : ∀ ρ, g ρ ∈ GlobalTheory.Dec.KC (ε ρ) := fun ρ => mem_KC (hg ρ)
  have hcomm : g * Pi.mulSingle τ k = Pi.mulSingle τ k * g := by
    funext ρ
    by_cases hρ : ρ = τ
    · subst hρ
      simp [h1]
    · simp [Pi.mulSingle_eq_of_ne hρ]
  show ϖ g * ϖ (Pi.mulSingle τ k) = ϖ (Pi.mulSingle τ k) * ϖ g
  rw [← h.2.2.1 _ _ hg' hs, ← h.2.2.1 _ _ hs hg', hcomm]

/- English proof (translation)
Establish `hUU : ∀ i j, i ≠ j → ∀ a b, Commute (U i a) (U j b)`. Introduce `i j hij a b`. Use `commute_span (τ := j) (fun k hk => ?_) (hU j b)` and prove the remaining obligations. Conclude with `(commute_away h (fun ρ => single_mem hk ρ) (by rw [Pi.mulSingle_eq_of_ne hij]) (hU i a)).symm`. Take `⟨m, hm⟩` from `exists_multi U hUU`.

Use `⟨m, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `A hA x`. Establish `hAU : ∀ i a, Commute A (U i a)` using `fun i a => commute_span (fun k hk => hA _ (fun ρ => single_mem hk ρ)) (hU i a)`. Proceed by induction on `x using PiTensorProduct.induction_on with`. Consider the case `smul_tprod r v`.

Rewrite using `[map_smul, hm]`. Conclude with `(Finset.noncommProd_commute _ _ _ _ (fun j _ => hAU j (v j))).smul_right r`. Consider the case `add x y hx hy`. Rewrite using `[map_add]`. Conclude with `hx.add_right hy`.

Introduce `g hg v y hv`. Establish `key : ∀ s : Finset ι, (s.noncommProd (fun j => U j (v j)) (pw U hUU v s)) y = ϖ (fun τ => if τ ∈ s then g τ else 1) y`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`.

Establish `e1 : (fun τ : ι => if τ ∈ (∅ : Finset ι) then g τ else 1) = 1`. Use function extensionality and compare the values at `τ`. Simplify using the standard rewrite rules. Rewrite using `[e1, h.2.1, Finset.noncommProd_empty]`. Consider the case `insert a s ha ih`.

Establish `hgs : ∀ ρ, (if ρ ∈ s then g ρ else 1) ∈ Formalism.REAL.Kset (ε ρ)` using `fun ρ => by split_ifs exacts [hg ρ, one_mem_K]`. Establish `hc` using `commute_away h hgs (by simp [ha]) (hU a (v a))`. Rewrite using `[Finset.noncommProd_insert_of_notMem _ _ _ _ ha, Module.End.mul_apply, ih, ← Module.End.mul_apply, ← hc.eq, Module.End.mul_apply, hv a, ← Module.End.mul_apply, ← h.2.2.1 _ _ (fun ρ => mem_KC (hgs ρ)) (fun ρ => mem_KC (single_mem (hg a) ρ))]`. Use `congr 2`. Use function extensionality and compare the values at `ρ`.

Distinguish the cases in `hρ : ρ = a`. Substitute `hρ` using the available equality. Simplify using `[ha]`. Simplify using `[Finset.mem_insert, hρ]`. Use `key Finset.univ` as an intermediate fact.

Simplify `this` using `[hm]`. Introduce `y τ k hk v u huv`. Establish `e2` using `prod_update U hUU v τ (v τ)`. Simplify using `only [Function.update_eq_self] at e2`. Rewrite using `[hm, hm, prod_update U hUU v τ u, e2]`.

Establish `hc : Commute (ϖ (Pi.mulSingle τ k)) ((Finset.univ.erase τ).noncommProd (fun j => U j (v j)) (pw U hUU _ _))` using `Finset.noncommProd_commute _ _ _ _ (fun j hj => commute_away h (fun ρ => single_mem hk ρ) (by rw [Pi.mulSingle_eq_of_ne (Finset.ne_of_mem_erase hj)]) (hU j (v j)))`. Rewrite using `[Module.End.mul_apply, Module.End.mul_apply, huv, ← Module.End.mul_apply, ← hc.eq, Module.End.mul_apply]`.
-/
theorem core [Fintype ι] {B : P →ₗ⋆[ℂ] P →ₗ[ℂ] ℂ} {ϖ : (ι → Matrix (Fin n) (Fin n) ℂ) → Module.End ℂ P}
    (h : IsHolFam ε B ϖ) {L : ι → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℂ (L i)]
    (U : ∀ i, L i →ₗ[ℂ] Module.End ℂ P)
    (hU : ∀ i a, U i a ∈ Submodule.span ℂ ((fun g => ϖ (Pi.mulSingle i g)) '' Formalism.REAL.Kset (ε i))) :
    ∃ m : (⨂[ℂ] i, L i) →ₗ[ℂ] Module.End ℂ P,
      (∀ A : Module.End ℂ P, (∀ k, (∀ τ, k τ ∈ Formalism.REAL.Kset (ε τ)) → Commute A (ϖ k)) → ∀ x, Commute A (m x)) ∧
      (∀ g : ι → Matrix (Fin n) (Fin n) ℂ, (∀ τ, g τ ∈ Formalism.REAL.Kset (ε τ)) → ∀ (v : ∀ i, L i) (y : P),
        (∀ τ, U τ (v τ) y = ϖ (Pi.mulSingle τ (g τ)) y) → m (PiTensorProduct.tprod ℂ v) y = ϖ g y) ∧
      ∀ (y : P) (τ : ι), ∀ k ∈ Formalism.REAL.Kset (ε τ), ∀ (v : ∀ i, L i) (u : L τ),
        U τ u y = ϖ (Pi.mulSingle τ k) (U τ (v τ) y) →
        m (PiTensorProduct.tprod ℂ (Function.update v τ u)) y =
          ϖ (Pi.mulSingle τ k) (m (PiTensorProduct.tprod ℂ v) y) := by
  have hUU : ∀ i j, i ≠ j → ∀ a b, Commute (U i a) (U j b) := by
    intro i j hij a b
    refine commute_span (τ := j) (fun k hk => ?_) (hU j b)
    exact (commute_away h (fun ρ => single_mem hk ρ) (by rw [Pi.mulSingle_eq_of_ne hij]) (hU i a)).symm
  obtain ⟨m, hm⟩ := exists_multi U hUU
  refine ⟨m, ?_, ?_, ?_⟩
  · intro A hA x
    have hAU : ∀ i a, Commute A (U i a) := fun i a =>
      commute_span (fun k hk => hA _ (fun ρ => single_mem hk ρ)) (hU i a)
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      rw [map_smul, hm]
      exact (Finset.noncommProd_commute _ _ _ _ (fun j _ => hAU j (v j))).smul_right r
    | add x y hx hy =>
      rw [map_add]
      exact hx.add_right hy
  · intro g hg v y hv
    have key : ∀ s : Finset ι, (s.noncommProd (fun j => U j (v j)) (pw U hUU v s)) y =
        ϖ (fun τ => if τ ∈ s then g τ else 1) y := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        have e1 : (fun τ : ι => if τ ∈ (∅ : Finset ι) then g τ else 1) = 1 := by
          funext τ
          simp
        rw [e1, h.2.1, Finset.noncommProd_empty]
      | insert a s ha ih =>
        have hgs : ∀ ρ, (if ρ ∈ s then g ρ else 1) ∈ Formalism.REAL.Kset (ε ρ) := fun ρ => by
          split_ifs
          exacts [hg ρ, one_mem_K]
        have hc := commute_away h hgs (by simp [ha]) (hU a (v a))
        rw [Finset.noncommProd_insert_of_notMem _ _ _ _ ha, Module.End.mul_apply, ih,
          ← Module.End.mul_apply, ← hc.eq, Module.End.mul_apply, hv a, ← Module.End.mul_apply,
          ← h.2.2.1 _ _ (fun ρ => mem_KC (hgs ρ)) (fun ρ => mem_KC (single_mem (hg a) ρ))]
        congr 2
        funext ρ
        by_cases hρ : ρ = a
        · subst hρ
          simp [ha]
        · simp [Finset.mem_insert, hρ]
    have := key Finset.univ
    simpa [hm] using this
  · intro y τ k hk v u huv
    have e2 := prod_update U hUU v τ (v τ)
    simp only [Function.update_eq_self] at e2
    rw [hm, hm, prod_update U hUU v τ u, e2]
    have hc : Commute (ϖ (Pi.mulSingle τ k))
        ((Finset.univ.erase τ).noncommProd (fun j => U j (v j)) (pw U hUU _ _)) :=
      Finset.noncommProd_commute _ _ _ _ (fun j hj =>
        commute_away h (fun ρ => single_mem hk ρ) (by rw [Pi.mulSingle_eq_of_ne (Finset.ne_of_mem_erase hj)])
          (hU j (v j)))
    rw [Module.End.mul_apply, Module.End.mul_apply, huv, ← Module.End.mul_apply, ← hc.eq,
      Module.End.mul_apply]

end Grp

/- English proof (translation)
Introduce `D V Sp M P _ _ B ϖ h`. Establish `hKU : ∀ τ g, g ∈ Formalism.REAL.Kset (M.ε τ) → g ∈ UJset (M.ε τ)`. Introduce `τ g hg`. Take `⟨hu, hc⟩` from `hg`. Use `show gᴴ * Formalism.REAL.Jm (M.ε τ) * g = Formalism.REAL.Jm (M.ε τ)`.

Rewrite using `[Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff'.mp hu, Matrix.one_mul]`. Establish `hUR : ∀ τ, IsURepOn (Formalism.REAL.Kset (M.ε τ)) (M.σ τ)`. Introduce `τ`. Take `⟨⟨d1, d2⟩, d3, d4⟩` from `(M.ds τ).2.2.1`. Conclude with `⟨⟨d1, fun a ha b hb => d2 a (hKU τ a ha) b (hKU τ b hb)⟩, fun g hg => d3 g (hKU τ g hg), fun v => (d4 v).mono (fun g hg => hKU τ g hg)⟩`.

Use `choose S hSK hSsm using GlobalTheory.T.exists_lowestKType_le_smoothVectors D V Sp M`. Use `choose w T hw0 hTspan hTbot using fun τ => GlobalTheory.T.exists_operator_lowestWeight_holomorphic_KType V.rank (M.ε τ) (Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ)) (M.H τ) (M.σ τ) (S τ) (hUR τ) (hSK τ) P B (fun g => ϖ (Pi.mulSingle τ g)) (h.2.2.2 τ)`. Establish `: ∀ τ, FiniteDimensional ℂ (S τ)` using `fun τ => (hSK τ).1`. Establish `hstar : ∀ τ k, k ∈ Formalism.REAL.Kset (M.ε τ) → star k ∈ Formalism.REAL.Kset (M.ε τ)`. Introduce `τ k hk`.

Take `⟨hu, hc⟩` from `hk`. Use `⟨Unitary.star_mem hu, ?_⟩` and prove the remaining obligations. Establish `h3` using `congrArg star hc`. Rewrite `h3` using `[star_mul, star_mul, Matrix.star_eq_conjTranspose (Formalism.REAL.Jm _), Formalism.REAL.Jm_conjTranspose]`. Conclude with `h3.symm`.

Establish `hinner : ∀ τ k, k ∈ Formalism.REAL.Kset (M.ε τ) → ∀ x y : M.H τ, ⟪M.σ τ k x, M.σ τ k y⟫_ℂ = ⟪x, y⟫_ℂ`. Introduce `τ k hk x y`. Set `L : M.H τ →ₗᵢ[ℂ] M.H τ` to `{ toLinearMap := (M.σ τ k : M.H τ →ₗ[ℂ] M.H τ), norm_map' := (hUR τ).2.1 k hk }`. Conclude with `L.inner_map_map x y`. Establish `hproj : ∀ τ k, k ∈ Formalism.REAL.Kset (M.ε τ) → ∀ x : M.H τ, (S τ).starProjection (M.σ τ k x) = M.σ τ k ((S τ).starProjection x)`.

Introduce `τ k hk x`. Apply `Submodule.eq_starProjection_of_mem_of_inner_eq_zero` to reduce the goal to its premises. Conclude with `(hSK τ).2.1 k hk _ (Submodule.starProjection_apply_mem _ _)`. Introduce `z hz`. Establish `hz' : M.σ τ k (M.σ τ (star k) z) = z`.

Rewrite using `[← ContinuousLinearMap.comp_apply, ← (hUR τ).1.2 k hk (star k) (hstar τ k hk), Matrix.mem_unitaryGroup_iff.mp hk.1, (hUR τ).1.1]`. Both sides reduce to the same expression. Rewrite using `[← hz', ← map_sub, hinner τ k hk]`. Conclude with `Submodule.starProjection_inner_eq_zero _ _ ((hSK τ).2.1 _ (hstar τ k hk) _ hz)`. Set `U : ∀ τ, lowT M τ →ₗ[ℂ] Module.End ℂ P` to `fun τ => T τ ∘ₗ ((S τ).orthogonalProjectionOnto : M.H τ →ₗ[ℂ] S τ) ∘ₗ (M.sm τ).subtype ∘ₗ (lowT M τ).subtype`.

Establish `hU : ∀ τ (u : lowT M τ), U τ u = T τ ((S τ).orthogonalProjectionOnto ((u : M.sm τ) : M.H τ))` using `fun τ u => rfl`. Take `⟨m, hm1, hm2, hm3⟩` from `core h U (fun τ a => by rw [hU]; exact hTspan τ _)`. Use `⟨m, hm1, ?_, ?_⟩` and prove the remaining obligations. Introduce `κ hκ`. Establish `hmem : ∀ τ, M.σ τ (κ τ) (w τ : M.H τ) ∈ S τ` using `fun τ => (hSK τ).2.1 _ (hκ τ) _ (w τ).2`.

Establish `hlow : ∀ τ, S τ ≤ lowKSub (M.ε τ) (M.lam τ) (M.σ τ)` using `fun τ => le_sSup (hSK τ)`. Set `v : ∀ τ, lowT M τ` to `fun τ => ⟨⟨M.σ τ (κ τ) (w τ : M.H τ), hSsm τ (hmem τ)⟩, by show M.σ τ (κ τ) (w τ : M.H τ) ∈ lowKSub (M.ε τ) (M.lam τ) (M.σ τ)`. Conclude with `hlow τ (hmem τ)⟩`. Use `⟨v, fun τ hv => ?_, fun y hy => ?_⟩` and prove the remaining obligations. Apply `hw0 τ` to reduce the goal to its premises.

Establish `h0 : M.σ τ (κ τ) (w τ : M.H τ) = 0`. Use `congrArg (fun x : lowT M τ => ((x : M.sm τ) : M.H τ)) hv` as an intermediate fact. Simplify `this` using `[v]`. Establish `hn` using `(hUR τ).2.1 (κ τ) (hκ τ) (w τ : M.H τ)`. Rewrite `hn` using `[h0, norm_zero]`.

Conclude with `Subtype.ext (norm_eq_zero.mp hn.symm)`. Apply `hm2 _ (fun τ => conj_mem (hκ τ)) v y` to reduce the goal to its premises. Introduce `τ`. Take `⟨hb1, hb2⟩` from `hTbot τ y (hy τ)`. Rewrite using `[hU]`.

Establish `e3 : (S τ).orthogonalProjectionOnto (((v τ : lowT M τ) : M.sm τ) : M.H τ) = ⟨M.σ τ (κ τ) (w τ : M.H τ), hmem τ⟩` using `Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (⟨_, hmem τ⟩ : S τ)`. Rewrite using `[e3, hb2 (κ τ) (hκ τ) (w τ) _ rfl, hb1]`. Introduce `y hy τ k hk v u huv`. Apply `hm3 y τ (k.map star) (conj_mem hk) v u` to reduce the goal to its premises. Take `⟨_, hb2⟩` from `hTbot τ y (hy τ)`.

Rewrite using `[hU, hU]`. Apply `hb2 k hk` to reduce the goal to its premises. Rewrite using `[Submodule.coe_orthogonalProjectionOnto_apply, Submodule.coe_orthogonalProjectionOnto_apply, huv, hproj τ k hk]`.
-/
theorem lowest_types_act : ∀ (D : D7) (V : HSp D) (Sp : D.what₂.Tau → SPar) (M : DSModel V Sp) (P : Type) [AddCommGroup P] [Module ℂ P] (B : P →ₗ⋆[ℂ] P →ₗ[ℂ] ℂ) (ϖ : (D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) → Module.End ℂ P), IsHolFam M.ε B ϖ → ∃ m : LowT M →ₗ[ℂ] Module.End ℂ P, (∀ A : Module.End ℂ P, (∀ k, (∀ τ, k τ ∈ Formalism.REAL.Kset (M.ε τ)) → Commute A (ϖ k)) → ∀ x, Commute A (m x)) ∧ (∀ κ : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, κ τ ∈ Formalism.REAL.Kset (M.ε τ)) → ∃ v : ∀ τ, lowT M τ, (∀ τ, v τ ≠ 0) ∧ ∀ y, IsBotFam M.ε ϖ (fun τ => -Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ)) y → m (PiTensorProduct.tprod ℂ v) y = ϖ (fun τ => (κ τ).map star) y) ∧ ∀ y, IsBotFam M.ε ϖ (fun τ => -Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ)) y → ∀ τ, ∀ k ∈ Formalism.REAL.Kset (M.ε τ), ∀ (v : ∀ ρ, lowT M ρ) (u : lowT M τ), ((u : M.sm τ) : M.H τ) = M.σ τ k ((v τ : M.sm τ) : M.H τ) → m (PiTensorProduct.tprod ℂ (Function.update v τ u)) y = ϖ (Pi.mulSingle τ (k.map star)) (m (PiTensorProduct.tprod ℂ v) y) := by
  intro D V Sp M P _ _ B ϖ h
  have hKU : ∀ τ g, g ∈ Formalism.REAL.Kset (M.ε τ) → g ∈ UJset (M.ε τ) := by
    intro τ g hg
    obtain ⟨hu, hc⟩ := hg
    show gᴴ * Formalism.REAL.Jm (M.ε τ) * g = Formalism.REAL.Jm (M.ε τ)
    rw [Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose,
      Matrix.mem_unitaryGroup_iff'.mp hu, Matrix.one_mul]
  have hUR : ∀ τ, IsURepOn (Formalism.REAL.Kset (M.ε τ)) (M.σ τ) := by
    intro τ
    obtain ⟨⟨d1, d2⟩, d3, d4⟩ := (M.ds τ).2.2.1
    exact ⟨⟨d1, fun a ha b hb => d2 a (hKU τ a ha) b (hKU τ b hb)⟩, fun g hg => d3 g (hKU τ g hg),
      fun v => (d4 v).mono (fun g hg => hKU τ g hg)⟩
  choose S hSK hSsm using GlobalTheory.T.exists_lowestKType_le_smoothVectors D V Sp M
  choose w T hw0 hTspan hTbot using fun τ =>
    GlobalTheory.T.exists_operator_lowestWeight_holomorphic_KType V.rank (M.ε τ) (Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ)) (M.H τ) (M.σ τ) (S τ) (hUR τ)
      (hSK τ) P B (fun g => ϖ (Pi.mulSingle τ g)) (h.2.2.2 τ)
  have : ∀ τ, FiniteDimensional ℂ (S τ) := fun τ => (hSK τ).1

  have hstar : ∀ τ k, k ∈ Formalism.REAL.Kset (M.ε τ) → star k ∈ Formalism.REAL.Kset (M.ε τ) := by
    intro τ k hk
    obtain ⟨hu, hc⟩ := hk
    refine ⟨Unitary.star_mem hu, ?_⟩
    have h3 := congrArg star hc
    rw [star_mul, star_mul, Matrix.star_eq_conjTranspose (Formalism.REAL.Jm _), Formalism.REAL.Jm_conjTranspose] at h3
    exact h3.symm
  have hinner : ∀ τ k, k ∈ Formalism.REAL.Kset (M.ε τ) → ∀ x y : M.H τ, ⟪M.σ τ k x, M.σ τ k y⟫_ℂ = ⟪x, y⟫_ℂ := by
    intro τ k hk x y
    let L : M.H τ →ₗᵢ[ℂ] M.H τ := { toLinearMap := (M.σ τ k : M.H τ →ₗ[ℂ] M.H τ), norm_map' := (hUR τ).2.1 k hk }
    exact L.inner_map_map x y
  have hproj : ∀ τ k, k ∈ Formalism.REAL.Kset (M.ε τ) → ∀ x : M.H τ,
      (S τ).starProjection (M.σ τ k x) = M.σ τ k ((S τ).starProjection x) := by
    intro τ k hk x
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    · exact (hSK τ).2.1 k hk _ (Submodule.starProjection_apply_mem _ _)
    · intro z hz
      have hz' : M.σ τ k (M.σ τ (star k) z) = z := by
        rw [← ContinuousLinearMap.comp_apply, ← (hUR τ).1.2 k hk (star k) (hstar τ k hk),
          Matrix.mem_unitaryGroup_iff.mp hk.1, (hUR τ).1.1]
        rfl
      rw [← hz', ← map_sub, hinner τ k hk]
      exact Submodule.starProjection_inner_eq_zero _ _ ((hSK τ).2.1 _ (hstar τ k hk) _ hz)
  let U : ∀ τ, lowT M τ →ₗ[ℂ] Module.End ℂ P := fun τ =>
    T τ ∘ₗ ((S τ).orthogonalProjectionOnto : M.H τ →ₗ[ℂ] S τ) ∘ₗ (M.sm τ).subtype ∘ₗ (lowT M τ).subtype
  have hU : ∀ τ (u : lowT M τ), U τ u = T τ ((S τ).orthogonalProjectionOnto ((u : M.sm τ) : M.H τ)) :=
    fun τ u => rfl
  obtain ⟨m, hm1, hm2, hm3⟩ := core h U (fun τ a => by rw [hU]; exact hTspan τ _)
  refine ⟨m, hm1, ?_, ?_⟩
  · intro κ hκ
    have hmem : ∀ τ, M.σ τ (κ τ) (w τ : M.H τ) ∈ S τ := fun τ => (hSK τ).2.1 _ (hκ τ) _ (w τ).2
    have hlow : ∀ τ, S τ ≤ lowKSub (M.ε τ) (M.lam τ) (M.σ τ) := fun τ => le_sSup (hSK τ)
    let v : ∀ τ, lowT M τ := fun τ =>
      ⟨⟨M.σ τ (κ τ) (w τ : M.H τ), hSsm τ (hmem τ)⟩, by
        show M.σ τ (κ τ) (w τ : M.H τ) ∈ lowKSub (M.ε τ) (M.lam τ) (M.σ τ)
        exact hlow τ (hmem τ)⟩
    refine ⟨v, fun τ hv => ?_, fun y hy => ?_⟩
    · apply hw0 τ
      have h0 : M.σ τ (κ τ) (w τ : M.H τ) = 0 := by
        have := congrArg (fun x : lowT M τ => ((x : M.sm τ) : M.H τ)) hv
        simpa [v] using this
      have hn := (hUR τ).2.1 (κ τ) (hκ τ) (w τ : M.H τ)
      rw [h0, norm_zero] at hn
      exact Subtype.ext (norm_eq_zero.mp hn.symm)
    · apply hm2 _ (fun τ => conj_mem (hκ τ)) v y
      intro τ
      obtain ⟨hb1, hb2⟩ := hTbot τ y (hy τ)
      rw [hU]
      have e3 : (S τ).orthogonalProjectionOnto (((v τ : lowT M τ) : M.sm τ) : M.H τ) =
          ⟨M.σ τ (κ τ) (w τ : M.H τ), hmem τ⟩ :=
        Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (⟨_, hmem τ⟩ : S τ)
      rw [e3, hb2 (κ τ) (hκ τ) (w τ) _ rfl, hb1]
  · intro y hy τ k hk v u huv
    apply hm3 y τ (k.map star) (conj_mem hk) v u
    obtain ⟨_, hb2⟩ := hTbot τ y (hy τ)
    rw [hU, hU]
    apply hb2 k hk
    rw [Submodule.coe_orthogonalProjectionOnto_apply, Submodule.coe_orthogonalProjectionOnto_apply, huv,
      hproj τ k hk]

end GlobalTheory.JointHarm.MultiOp
