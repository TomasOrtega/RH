import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockUniOne
open NumberField CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula Formalism.L2.Pj GlobalTheory GlobalTheory.ArInt GlobalTheory.VB GlobalTheory.CovTest GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.TwoLat GlobalTheory.OrthFilt GlobalTheory.VdmRec GlobalTheory.TrueGeo
open GlobalTheory.LieVB (omega)
open GlobalTheory.LocM (tanEv)
open Formalism.MainNotions.DIV.Cons (intO)
open scoped Classical
open GlobalTheory.LieFilt

namespace GlobalTheory.LieFilt

/- English proof (translation)
Establish `hsub : ∀ x y : K, ‖x - y‖ ≤ max ‖x‖ ‖y‖` using `fun x y => by`. Simplify `IsUltrametricDist.norm_add_le_max x (-y)` using `[sub_eq_add_neg, norm_neg]`. Establish `hcol : ∀ z : κ, ∃ a' : κ → K, (∀ z', ¬ bl z' < bl z → a' z' = 0) ∧ ∀ b, ‖P.mulVec (Pi.single z 1 + a') b‖ ≤ 1`. Introduce `z`. Use `(hG (bl z) (Pi.single z 1) ?_).1 ?_` and prove the remaining obligations.

Introduce `z' hz'`. Establish `: z' ≠ z` using `fun h => hz' (h ▸ rfl)`. Simplify using `[Pi.single_apply, this]`. Introduce `z'`. Distinguish the cases in `h : z' = z`.

Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, h]`. Use `choose a' ha'0 ha'1 using hcol`. Use `set N : Matrix κ κ K := Matrix.of fun z' z => ((Pi.single z (1 : K) : κ → K) + a' z) z' with hN`.

Establish `hBU : BlockUni bl N`. Introduce `z' z h`. Simplify using `only [hN, Matrix.of_apply, Pi.add_apply, ha'0 z z' h, add_zero, Matrix.one_apply, Pi.single_apply]`. Establish `hBT : N.BlockTriangular bl`. Introduce `z' z h`.

Rewrite using `[hBU z' z (by omega), Matrix.one_apply_ne (fun e => by subst e; exact lt_irrefl _ h)]`. Establish `hdet : N.det = 1`. Rewrite using `[hBT.det]`. Use `Finset.prod_eq_one fun k _ => ?_` and prove the remaining obligations. Establish `: N.toSquareBlock bl k = 1`.

Use extensionality with `⟨i, hi⟩ ⟨j, hj⟩`. Simplify using `only [Matrix.toSquareBlock_def, Matrix.of_apply]`. Rewrite using `[hBU i j (by omega)]`. Simplify using `[Matrix.one_apply, Subtype.ext_iff]`. Rewrite using `[this, Matrix.det_one]`.

Establish `hNu : IsUnit N.det` using `by rw [hdet]; exact isUnit_one`. Establish `hNbij : Function.Bijective N.mulVec`. Prove the components needed by the constructor for the conclusion. Introduce `v w h`. Use `congrArg (fun x => N⁻¹.mulVec x) h` as an intermediate fact.

Simplify `this` using `[Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul N hNu]`. Introduce `v`. Conclude with `⟨N⁻¹.mulVec v, by simp [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv N hNu]⟩`. Use `set C := P * N with hC`. Establish `hCint : ∀ b z, ‖C b z‖ ≤ 1`.

Introduce `b z`. Use `ha'1 z b` as an intermediate fact. Use `this using 2` and compare the differences between its conclusion and the goal. Simplify using `[hC, Matrix.mul_apply, Matrix.mulVec, dotProduct, hN]`. Establish `hCbij : Function.Bijective (Matrix.toLin' C)`.

Establish `: (Matrix.toLin' C : (κ → K) → (Fin g → K)) = P.mulVec ∘ N.mulVec`. Use function extensionality and compare the values at `v`. Simplify using `[hC, Matrix.mulVec_mulVec]`. Rewrite using `[this]`. Conclude with `hP.comp hNbij`.

Use `set e := LinearEquiv.ofBijective (Matrix.toLin' C) hCbij with he`. Use `set C' : Matrix κ (Fin g) K := LinearMap.toMatrix' (e.symm : (Fin g → K) →ₗ[K] (κ → K)) with hC'`. Establish `h1 : C * C' = 1`. Apply `Matrix.toLin'.injective` to reduce the goal to its premises. Rewrite using `[Matrix.toLin'_mul, hC', Matrix.toLin'_toMatrix', Matrix.toLin'_one]`.

Use `LinearMap.ext fun v => ?_` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply, LinearMap.id_apply]`. Conclude with `e.apply_symm_apply v`. Establish `h2 : C' * C = 1`. Apply `Matrix.toLin'.injective` to reduce the goal to its premises.

Rewrite using `[Matrix.toLin'_mul, hC', Matrix.toLin'_toMatrix', Matrix.toLin'_one]`. Use `LinearMap.ext fun v => ?_` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply, LinearMap.id_apply]`. Conclude with `e.symm_apply_apply v`. Establish `key : ∀ k : ℕ, ∀ y : κ → K, (∀ z, k ≤ bl z → y z = 0) → (∀ b, ‖C.mulVec y b‖ ≤ 1) → ∀ z, ‖y z‖ ≤ 1`.

Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro y hy _ z`. Rewrite using `[hy z (Nat.zero_le _)]`. Simplify using the standard rewrite rules.

Consider the case `succ k ih`. Introduce `y hy hCy`. Use `set yk : κ → K := fun z => if bl z = k then y z else 0 with hyk`. Establish `hNy : ∀ z, ¬ bl z < k → N.mulVec y z = y z`. Introduce `z hz`.

Simplify using `only [Matrix.mulVec, dotProduct]`. Rewrite using `[Finset.sum_eq_single z]`. Rewrite using `[hBU z z (lt_irrefl _)]`. Simplify using the standard rewrite rules. Introduce `w _ hw`.

Distinguish the cases in `hwk : k + 1 ≤ bl w`. Rewrite using `[hy w hwk, mul_zero]`. Rewrite using `[hBU z w (by omega), Matrix.one_apply_ne (Ne.symm hw), zero_mul]`. Simplify using the standard rewrite rules. Establish `hyk_int : ∀ z, ‖yk z‖ ≤ 1`.

Use `(hG k yk ?_).2 ⟨N.mulVec y - yk, ?_, ?_⟩` and prove the remaining obligations. Introduce `z hz`. Simplify using `[hyk, hz]`. Introduce `z hz`. Rewrite using `[Pi.sub_apply, hNy z hz]`.

Distinguish the cases in `h : bl z = k`. Simplify using `[hyk, h]`. Simplify using `[hyk, h, hy z (by omega)]`. Introduce `b`. Establish `: yk + (N.mulVec y - yk) = N.mulVec y` using `by ext; simp`.

Rewrite using `[this, Matrix.mulVec_mulVec]`. Conclude with `hCy b`. Establish `hCyk : ∀ b, ‖C.mulVec yk b‖ ≤ 1`. Introduce `b`. Simplify using `only [Matrix.mulVec, dotProduct]`.

Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun z _ => ?_` and prove the remaining obligations. Rewrite using `[norm_mul]`. Conclude with `mul_le_one₀ (hCint b z) (norm_nonneg _) (hyk_int z)`. Establish `hrest` using `ih (y - yk) (fun z hz => by`. Distinguish the cases in `h : bl z = k`.

Simplify using `[hyk, h]`. Simplify using `[hyk, h, hy z (by omega)])`. Use the proof step `(fun b => by`. Rewrite using `[Matrix.mulVec_sub, Pi.sub_apply]`. Conclude with `(hsub _ _).trans (max_le (hCy b) (hCyk b)))`.

Introduce `z`. Establish `: y z = (y - yk) z + yk z` using `by simp`. Rewrite using `[this]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hrest z) (hyk_int z))`. Establish `hyall : ∀ y : κ → K, (∀ b, ‖C.mulVec y b‖ ≤ 1) → ∀ z, ‖y z‖ ≤ 1` using `fun y hy => key (Finset.univ.sup bl + 1) y (fun z hz => absurd hz (by have := Finset.le_sup (f := bl) (Finset.mem_univ z); omega)) hy`.

Use `⟨N, C', hBU, hCint, ?_, h1, h2⟩` and prove the remaining obligations. Introduce `z b`. Use `hyall (fun z => C' z b) (fun i => ?_) z` and prove the remaining obligations. Establish `: C.mulVec (fun z => C' z b) i = (C * C') i b`. Simplify using `[Matrix.mulVec, dotProduct, Matrix.mul_apply]`.

Rewrite using `[this, h1, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem intAdapted_of_grCond {K : Type} [NormedField K] [IsUltrametricDist K] {κ : Type} [Fintype κ] (bl : κ → ℕ)
    {g : ℕ} (P : Matrix (Fin g) κ K) (hP : Function.Bijective P.mulVec) (hG : GrCond bl P) : IntAdapted bl P := by
  have hsub : ∀ x y : K, ‖x - y‖ ≤ max ‖x‖ ‖y‖ := fun x y => by
    simpa [sub_eq_add_neg, norm_neg] using IsUltrametricDist.norm_add_le_max x (-y)
  have hcol : ∀ z : κ, ∃ a' : κ → K, (∀ z', ¬ bl z' < bl z → a' z' = 0) ∧
      ∀ b, ‖P.mulVec (Pi.single z 1 + a') b‖ ≤ 1 := by
    intro z
    refine (hG (bl z) (Pi.single z 1) ?_).1 ?_
    · intro z' hz'
      have : z' ≠ z := fun h => hz' (h ▸ rfl)
      simp [Pi.single_apply, this]
    · intro z'
      by_cases h : z' = z
      · subst h; simp
      · simp [Pi.single_apply, h]
  choose a' ha'0 ha'1 using hcol
  set N : Matrix κ κ K := Matrix.of fun z' z => ((Pi.single z (1 : K) : κ → K) + a' z) z' with hN
  have hBU : BlockUni bl N := by
    intro z' z h
    simp only [hN, Matrix.of_apply, Pi.add_apply, ha'0 z z' h, add_zero, Matrix.one_apply, Pi.single_apply]
  have hBT : N.BlockTriangular bl := by
    intro z' z h
    rw [hBU z' z (by omega), Matrix.one_apply_ne (fun e => by subst e; exact lt_irrefl _ h)]
  have hdet : N.det = 1 := by
    rw [hBT.det]
    refine Finset.prod_eq_one fun k _ => ?_
    have : N.toSquareBlock bl k = 1 := by
      ext ⟨i, hi⟩ ⟨j, hj⟩
      simp only [Matrix.toSquareBlock_def, Matrix.of_apply]
      rw [hBU i j (by omega)]
      simp [Matrix.one_apply, Subtype.ext_iff]
    rw [this, Matrix.det_one]
  have hNu : IsUnit N.det := by rw [hdet]; exact isUnit_one
  have hNbij : Function.Bijective N.mulVec := by
    constructor
    · intro v w h
      have := congrArg (fun x => N⁻¹.mulVec x) h
      simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul N hNu] using this
    · intro v
      exact ⟨N⁻¹.mulVec v, by simp [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv N hNu]⟩
  set C := P * N with hC
  have hCint : ∀ b z, ‖C b z‖ ≤ 1 := by
    intro b z
    have := ha'1 z b
    convert this using 2
    simp [hC, Matrix.mul_apply, Matrix.mulVec, dotProduct, hN]
  have hCbij : Function.Bijective (Matrix.toLin' C) := by
    have : (Matrix.toLin' C : (κ → K) → (Fin g → K)) = P.mulVec ∘ N.mulVec := by
      funext v; simp [hC, Matrix.mulVec_mulVec]
    rw [this]; exact hP.comp hNbij
  set e := LinearEquiv.ofBijective (Matrix.toLin' C) hCbij with he
  set C' : Matrix κ (Fin g) K := LinearMap.toMatrix' (e.symm : (Fin g → K) →ₗ[K] (κ → K)) with hC'
  have h1 : C * C' = 1 := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, hC', Matrix.toLin'_toMatrix', Matrix.toLin'_one]
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.comp_apply, LinearMap.id_apply]
    exact e.apply_symm_apply v
  have h2 : C' * C = 1 := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, hC', Matrix.toLin'_toMatrix', Matrix.toLin'_one]
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.comp_apply, LinearMap.id_apply]
    exact e.symm_apply_apply v
  have key : ∀ k : ℕ, ∀ y : κ → K, (∀ z, k ≤ bl z → y z = 0) → (∀ b, ‖C.mulVec y b‖ ≤ 1) →
      ∀ z, ‖y z‖ ≤ 1 := by
    intro k
    induction k with
    | zero => intro y hy _ z; rw [hy z (Nat.zero_le _)]; simp
    | succ k ih =>
      intro y hy hCy
      set yk : κ → K := fun z => if bl z = k then y z else 0 with hyk
      have hNy : ∀ z, ¬ bl z < k → N.mulVec y z = y z := by
        intro z hz
        simp only [Matrix.mulVec, dotProduct]
        rw [Finset.sum_eq_single z]
        · rw [hBU z z (lt_irrefl _)]; simp
        · intro w _ hw
          by_cases hwk : k + 1 ≤ bl w
          · rw [hy w hwk, mul_zero]
          · rw [hBU z w (by omega), Matrix.one_apply_ne (Ne.symm hw), zero_mul]
        · simp
      have hyk_int : ∀ z, ‖yk z‖ ≤ 1 := by
        refine (hG k yk ?_).2 ⟨N.mulVec y - yk, ?_, ?_⟩
        · intro z hz; simp [hyk, hz]
        · intro z hz
          rw [Pi.sub_apply, hNy z hz]
          by_cases h : bl z = k
          · simp [hyk, h]
          · simp [hyk, h, hy z (by omega)]
        · intro b
          have : yk + (N.mulVec y - yk) = N.mulVec y := by ext; simp
          rw [this, Matrix.mulVec_mulVec]
          exact hCy b
      have hCyk : ∀ b, ‖C.mulVec yk b‖ ≤ 1 := by
        intro b
        simp only [Matrix.mulVec, dotProduct]
        refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun z _ => ?_
        rw [norm_mul]
        exact mul_le_one₀ (hCint b z) (norm_nonneg _) (hyk_int z)
      have hrest := ih (y - yk)
        (fun z hz => by
          by_cases h : bl z = k
          · simp [hyk, h]
          · simp [hyk, h, hy z (by omega)])
        (fun b => by
          rw [Matrix.mulVec_sub, Pi.sub_apply]
          exact (hsub _ _).trans (max_le (hCy b) (hCyk b)))
      intro z
      have : y z = (y - yk) z + yk z := by simp
      rw [this]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hrest z) (hyk_int z))
  have hyall : ∀ y : κ → K, (∀ b, ‖C.mulVec y b‖ ≤ 1) → ∀ z, ‖y z‖ ≤ 1 := fun y hy =>
    key (Finset.univ.sup bl + 1) y
      (fun z hz => absurd hz (by have := Finset.le_sup (f := bl) (Finset.mem_univ z); omega)) hy
  refine ⟨N, C', hBU, hCint, ?_, h1, h2⟩
  intro z b
  refine hyall (fun z => C' z b) (fun i => ?_) z
  have : C.mulVec (fun z => C' z b) i = (C * C') i b := by
    simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
  rw [this, h1, Matrix.one_apply]
  split_ifs <;> simp

/- English proof (translation)
Introduce `K _ _ κ _ bl g P hP hG`. Conclude with `intAdapted_of_grCond bl P hP hG`.
-/
theorem intAdapted_of_grCond' : ∀ {K : Type} [NormedField K] [IsUltrametricDist K] {κ : Type} [Fintype κ] (bl : κ → ℕ) {g : ℕ}
    (P : Matrix (Fin g) κ K), Function.Bijective P.mulVec → GrCond bl P → IntAdapted bl P :=
  by intro K _ _ κ _ bl g P hP hG; exact intAdapted_of_grCond bl P hP hG

end GlobalTheory.LieFilt
