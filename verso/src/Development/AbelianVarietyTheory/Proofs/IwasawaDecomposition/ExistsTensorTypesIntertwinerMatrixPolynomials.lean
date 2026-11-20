import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import ReciprocityTheory.DualLattices.FischerSelfNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TotalDegreeSubstFLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryGroupIntertwinerOfHighestWeightPolyStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsJointHighestWeightLeadingMinorProductStatement

open Formalism.MainNotions.S Matrix GlobalTheory.CompactHowe
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompactHoweJoint

/- English proof (translation)
Set `𝓗 : Submodule ℂ (H →ₗ[ℂ] P)` to `{ carrier := {A | ∀ g ∈ S, ∀ u, A (τ g u) = a g (A u)} add_mem' := fun {A B} hA hB g hg u => by`. Simplify using `only [LinearMap.add_apply, map_add, hA g hg u, hB g hg u]`. Use the proof step `zero_mem' := fun g _ u => by simp`. Use the proof step `smul_mem' := fun c A hA g hg u => by`. Simplify using `only [LinearMap.smul_apply, map_smul, hA g hg u] }`.

Establish `hv₀ : v₀ ≠ 0` using `fun h => hne (by rw [h, map_zero])`. Establish `hv₀' : v₀' ≠ 0` using `fun h => hne (by rw [h0, h, map_zero])`. Set `ev : 𝓗 →ₗ[ℂ] P` to `(LinearMap.applyₗ v₀).comp 𝓗.subtype`. Establish `hev : ∀ A : 𝓗, ev A = (A : H →ₗ[ℂ] P) v₀` using `fun _ => rfl`. Establish `hinj : Function.Injective ev`.

Rewrite using `[injective_iff_map_eq_zero]`. Introduce `A hA`. Break down `hirr (LinearMap.ker (A : H →ₗ[ℂ] P)) (fun g hg v hv => by` into its components or cases. Rewrite `hv`, the goal using `[LinearMap.mem_ker]`. Rewrite using `[A.2 g hg v, hv, map_zero]) with h | h`.

Conclude with `absurd ((Submodule.eq_bot_iff _).1 h v₀ hA) hv₀`. Conclude with `Subtype.ext (LinearMap.ker_eq_top.1 h)`. Establish `hstab : ∀ h, ∀ A ∈ 𝓗, (b h).comp A ∈ 𝓗` using `fun h A hA g hg u => by`. Rewrite using `[LinearMap.comp_apply, LinearMap.comp_apply, hA g hg u, hab]`. Establish `hrange : ∀ v', L' v' ∈ LinearMap.range ev`.

Break down `hirr' ((LinearMap.range ev).comap L') (fun h hh v hv => by` into its components or cases. Take `⟨A, hA⟩` from `hv`. Use `⟨⟨(b h).comp A, hstab h _ A.2⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hL' h hh, ← hA]`. Use the proof step `rfl) with h | h`.

Conclude with `absurd ((Submodule.eq_bot_iff _).1 h v₀' ⟨⟨L, hL⟩, h0⟩) hv₀'`. Introduce `v'`. Establish `: v' ∈ (LinearMap.range ev).comap L'` using `h ▸ Submodule.mem_top`. Conclude with `this`. Set `Φ : H' →ₗ[ℂ] 𝓗` to `(LinearEquiv.ofInjective ev hinj).symm.toLinearMap.comp (L'.codRestrict _ hrange)`.

Establish `hΦ : ∀ v', ev (Φ v') = L' v'` using `fun v' => congrArg Subtype.val ((LinearEquiv.ofInjective ev hinj).apply_symm_apply (L'.codRestrict _ hrange v'))`. Use `⟨𝓗.subtype.comp Φ, fun h => hne ?_, fun h hh g hg v' v => ?_⟩` and prove the remaining obligations. Rewrite using `[h0, ← hΦ, hev]`. Conclude with `congrArg (fun f : H' →ₗ[ℂ] H →ₗ[ℂ] P => f v₀' v₀) h`. Establish `key : Φ (τ' h v') = ⟨(b h).comp (Φ v'), hstab h _ (Φ v').2⟩`.

Apply `hinj` to reduce the goal to its premises. Rewrite using `[hΦ, hL' h hh, ← hΦ v']`. Both sides reduce to the same expression. Use `show (Φ (τ' h v') : H →ₗ[ℂ] P) (τ g v) = b h (a g ((Φ v' : H →ₗ[ℂ] P) v))`. Rewrite using `[key]`.

Use `show b h ((Φ v' : H →ₗ[ℂ] P) (τ g v)) = _`. Rewrite using `[(Φ v').2 g hg v]`.
-/
theorem exists_bilinear {G G' H H' P : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup H'] [Module ℂ H']
    [AddCommGroup P] [Module ℂ P] (S : Set G) (S' : Set G') (τ : G → H →ₗ[ℂ] H) (τ' : G' → H' →ₗ[ℂ] H')
    (a : G → P →ₗ[ℂ] P) (b : G' → P →ₗ[ℂ] P) (hab : ∀ g h x, a g (b h x) = b h (a g x))
    (hirr : ∀ U : Submodule ℂ H, (∀ g ∈ S, ∀ v ∈ U, τ g v ∈ U) → U = ⊥ ∨ U = ⊤)
    (hirr' : ∀ U : Submodule ℂ H', (∀ g ∈ S', ∀ v ∈ U, τ' g v ∈ U) → U = ⊥ ∨ U = ⊤)
    (L : H →ₗ[ℂ] P) (L' : H' →ₗ[ℂ] P) (hL : ∀ g ∈ S, ∀ u, L (τ g u) = a g (L u))
    (hL' : ∀ h ∈ S', ∀ u, L' (τ' h u) = b h (L' u)) (v₀ : H) (v₀' : H') (h0 : L v₀ = L' v₀')
    (hne : L v₀ ≠ 0) :
    ∃ Ψ : H' →ₗ[ℂ] H →ₗ[ℂ] P, Ψ ≠ 0 ∧ ∀ h ∈ S', ∀ g ∈ S, ∀ v' v, Ψ (τ' h v') (τ g v) = b h (a g (Ψ v' v)) := by
  let 𝓗 : Submodule ℂ (H →ₗ[ℂ] P) :=
    { carrier := {A | ∀ g ∈ S, ∀ u, A (τ g u) = a g (A u)}
      add_mem' := fun {A B} hA hB g hg u => by
        simp only [LinearMap.add_apply, map_add, hA g hg u, hB g hg u]
      zero_mem' := fun g _ u => by simp
      smul_mem' := fun c A hA g hg u => by
        simp only [LinearMap.smul_apply, map_smul, hA g hg u] }
  have hv₀ : v₀ ≠ 0 := fun h => hne (by rw [h, map_zero])
  have hv₀' : v₀' ≠ 0 := fun h => hne (by rw [h0, h, map_zero])
  let ev : 𝓗 →ₗ[ℂ] P := (LinearMap.applyₗ v₀).comp 𝓗.subtype
  have hev : ∀ A : 𝓗, ev A = (A : H →ₗ[ℂ] P) v₀ := fun _ => rfl
  have hinj : Function.Injective ev := by
    rw [injective_iff_map_eq_zero]
    intro A hA
    rcases hirr (LinearMap.ker (A : H →ₗ[ℂ] P)) (fun g hg v hv => by
      rw [LinearMap.mem_ker] at hv ⊢
      rw [A.2 g hg v, hv, map_zero]) with h | h
    · exact absurd ((Submodule.eq_bot_iff _).1 h v₀ hA) hv₀
    · exact Subtype.ext (LinearMap.ker_eq_top.1 h)
  have hstab : ∀ h, ∀ A ∈ 𝓗, (b h).comp A ∈ 𝓗 := fun h A hA g hg u => by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hA g hg u, hab]
  have hrange : ∀ v', L' v' ∈ LinearMap.range ev := by
    rcases hirr' ((LinearMap.range ev).comap L') (fun h hh v hv => by
      obtain ⟨A, hA⟩ := hv
      refine ⟨⟨(b h).comp A, hstab h _ A.2⟩, ?_⟩
      rw [hL' h hh, ← hA]
      rfl) with h | h
    · exact absurd ((Submodule.eq_bot_iff _).1 h v₀' ⟨⟨L, hL⟩, h0⟩) hv₀'
    · intro v'
      have : v' ∈ (LinearMap.range ev).comap L' := h ▸ Submodule.mem_top
      exact this
  let Φ : H' →ₗ[ℂ] 𝓗 :=
    (LinearEquiv.ofInjective ev hinj).symm.toLinearMap.comp (L'.codRestrict _ hrange)
  have hΦ : ∀ v', ev (Φ v') = L' v' := fun v' =>
    congrArg Subtype.val ((LinearEquiv.ofInjective ev hinj).apply_symm_apply (L'.codRestrict _ hrange v'))
  refine ⟨𝓗.subtype.comp Φ, fun h => hne ?_, fun h hh g hg v' v => ?_⟩
  · rw [h0, ← hΦ, hev]
    exact congrArg (fun f : H' →ₗ[ℂ] H →ₗ[ℂ] P => f v₀' v₀) h
  · have key : Φ (τ' h v') = ⟨(b h).comp (Φ v'), hstab h _ (Φ v').2⟩ := by
      apply hinj
      rw [hΦ, hL' h hh, ← hΦ v']
      rfl
    show (Φ (τ' h v') : H →ₗ[ℂ] P) (τ g v) = b h (a g ((Φ v' : H →ₗ[ℂ] P) v))
    rw [key]
    show b h ((Φ v' : H →ₗ[ℂ] P) (τ g v)) = _
    rw [(Φ v').2 g hg v]

/- English proof (translation)
Establish `hJ : Formalism.REAL.Jm (allPos k) = 1` using `by simp [Formalism.REAL.Jm, allPos]`. Use `show (g ∈ Matrix.unitaryGroup (Fin k) ℂ ∧ g * Formalism.REAL.Jm (allPos k) = Formalism.REAL.Jm (allPos k) * g) ↔ gᴴ * Formalism.REAL.Jm (allPos k) * g = Formalism.REAL.Jm (allPos k)`. Rewrite using `[hJ, Matrix.mul_one, Matrix.mul_one, Matrix.one_mul, Matrix.mem_unitaryGroup_iff']`. Simplify using `[Matrix.star_eq_conjTranspose]`.
-/
theorem mem_K_iff {k : ℕ} (g : Matrix (Fin k) (Fin k) ℂ) :
    g ∈ Formalism.REAL.Kset (allPos k) ↔ g ∈ UJset (allPos k) := by
  have hJ : Formalism.REAL.Jm (allPos k) = 1 := by simp [Formalism.REAL.Jm, allPos]
  show (g ∈ Matrix.unitaryGroup (Fin k) ℂ ∧ g * Formalism.REAL.Jm (allPos k) = Formalism.REAL.Jm (allPos k) * g) ↔
    gᴴ * Formalism.REAL.Jm (allPos k) * g = Formalism.REAL.Jm (allPos k)
  rw [hJ, Matrix.mul_one, Matrix.mul_one, Matrix.one_mul, Matrix.mem_unitaryGroup_iff']
  simp [Matrix.star_eq_conjTranspose]

open MvPolynomial in
/- English proof (translation)
Establish `key : subst2 h (1 : Matrix (Fin n) (Fin n) ℂ) = ReciprocityTheory.PGsh.rowSubst h`. Use `algHom_ext fun p => ?_` and prove the remaining obligations. Rewrite using `[subst2_X, ReciprocityTheory.PGsh.rowSubst, aeval_X]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single p.2]`.

Simplify using the standard rewrite rules. Introduce `l _ hl`. Simplify using `[Matrix.one_apply_ne hl]`. Simplify using the standard rewrite rules. Rewrite using `[key]`.
-/
theorem subst2_one_right {N n : ℕ} (h : Matrix (Fin N) (Fin N) ℂ) (P : MvPolynomial (Fin N × Fin n) ℂ) :
    subst2 h 1 P = ReciprocityTheory.PGsh.rowSubst h P := by
  have key : subst2 h (1 : Matrix (Fin n) (Fin n) ℂ) = ReciprocityTheory.PGsh.rowSubst h := by
    refine algHom_ext fun p => ?_
    rw [subst2_X, ReciprocityTheory.PGsh.rowSubst, aeval_X]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_eq_single p.2]
    · simp
    · intro l _ hl; simp [Matrix.one_apply_ne hl]
    · simp
  rw [key]

open MvPolynomial in
/- English proof (translation)
Establish `key : (subst2 (1 : Matrix (Fin N) (Fin N) ℂ) g).comp (rename Prod.swap) = (rename Prod.swap).comp (ReciprocityTheory.PGsh.rowSubst (ι` using `Fin N) g) := by`. Use `algHom_ext fun p => ?_` and prove the remaining obligations. Rewrite using `[AlgHom.comp_apply, AlgHom.comp_apply, rename_X, subst2_X, ReciprocityTheory.PGsh.rowSubst, aeval_X, Finset.sum_eq_single p.2]`. Establish `h1 : (1 : Matrix (Fin N) (Fin N) ℂ) p.2 p.swap.1 = 1` using `Matrix.one_apply_eq _`. Simplify using `[map_sum, h1]`.

Introduce `l _ hl`. Establish `h1 : (1 : Matrix (Fin N) (Fin N) ℂ) l p.swap.1 = 0` using `Matrix.one_apply_ne hl`. Simplify using `[h1]`. Simplify using the standard rewrite rules. Conclude with `congrArg (fun f => f P) key`.
-/
theorem subst2_one_left {N n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) (P : MvPolynomial (Fin n × Fin N) ℂ) :
    subst2 1 g (rename Prod.swap P) = rename Prod.swap (ReciprocityTheory.PGsh.rowSubst g P) := by
  have key : (subst2 (1 : Matrix (Fin N) (Fin N) ℂ) g).comp (rename Prod.swap) =
      (rename Prod.swap).comp (ReciprocityTheory.PGsh.rowSubst (ι := Fin N) g) := by
    refine algHom_ext fun p => ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply, rename_X, subst2_X, ReciprocityTheory.PGsh.rowSubst, aeval_X,
      Finset.sum_eq_single p.2]
    · have h1 : (1 : Matrix (Fin N) (Fin N) ℂ) p.2 p.swap.1 = 1 := Matrix.one_apply_eq _
      simp [map_sum, h1]
    · intro l _ hl
      have h1 : (1 : Matrix (Fin N) (Fin N) ℂ) l p.swap.1 = 0 := Matrix.one_apply_ne hl
      simp [h1]
    · simp
  exact congrArg (fun f => f P) key

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun _ => Matrix.one_apply_eq _, fun _ _ h => Matrix.one_apply_ne h.ne'⟩`.
-/
theorem isUpperUnitri_one (k : ℕ) : ReciprocityTheory.PGsh.IsUpperUnitri (1 : Matrix (Fin k) (Fin k) ℂ) :=
  ⟨fun _ => Matrix.one_apply_eq _, fun _ _ h => Matrix.one_apply_ne h.ne'⟩

open MvPolynomial in

/- English proof (translation)
Introduce `N n hn ν H _ _ _ τ H' _ _ _ τ' hν hz hτ hK hτ' hK'`. Take `⟨Δ, hΔ, hU, hD⟩` from `GlobalTheory.T.exists_jointHighestWeight_leadingMinorProduct N n hn ν hν hz`. Establish `hsw : ∀ Q : MvPolynomial (Fin N × Fin n) ℂ, rename (Prod.swap : Fin n × Fin N → _) (rename Prod.swap Q) = Q` using `fun Q => by`. Rewrite using `[rename_rename]`. Simplify using the standard rewrite rules.

Establish `hinj : Function.Injective (rename (Prod.swap : Fin n × Fin N → Fin N × Fin n) : MvPolynomial _ ℂ → MvPolynomial _ ℂ)` using `rename_injective _ Prod.swap_injective`. Take `⟨L', hL', v₀', hv'⟩` from `GlobalTheory.T.exists_unitaryGroup_intertwiner_of_highest_weight_polynomial N (Fin n) ν H' τ' Δ hτ' hK' hΔ (fun g hg => by rw [← subst2_one_right, hU g 1 hg (isUpperUnitri_one n)]) (fun d => by`. Use `hD d (fun _ => 1)` as an intermediate fact. Rewrite `this` using `[Matrix.diagonal_one, subst2_one_right]`. Simplify using `using this)`.

Take `⟨L, hL, v₀, hv⟩` from `GlobalTheory.T.exists_unitaryGroup_intertwiner_of_highest_weight_polynomial n (Fin N) (fun a => ν (Fin.castLE hn a)) H τ (rename Prod.swap Δ) hτ hK (fun h => hΔ (by rw [← hsw Δ, h, map_zero])) (fun g hg => hinj (by rw [← subst2_one_left, hsw, hU 1 g (isUpperUnitri_one N) hg])) (f …`. Use `hD (fun _ => 1) e` as an intermediate fact. Rewrite `this` using `[Matrix.diagonal_one]`. Rewrite using `[← subst2_one_left, map_smul, hsw, this]`. Use the proof step `simp))`.

Establish `hLv : ((rename (Prod.swap : Fin n × Fin N → Fin N × Fin n)).toLinearMap.comp L) v₀ = Δ` using `by show rename Prod.swap (L v₀) = Δ`. Rewrite using `[hv, hsw]`. Take `⟨Ψ, hΨ, hΨe⟩` from `exists_bilinear (UJset (allPos n)) (UJset (allPos N)) (fun g => (τ g).toLinearMap) (fun h => (τ' h).toLinearMap) (fun g => (subst2 (1 : Matrix (Fin N) (Fin N) ℂ) g).toLinearMap) (fun h => (subst2 h (1 : Matrix (Fin n) (Fin n) ℂ)).toLinearMap) (fun g h x => by simp [subst2_mul]) ( …`. Rewrite using `[hL g hg u, subst2_one_left])`. Use the proof step `(fun h hh u => by show L' (τ' h u) = subst2 h 1 (L' u)`.

Rewrite using `[hL' h hh u, subst2_one_right])`. Use `v₀ v₀' (hLv.trans hv'.symm) (by rw [hLv]; exact hΔ)`. Use `⟨Ψ, hΨ, fun h hh g hg v' v => ?_⟩` and prove the remaining obligations. Use `hΨe h hh g hg v' v` as an intermediate fact. Simplify `this` using `[subst2_mul]`.
-/
theorem exists_joint_intertwiner : ∀ (N n : ℕ) (hn : n ≤ N) (ν : Fin N → ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [FiniteDimensional ℂ H'] (τ' : Matrix (Fin N) (Fin N) ℂ → (H' →L[ℂ] H')), Antitone ν → (∀ b : Fin N, n ≤ (b : ℕ) → ν b = 0) → IsURepOn (UJset (allPos n)) τ → IsKTypeOf (allPos n) τ (fun a => (ν (Fin.castLE hn a) : ℝ)) ⊤ → IsURepOn (UJset (allPos N)) τ' → IsKTypeOf (allPos N) τ' (fun b => (ν b : ℝ)) ⊤ → ∃ Ψ : H' →ₗ[ℂ] H →ₗ[ℂ] MvPolynomial (Fin N × Fin n) ℂ, Ψ ≠ 0 ∧ ∀ h ∈ UJset (allPos N), ∀ g ∈ UJset (allPos n), ∀ v' v, Ψ (τ' h v') (τ g v) = subst2 h g (Ψ v' v) := by
  intro N n hn ν H _ _ _ τ H' _ _ _ τ' hν hz hτ hK hτ' hK'
  obtain ⟨Δ, hΔ, hU, hD⟩ := GlobalTheory.T.exists_jointHighestWeight_leadingMinorProduct N n hn ν hν hz
  have hsw : ∀ Q : MvPolynomial (Fin N × Fin n) ℂ,
      rename (Prod.swap : Fin n × Fin N → _) (rename Prod.swap Q) = Q := fun Q => by
    rw [rename_rename]; simp
  have hinj : Function.Injective
      (rename (Prod.swap : Fin n × Fin N → Fin N × Fin n) : MvPolynomial _ ℂ → MvPolynomial _ ℂ) :=
    rename_injective _ Prod.swap_injective
  obtain ⟨L', hL', v₀', hv'⟩ := GlobalTheory.T.exists_unitaryGroup_intertwiner_of_highest_weight_polynomial N (Fin n) ν H' τ' Δ hτ' hK' hΔ
    (fun g hg => by rw [← subst2_one_right, hU g 1 hg (isUpperUnitri_one n)])
    (fun d => by
      have := hD d (fun _ => 1)
      rw [Matrix.diagonal_one, subst2_one_right] at this
      simpa using this)
  obtain ⟨L, hL, v₀, hv⟩ := GlobalTheory.T.exists_unitaryGroup_intertwiner_of_highest_weight_polynomial n (Fin N) (fun a => ν (Fin.castLE hn a)) H τ
    (rename Prod.swap Δ) hτ hK
    (fun h => hΔ (by rw [← hsw Δ, h, map_zero]))
    (fun g hg => hinj (by rw [← subst2_one_left, hsw, hU 1 g (isUpperUnitri_one N) hg]))
    (fun e => hinj (by
      have := hD (fun _ => 1) e
      rw [Matrix.diagonal_one] at this
      rw [← subst2_one_left, map_smul, hsw, this]
      simp))
  have hLv : ((rename (Prod.swap : Fin n × Fin N → Fin N × Fin n)).toLinearMap.comp L) v₀ = Δ := by
    show rename Prod.swap (L v₀) = Δ
    rw [hv, hsw]
  obtain ⟨Ψ, hΨ, hΨe⟩ := exists_bilinear (UJset (allPos n)) (UJset (allPos N))
    (fun g => (τ g).toLinearMap) (fun h => (τ' h).toLinearMap)
    (fun g => (subst2 (1 : Matrix (Fin N) (Fin N) ℂ) g).toLinearMap)
    (fun h => (subst2 h (1 : Matrix (Fin n) (Fin n) ℂ)).toLinearMap)
    (fun g h x => by simp [subst2_mul])
    (fun U hS => hK.2.2.1 U le_top fun g hg => hS g ((mem_K_iff g).1 hg))
    (fun U hS => hK'.2.2.1 U le_top fun g hg => hS g ((mem_K_iff g).1 hg))
    ((rename (Prod.swap : Fin n × Fin N → Fin N × Fin n)).toLinearMap.comp L) L'
    (fun g hg u => by
      show rename Prod.swap (L (τ g u)) = subst2 1 g (rename Prod.swap (L u))
      rw [hL g hg u, subst2_one_left])
    (fun h hh u => by
      show L' (τ' h u) = subst2 h 1 (L' u)
      rw [hL' h hh u, subst2_one_right])
    v₀ v₀' (hLv.trans hv'.symm) (by rw [hLv]; exact hΔ)
  refine ⟨Ψ, hΨ, fun h hh g hg v' v => ?_⟩
  have := hΨe h hh g hg v' v
  simpa [subst2_mul] using this

end GlobalTheory.CompactHoweJoint

end
