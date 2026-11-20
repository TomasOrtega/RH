import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexifiedDerivedActionIsLieAction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtremalLowestKtypeKilledByCompactRoots

open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HolRead.KCpt

open GlobalTheory.HolDict GlobalTheory.HolDict.BorelK

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Mt n → (H →L[ℂ] H)}

/- English proof (translation)
Establish `ma : a ∈ negS ε` using `by simp [negS, ha]`. Establish `mb : b ∈ negS ε` using `by simp [negS, hb]`. Establish `h1 : revNeg ε a = (revOn ε ⟨a, ma⟩ : Fin n)` using `Equiv.Perm.ofSubtype_apply_of_mem _ ma`. Establish `h2 : revNeg ε b = (revOn ε ⟨b, mb⟩ : Fin n)` using `Equiv.Perm.ofSubtype_apply_of_mem _ mb`. Rewrite using `[h1, h2]`.

Establish `h3 : (⟨b, mb⟩ : {x // x ∈ negS ε}) < ⟨a, ma⟩` using `h`. Establish `h4` using `((negS ε).orderIsoOfFin rfl).symm.strictMono h3`. Conclude with `((negS ε).orderIsoOfFin rfl).strictMono (Fin.rev_lt_rev.2 h4)`.
-/
theorem revNeg_lt {a b : Fin n} (ha : ε a = false) (hb : ε b = false) (h : b < a) : revNeg ε a < revNeg ε b := by
  have ma : a ∈ negS ε := by simp [negS, ha]
  have mb : b ∈ negS ε := by simp [negS, hb]
  have h1 : revNeg ε a = (revOn ε ⟨a, ma⟩ : Fin n) := Equiv.Perm.ofSubtype_apply_of_mem _ ma
  have h2 : revNeg ε b = (revOn ε ⟨b, mb⟩ : Fin n) := Equiv.Perm.ofSubtype_apply_of_mem _ mb
  rw [h1, h2]
  have h3 : (⟨b, mb⟩ : {x // x ∈ negS ε}) < ⟨a, ma⟩ := h
  have h4 := ((negS ε).orderIsoOfFin rfl).symm.strictMono h3
  exact ((negS ε).orderIsoOfFin rfl).strictMono (Fin.rev_lt_rev.2 h4)

/- English proof (translation)
Establish `hh : (Formalism.REAL.Jm ε).IsHermitian` using `Formalism.REAL.Jm_conjTranspose ε`. Establish `z0 : ∀ x : H, dRepC (Formalism.REAL.Jm ε) σ 0 x = 0`. Introduce `x`. Simplify using `[dRepC, conjH, dRep]`. Establish `l1 : ∀ (s : ℂ) Z, dRepC (Formalism.REAL.Jm ε) σ (s • Z) v = s • dRepC (Formalism.REAL.Jm ε) σ Z v`.

Introduce `s Z`. Use `LieAct.dRepC_lin hh det_Jm hσ hs s Z 0` as an intermediate fact. Rewrite `this` using `[add_zero, z0, add_zero]`. Then use the resulting hypothesis. Establish `l2 : ∀ (s : ℂ) Z, dRepC (Formalism.REAL.Jm ε) σ Z (s • v) = s • dRepC (Formalism.REAL.Jm ε) σ Z v`. Introduce `s Z`.

Use `LieAct.dRepC_vec (π := σ) hh det_Jm hs hs (s - 1) Z` as an intermediate fact. Rewrite `this` using `[sub_smul, one_smul, sub_add_cancel, sub_smul, one_smul, sub_add_cancel]`. Conclude with `this`. Introduce `θ hθ`. Establish `hinv : (diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I))⁻¹ = diagonal fun a => Complex.exp (-((θ a : ℂ) * Complex.I))`.

Apply `Matrix.inv_eq_left_inv` to reduce the goal to its premises. Rewrite using `[diagonal_mul_diagonal, ← diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `b`. Rewrite using `[← Complex.exp_add]`.

Simplify using the standard rewrite rules. Establish `e : (diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I)) * Matrix.single a c (1 : ℂ) * (diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I))⁻¹ = Complex.exp ((θ a : ℂ) * Complex.I + -((θ c : ℂ) * Complex.I)) • Matrix.single a c (1 : ℂ)`. Rewrite using `[hinv]`. Use extensionality with `i j`. Simplify using `only [mul_diagonal, diagonal_mul, Matrix.smul_apply, Matrix.single_apply]`.

Distinguish the cases in `h' : a = i ∧ c = j`. Take `⟨rfl, rfl⟩` from `h'`. Simplify using `[Complex.exp_add]`. Simplify using `[h']`. Rewrite using `[LieAct.rep_dRepC hh det_Jm hσ hs (kset_uj hθ), e, hv θ hθ, l2, l1, smul_smul, ← Complex.exp_add]`.

Use `congr 2`. Simplify using `[Formalism.REAL.root, Pi.single_apply, add_mul, Finset.sum_add_distrib, sub_eq_add_neg]`.
-/
theorem isWtOn_root (hσ : IsURepOn (UJset ε) σ) {μ : Fin n → ℝ} {v : H}
    (hs : SmoothVec (lieH (Formalism.REAL.Jm ε)) σ v) (hv : IsWtOn (Formalism.REAL.Kset ε) σ μ v) (a c : Fin n) :
    IsWtOn (Formalism.REAL.Kset ε) σ (μ + Formalism.REAL.root a c) (dRepC (Formalism.REAL.Jm ε) σ (Matrix.single a c 1) v) := by
  have hh : (Formalism.REAL.Jm ε).IsHermitian := Formalism.REAL.Jm_conjTranspose ε
  have z0 : ∀ x : H, dRepC (Formalism.REAL.Jm ε) σ 0 x = 0 := by
    intro x
    simp [dRepC, conjH, dRep]
  have l1 : ∀ (s : ℂ) Z, dRepC (Formalism.REAL.Jm ε) σ (s • Z) v = s • dRepC (Formalism.REAL.Jm ε) σ Z v := by
    intro s Z
    have := LieAct.dRepC_lin hh det_Jm hσ hs s Z 0
    rwa [add_zero, z0, add_zero] at this
  have l2 : ∀ (s : ℂ) Z, dRepC (Formalism.REAL.Jm ε) σ Z (s • v) = s • dRepC (Formalism.REAL.Jm ε) σ Z v := by
    intro s Z
    have := LieAct.dRepC_vec (π := σ) hh det_Jm hs hs (s - 1) Z
    rw [sub_smul, one_smul, sub_add_cancel, sub_smul, one_smul, sub_add_cancel] at this
    exact this
  intro θ hθ
  have hinv : (diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I))⁻¹ =
      diagonal fun a => Complex.exp (-((θ a : ℂ) * Complex.I)) := by
    apply Matrix.inv_eq_left_inv
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext b
    rw [← Complex.exp_add]; simp
  have e : (diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I)) * Matrix.single a c (1 : ℂ) *
      (diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I))⁻¹ =
      Complex.exp ((θ a : ℂ) * Complex.I + -((θ c : ℂ) * Complex.I)) • Matrix.single a c (1 : ℂ) := by
    rw [hinv]
    ext i j
    simp only [mul_diagonal, diagonal_mul, Matrix.smul_apply, Matrix.single_apply]
    by_cases h' : a = i ∧ c = j
    · obtain ⟨rfl, rfl⟩ := h'
      simp [Complex.exp_add]
    · simp [h']
  rw [LieAct.rep_dRepC hh det_Jm hσ hs (kset_uj hθ), e, hv θ hθ, l2, l1, smul_smul, ← Complex.exp_add]
  congr 2
  simp [Formalism.REAL.root, Pi.single_apply, add_mul, Finset.sum_add_distrib, sub_eq_add_neg]

/- English proof (translation)
Establish `hε : ∀ b, ε ((revNeg ε).symm b) = ε b` using `fun b => by`. Rewrite using `[← eps_revNeg ε ((revNeg ε).symm b), Equiv.apply_symm_apply]`. Establish `h1` using `isWtOn_perm hσ (revNeg ε).symm hε (isWtOn_root hσ hs hw a c)`. Establish `e : (fun b => ((fun a => Formalism.QuantumDeterminants.lowK ε lam (revNeg ε a)) + Formalism.REAL.root a c) ((revNeg ε).symm b)) = Formalism.QuantumDeterminants.lowK ε lam + Formalism.REAL.root (revNeg ε a) (revNeg ε c)`. Use function extensionality and compare the values at `b`.

Simplify using `[Formalism.REAL.root, Pi.single_apply, Equiv.symm_apply_eq]`. Rewrite `h1` using `[e]`. Establish `h2` using `orth_of_not_cdom hσ h1 (not_cdom _ hlt)`. Establish `hK` using `pM_mem (revNeg ε).symm hε`. Establish `h3 : ∀ x ∈ lowKSub ε lam σ, ⟪dRepC (Formalism.REAL.Jm ε) σ (Matrix.single a c 1) v, x⟫_ℂ = 0`.

Introduce `x hx`. Rewrite using `[← inner_rep hσ hK]`. Conclude with `h2 _ (stable_sSup _ hK x hx)`. Conclude with `inner_self_eq_zero.1 (inner_dRepC stable_sSup h3 hv hac)`.
-/
theorem killed {lam : Fin n → ℝ} (hσ : IsURepOn (UJset ε) σ) {v : H} (hv : v ∈ lowKSub ε lam σ)
    (hs : SmoothVec (lieH (Formalism.REAL.Jm ε)) σ v)
    (hw : IsWtOn (Formalism.REAL.Kset ε) σ (fun a => Formalism.QuantumDeterminants.lowK ε lam (revNeg ε a)) v) {a c : Fin n} (hac : ε a = ε c)
    (hlt : revNeg ε a < revNeg ε c) : dRepC (Formalism.REAL.Jm ε) σ (Matrix.single a c 1) v = 0 := by
  have hε : ∀ b, ε ((revNeg ε).symm b) = ε b := fun b => by
    rw [← eps_revNeg ε ((revNeg ε).symm b), Equiv.apply_symm_apply]
  have h1 := isWtOn_perm hσ (revNeg ε).symm hε (isWtOn_root hσ hs hw a c)
  have e : (fun b => ((fun a => Formalism.QuantumDeterminants.lowK ε lam (revNeg ε a)) + Formalism.REAL.root a c) ((revNeg ε).symm b)) =
      Formalism.QuantumDeterminants.lowK ε lam + Formalism.REAL.root (revNeg ε a) (revNeg ε c) := by
    funext b
    simp [Formalism.REAL.root, Pi.single_apply, Equiv.symm_apply_eq]
  rw [e] at h1
  have h2 := orth_of_not_cdom hσ h1 (not_cdom _ hlt)
  have hK := pM_mem (revNeg ε).symm hε
  have h3 : ∀ x ∈ lowKSub ε lam σ, ⟪dRepC (Formalism.REAL.Jm ε) σ (Matrix.single a c 1) v, x⟫_ℂ = 0 := by
    intro x hx
    rw [← inner_rep hσ hK]
    exact h2 _ (stable_sSup _ hK x hx)
  exact inner_self_eq_zero.1 (inner_dRepC stable_sSup h3 hv hac)

/- English proof (translation)
Introduce `n H _ _ ε lam π hπ v hv hs hw a b hab X hX Y hY hE`. Rewrite using `[← LieAct.dRepC_parts (G := Formalism.REAL.Jm ε) det_Jm hX hY, hE]`. Break down `hab with ⟨ha, hb, h⟩ | ⟨ha, hb, h⟩` into its components or cases. Conclude with `killed hπ hv hs hw (ha.trans hb.symm) (by rwa [revNeg_of_pos ε ha, revNeg_of_pos ε hb])`. Conclude with `killed hπ hv hs hw (ha.trans hb.symm) (revNeg_lt ha hb h)`.
-/
theorem extremal_killed_compact : ∀ (n : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin n → Bool) (lam : Fin n → ℝ) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) π → ∀ v ∈ lowKSub ε lam π, SmoothVec {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0} π v → IsWtOn (Formalism.REAL.Kset ε) π (fun a => Formalism.QuantumDeterminants.lowK ε lam (revNeg ε a)) v → ∀ a b : Fin n, ((ε a = true ∧ ε b = true ∧ a < b) ∨ (ε a = false ∧ ε b = false ∧ b < a)) → ∀ X ∈ {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0}, ∀ Y ∈ {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0}, X + Complex.I • Y = Matrix.single a b 1 → dRep π X v + Complex.I • dRep π Y v = 0 := by
  intro n H _ _ ε lam π hπ v hv hs hw a b hab X hX Y hY hE
  rw [← LieAct.dRepC_parts (G := Formalism.REAL.Jm ε) det_Jm hX hY, hE]
  rcases hab with ⟨ha, hb, h⟩ | ⟨ha, hb, h⟩
  · exact killed hπ hv hs hw (ha.trans hb.symm) (by rwa [revNeg_of_pos ε ha, revNeg_of_pos ε hb])
  · exact killed hπ hv hs hw (ha.trans hb.symm) (revNeg_lt ha hb h)

end GlobalTheory.HolRead.KCpt
