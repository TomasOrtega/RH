import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.GoodSet

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section Tri

variable {k : Type} [Field k]

local notation "M2" => Matrix (Fin 2) (Fin 2) k

/- English proof (translation)
Establish `hd : (M : M2).det ≠ 0` using `((Matrix.isUnit_iff_isUnit_det _).1 M.isUnit).ne_zero`. Rewrite `hd` using `[Matrix.det_fin_two, h, mul_zero, sub_zero]`. Use `fin_cases j`. Conclude with `left_ne_zero_of_mul hd`. Conclude with `right_ne_zero_of_mul hd`.
-/
private theorem tri_diag_ne (M : GL (Fin 2) k) (h : (M : M2) 1 0 = 0) (j : Fin 2) :
    (M : M2) j j ≠ 0 := by
  have hd : (M : M2).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 M.isUnit).ne_zero
  rw [Matrix.det_fin_two, h, mul_zero, sub_zero] at hd
  fin_cases j
  · exact left_ne_zero_of_mul hd
  · exact right_ne_zero_of_mul hd

/- English proof (translation)
Use `⟨fun i => { toFun := fun s => Units.mk0 _ (tri_diag_ne (ρ s) (hT s) i) map_one' := ?_ map_mul' := ?_ }, fun i s => rfl⟩` and prove the remaining obligations. Use `ext`. Simplify using the standard rewrite rules. Introduce `s t`. Use `ext`.

Simplify using `only [map_mul, Units.val_mul, Units.val_mk0, Matrix.mul_apply, Fin.sum_univ_two]`. Apply the tactic sequence `fin_cases i <;> simp [hT]`.
-/
private theorem tri_chars {W : Type} [Group W] (ρ : W →* GL (Fin 2) k)
    (hT : ∀ s, (ρ s : M2) 1 0 = 0) :
    ∃ η : Fin 2 → W →* kˣ, ∀ i s, (η i s : k) = (ρ s : M2) i i := by
  refine ⟨fun i =>
    { toFun := fun s => Units.mk0 _ (tri_diag_ne (ρ s) (hT s) i)
      map_one' := ?_
      map_mul' := ?_ }, fun i s => rfl⟩
  · ext; simp
  · intro s t
    ext
    simp only [map_mul, Units.val_mul, Units.val_mk0, Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> simp [hT]

/- English proof (translation)
Establish `hc : ((P * M * P⁻¹ : GL (Fin 2) k) : M2).charpoly = (M : M2).charpoly`. Simplify using `using Matrix.charpoly_units_conj P (M : M2)`. Rewrite using `[← hc, Matrix.charpoly_fin_two, Matrix.det_fin_two, Matrix.trace_fin_two, h, Fin.prod_univ_two]`. Simplify using `only [mul_zero, sub_zero, C_add, C_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem tri_charpoly (P M : GL (Fin 2) k)
    (h : ((P * M * P⁻¹ : GL (Fin 2) k) : M2) 1 0 = 0) :
    (M : M2).charpoly = ∏ i, (X - C (((P * M * P⁻¹ : GL (Fin 2) k) : M2) i i)) := by
  have hc : ((P * M * P⁻¹ : GL (Fin 2) k) : M2).charpoly = (M : M2).charpoly := by
    simpa using Matrix.charpoly_units_conj P (M : M2)
  rw [← hc, Matrix.charpoly_fin_two, Matrix.det_fin_two, Matrix.trace_fin_two, h,
    Fin.prod_univ_two]
  simp only [mul_zero, sub_zero, C_add, C_mul]
  ring

/- English proof (translation)
Take `⟨μ, hμ⟩` from `Module.End.exists_eigenvalue (Matrix.toLin' (M : M2))`. Take `⟨v, hv⟩` from `hμ.exists_hasEigenvector`. Establish `hMv : (M : M2).mulVec v = μ • v`. Simplify `hv.apply_eq_smul` using `[Matrix.toLin'_apply]`. Establish `hv0 : v ≠ 0` using `hv.2`.

Choose the witnesses or unpack the hypotheses as in `⟨R, hR⟩ : ∃ R : GL (Fin 2) k, ∀ i, (R : M2) i 0 = v i := by`. Distinguish the cases in `h0 : v 0 = 0`. Apply the tactic sequence `have h1 : v 1 ≠ 0 := fun h1 => hv0 (by ext i; fin_cases i <;> simp [h0, h1])`. Use `⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![v 0, 1; v 1, 0] (by simp [Matrix.det_fin_two, h1]), ?_⟩` and prove the remaining obligations. Introduce `i`.

Apply the tactic sequence `fin_cases i <;> simp [Matrix.GeneralLinearGroup.mkOfDetNeZero]`. Use `⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![v 0, 0; v 1, 1] (by simp [Matrix.det_fin_two, h0]), ?_⟩` and prove the remaining obligations. Introduce `i`. Apply the tactic sequence `fin_cases i <;> simp [Matrix.GeneralLinearGroup.mkOfDetNeZero]`. Use `⟨R⁻¹, ?_⟩` and prove the remaining obligations.

Establish `hRT : (R : M2) * ((R⁻¹ * M * R⁻¹⁻¹ : GL (Fin 2) k) : M2) = (M : M2) * (R : M2)`. Rewrite using `[← Units.val_mul, ← Units.val_mul]`. Use `congr 1`. Use `group`. Use `set T : M2 := ((R⁻¹ * M * R⁻¹⁻¹ : GL (Fin 2) k) : M2) with hTdef`.

Establish `hcol : (R : M2).mulVec ![T 0 0 - μ, T 1 0] = 0`. Use extensionality with `i`. Establish `h1 : ((R : M2) * T) i 0 = ((M : M2) * (R : M2)) i 0` using `by rw [hRT]`. Establish `h2 : ((M : M2) * (R : M2)) i 0 = μ * v i`. Use `congrFun hMv i` as an intermediate fact.

Simplify using `only [Matrix.mul_apply, hR, Pi.smul_apply, smul_eq_mul] at this ⊢`. Simplify `this` using `[Matrix.mulVec, dotProduct]`. Rewrite `h1` using `[h2, Matrix.mul_apply, Fin.sum_univ_two, hR]`. Simplify using `only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hR, Pi.zero_apply]`. Simplify using `only [Matrix.cons_val_zero, Matrix.cons_val_one]`.

Take the linear combination `h1`. Establish `hdet : (R : M2).det ≠ 0` using `((Matrix.isUnit_iff_isUnit_det _).1 R.isUnit).ne_zero`. Use `Matrix.eq_zero_of_mulVec_eq_zero hdet hcol` as an intermediate fact. Simplify using `using congrFun this 1`.
-/
private theorem tri_exists [IsAlgClosed k] (M : GL (Fin 2) k) :
    ∃ Q : GL (Fin 2) k, ((Q * M * Q⁻¹ : GL (Fin 2) k) : M2) 1 0 = 0 := by
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (Matrix.toLin' (M : M2))
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hMv : (M : M2).mulVec v = μ • v := by
    simpa [Matrix.toLin'_apply] using hv.apply_eq_smul
  have hv0 : v ≠ 0 := hv.2
  obtain ⟨R, hR⟩ : ∃ R : GL (Fin 2) k, ∀ i, (R : M2) i 0 = v i := by
    by_cases h0 : v 0 = 0
    · have h1 : v 1 ≠ 0 := fun h1 => hv0 (by ext i; fin_cases i <;> simp [h0, h1])
      refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![v 0, 1; v 1, 0]
        (by simp [Matrix.det_fin_two, h1]), ?_⟩
      intro i
      fin_cases i <;> simp [Matrix.GeneralLinearGroup.mkOfDetNeZero]
    · refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![v 0, 0; v 1, 1]
        (by simp [Matrix.det_fin_two, h0]), ?_⟩
      intro i
      fin_cases i <;> simp [Matrix.GeneralLinearGroup.mkOfDetNeZero]
  refine ⟨R⁻¹, ?_⟩
  have hRT : (R : M2) * ((R⁻¹ * M * R⁻¹⁻¹ : GL (Fin 2) k) : M2) = (M : M2) * (R : M2) := by
    rw [← Units.val_mul, ← Units.val_mul]
    congr 1
    group
  set T : M2 := ((R⁻¹ * M * R⁻¹⁻¹ : GL (Fin 2) k) : M2) with hTdef
  have hcol : (R : M2).mulVec ![T 0 0 - μ, T 1 0] = 0 := by
    ext i
    have h1 : ((R : M2) * T) i 0 = ((M : M2) * (R : M2)) i 0 := by rw [hRT]
    have h2 : ((M : M2) * (R : M2)) i 0 = μ * v i := by
      have := congrFun hMv i
      simp only [Matrix.mul_apply, hR, Pi.smul_apply, smul_eq_mul] at this ⊢
      simpa [Matrix.mulVec, dotProduct] using this
    rw [h2, Matrix.mul_apply, Fin.sum_univ_two, hR] at h1
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hR, Pi.zero_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination h1
  have hdet : (R : M2).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 R.isUnit).ne_zero
  have := Matrix.eq_zero_of_mulVec_eq_zero hdet hcol
  simpa using congrFun this 1

private def triSub : Subgroup (GL (Fin 2) k) where
  carrier := {M | (M : M2) 1 0 = 0}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    simp [Matrix.mul_apply, Fin.sum_univ_two, ha, hb]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    simp [Matrix.coe_units_inv, Matrix.inv_def, Matrix.adjugate_fin_two, ha]

/- English proof (translation)
Distinguish the cases in `hsep : ∃ i ∈ I, (τ 0 i : k) ≠ (τ 1 i : k)`. Take `⟨i, hi, hne⟩` from `hsep`. Use `⟨g, fun s => ?_, fun s hs j => by rw [hg s hs]; simp⟩` and prove the remaining obligations. Establish `hc` using `hg (s * i * s⁻¹) (hI.conj_mem i hi s)`. Establish `hτ : ∀ j, (τ j (s * i * s⁻¹) : k) = (τ j i : k)`.

Introduce `j`. Simplify using `[mul_comm]`. Establish `hcomm : (g * ρ s * g⁻¹) * (g * ρ i * g⁻¹) = (g * ρ (s * i * s⁻¹) * g⁻¹) * (g * ρ s * g⁻¹)`. Simplify using `only [map_mul, map_inv]`. Use `group`.

Establish `hm` using `congrArg (fun x : GL (Fin 2) k => (x : M2) 1 0) hcomm`. Simplify using `only [Units.val_mul (g * ρ s * g⁻¹)] at hm`. Rewrite `hm` using `[Units.val_mul (g * ρ (s * i * s⁻¹) * g⁻¹), hg i hi, hc]`. Simplify using `only [Matrix.mul_diagonal, Matrix.diagonal_mul, hτ] at hm`. Establish `: (((g * ρ s * g⁻¹ : GL (Fin 2) k) : M2) 1 0) * ((τ 0 i : k) - (τ 1 i : k)) = 0`.

Take the linear combination `hm`. Conclude with `(mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hne)`. Use `push_neg at hsep`. Take `⟨Q, hQ⟩` from `tri_exists (g * ρ φ * g⁻¹)`. Establish `hsc : ∀ s ∈ I, ((Q * g) * ρ s * (Q * g)⁻¹ : GL (Fin 2) k) = g * ρ s * g⁻¹`.

Introduce `s hs`. Establish `hz : ((g * ρ s * g⁻¹ : GL (Fin 2) k) : M2) = (τ 0 s : k) • (1 : M2)`. Rewrite using `[hg s hs]`. Use extensionality with `a b`. Apply the tactic sequence `fin_cases a <;> fin_cases b <;> simp [hsep s hs]`.

Establish `hcm : Q * (g * ρ s * g⁻¹) = (g * ρ s * g⁻¹) * Q`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.val_mul Q (g * ρ s * g⁻¹), Units.val_mul (g * ρ s * g⁻¹) Q, hz]`. Simplify using the standard rewrite rules. Combine the equalities or inequalities in the displayed calculation.

Use `⟨Q * g, fun s => ?_, fun s hs j => ?_⟩` and prove the remaining obligations. Take `⟨n, i, hi, rfl⟩` from `hgen s`. Establish `hφ : (Q * g) * ρ φ * (Q * g)⁻¹ ∈ (triSub : Subgroup (GL (Fin 2) k))`. Express the relevant statement in the definitionally equal form `(((Q * g) * ρ φ * (Q * g)⁻¹ : GL (Fin 2) k) : M2) 1 0 = 0`. Establish `: ((Q * g) * ρ φ * (Q * g)⁻¹ : GL (Fin 2) k) = Q * (g * ρ φ * g⁻¹) * Q⁻¹` using `by group`.

Rewrite using `[this]`. Conclude with `hQ`. Establish `hi' : (Q * g) * ρ i * (Q * g)⁻¹ ∈ (triSub : Subgroup (GL (Fin 2) k))`. Express the relevant statement in the definitionally equal form `(((Q * g) * ρ i * (Q * g)⁻¹ : GL (Fin 2) k) : M2) 1 0 = 0`. Rewrite using `[hsc i hi, hg i hi]`.

Simplify using the standard rewrite rules. Establish `hall : (Q * g) * ρ (φ ^ n * i) * (Q * g)⁻¹ = ((Q * g) * ρ φ * (Q * g)⁻¹) ^ n * ((Q * g) * ρ i * (Q * g)⁻¹)`. Rewrite using `[map_mul, map_zpow]`. Use `(MulAut.conj (Q * g)).toMonoidHom.map_zpow (ρ φ) n` as an intermediate fact. Simplify using `only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply] at this`.

Rewrite using `[← this]`. Use `group`. Establish `: (Q * g) * ρ (φ ^ n * i) * (Q * g)⁻¹ ∈ (triSub : Subgroup (GL (Fin 2) k))`. Rewrite using `[hall]`. Conclude with `mul_mem (zpow_mem hφ n) hi'`.

Conclude with `this`. Rewrite using `[hsc s hs, hg s hs]`. Simplify using the standard rewrite rules.
-/
private theorem tri_core [IsAlgClosed k] {W : Type} [Group W] (ρ : W →* GL (Fin 2) k)
    (τ : Fin 2 → W →* kˣ) (I : Subgroup W) (hI : I.Normal) (φ : W)
    (hgen : ∀ s, ∃ n : ℤ, ∃ i ∈ I, s = φ ^ n * i) (g : GL (Fin 2) k)
    (hg : ∀ s ∈ I, ((g * ρ s * g⁻¹ : GL (Fin 2) k) : M2) = Matrix.diagonal fun i => (τ i s : k)) :
    ∃ P : GL (Fin 2) k, (∀ s, ((P * ρ s * P⁻¹ : GL (Fin 2) k) : M2) 1 0 = 0) ∧
      ∀ s ∈ I, ∀ j, ((P * ρ s * P⁻¹ : GL (Fin 2) k) : M2) j j = (τ j s : k) := by
  by_cases hsep : ∃ i ∈ I, (τ 0 i : k) ≠ (τ 1 i : k)
  · obtain ⟨i, hi, hne⟩ := hsep
    refine ⟨g, fun s => ?_, fun s hs j => by rw [hg s hs]; simp⟩
    have hc := hg (s * i * s⁻¹) (hI.conj_mem i hi s)
    have hτ : ∀ j, (τ j (s * i * s⁻¹) : k) = (τ j i : k) := by
      intro j
      simp [mul_comm]
    have hcomm : (g * ρ s * g⁻¹) * (g * ρ i * g⁻¹) = (g * ρ (s * i * s⁻¹) * g⁻¹) * (g * ρ s * g⁻¹) := by
      simp only [map_mul, map_inv]
      group
    have hm := congrArg (fun x : GL (Fin 2) k => (x : M2) 1 0) hcomm
    simp only [Units.val_mul (g * ρ s * g⁻¹)] at hm
    rw [Units.val_mul (g * ρ (s * i * s⁻¹) * g⁻¹), hg i hi, hc] at hm
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, hτ] at hm
    have : (((g * ρ s * g⁻¹ : GL (Fin 2) k) : M2) 1 0) * ((τ 0 i : k) - (τ 1 i : k)) = 0 := by
      linear_combination hm
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hne)
  · push_neg at hsep
    obtain ⟨Q, hQ⟩ := tri_exists (g * ρ φ * g⁻¹)
    have hsc : ∀ s ∈ I, ((Q * g) * ρ s * (Q * g)⁻¹ : GL (Fin 2) k) =
        g * ρ s * g⁻¹ := by
      intro s hs
      have hz : ((g * ρ s * g⁻¹ : GL (Fin 2) k) : M2) = (τ 0 s : k) • (1 : M2) := by
        rw [hg s hs]
        ext a b
        fin_cases a <;> fin_cases b <;> simp [hsep s hs]
      have hcm : Q * (g * ρ s * g⁻¹) = (g * ρ s * g⁻¹) * Q := by
        apply Units.ext
        rw [Units.val_mul Q (g * ρ s * g⁻¹), Units.val_mul (g * ρ s * g⁻¹) Q, hz]
        simp
      calc ((Q * g) * ρ s * (Q * g)⁻¹ : GL (Fin 2) k)
          = Q * (g * ρ s * g⁻¹) * Q⁻¹ := by group
        _ = g * ρ s * g⁻¹ := by rw [hcm]; group
    refine ⟨Q * g, fun s => ?_, fun s hs j => ?_⟩
    · obtain ⟨n, i, hi, rfl⟩ := hgen s
      have hφ : (Q * g) * ρ φ * (Q * g)⁻¹ ∈ (triSub : Subgroup (GL (Fin 2) k)) := by
        change (((Q * g) * ρ φ * (Q * g)⁻¹ : GL (Fin 2) k) : M2) 1 0 = 0
        have : ((Q * g) * ρ φ * (Q * g)⁻¹ : GL (Fin 2) k) = Q * (g * ρ φ * g⁻¹) * Q⁻¹ := by group
        rw [this]; exact hQ
      have hi' : (Q * g) * ρ i * (Q * g)⁻¹ ∈ (triSub : Subgroup (GL (Fin 2) k)) := by
        change (((Q * g) * ρ i * (Q * g)⁻¹ : GL (Fin 2) k) : M2) 1 0 = 0
        rw [hsc i hi, hg i hi]
        simp
      have hall : (Q * g) * ρ (φ ^ n * i) * (Q * g)⁻¹ =
          ((Q * g) * ρ φ * (Q * g)⁻¹) ^ n * ((Q * g) * ρ i * (Q * g)⁻¹) := by
        rw [map_mul, map_zpow]
        have := (MulAut.conj (Q * g)).toMonoidHom.map_zpow (ρ φ) n
        simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply] at this
        rw [← this]
        group
      have : (Q * g) * ρ (φ ^ n * i) * (Q * g)⁻¹ ∈ (triSub : Subgroup (GL (Fin 2) k)) := by
        rw [hall]; exact mul_mem (zpow_mem hφ n) hi'
      exact this
    · rw [hsc s hs, hg s hs]
      simp

end Tri

/- English proof (translation)
Introduce `L Ω _ _ _ _ _ l _ r _ τ w A h hD`. Take `⟨g, hg⟩` from `hD`. Establish `hdegc : ∀ (s : Weil h) (i : Ine (F` using `L) A), deg (s * ineIncl h i * s⁻¹) = 0 := by`. Introduce `s i`. Rewrite using `[deg_mul, deg_mul, deg_ineIncl, deg_inv]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hN : (ineIncl h).range.Normal`. Use `⟨?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨i, rfl⟩ s`. Use `⟨inePart (deg_frob (h := h)) (s * ineIncl h i * s⁻¹), ?_⟩` and prove the remaining obligations.

Rewrite using `[ineIncl_inePart, hdegc]`. Simplify using the standard rewrite rules. Establish `hgen : ∀ s : Weil h, ∃ n : ℤ, ∃ i ∈ (ineIncl h).range, s = frob h ^ n * i`. Introduce `s`. Use `⟨deg s, _, ⟨inePart (deg_frob (h := h)) s, rfl⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[ineIncl_inePart, mul_inv_cancel_left]`. Take `⟨P, hP1, hP2⟩` from `tri_core (r.comp (Weil h).subtype) (fun i => (τ i).comp (Weil h).subtype) (ineIncl h).range hN (frob h) hgen g (by`. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `hg i i.2)`. Take `⟨η, hη⟩` from `tri_chars ((MulAut.conj P).toMonoidHom.comp (r.comp (Weil h).subtype)) hP1`.

Use `⟨η, fun i s => ?_, fun s => ?_⟩` and prove the remaining obligations. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[hη]`. Conclude with `hP2 _ ⟨s, rfl⟩ i`. Use `tri_charpoly P (r s) (hP1 s)` as an intermediate fact.

Rewrite using `[this]`. Simplify using `only [hη]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.V.Z.Sym.Ga.flagAway :
    ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (r : G L Ω →* GL (Fin 2) (Qbar l)), Continuous r → ∀ τ : Fin 2 → G L Ω →* (Qbar l)ˣ, ∀ (w : Plc L) (A : ValuationSubring Ω) (h : IsPlaceOver A w), IsDiagOn r (Ine (F := L) A) τ → ∃ η : Fin 2 → Weil h →* (Qbar l)ˣ, (∀ i (s : Ine (F := L) A), η i (ineIncl h s) = τ i s) ∧ ∀ s : Weil h, (r s : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly = ∏ i, (X - C (η i s : Qbar l)) := by
  intro L Ω _ _ _ _ _ l _ r _ τ w A h hD
  obtain ⟨g, hg⟩ := hD
  have hdegc : ∀ (s : Weil h) (i : Ine (F := L) A), deg (s * ineIncl h i * s⁻¹) = 0 := by
    intro s i
    rw [deg_mul, deg_mul, deg_ineIncl, deg_inv]
    ring
  have hN : (ineIncl h).range.Normal := by
    refine ⟨?_⟩
    rintro _ ⟨i, rfl⟩ s
    refine ⟨inePart (deg_frob (h := h)) (s * ineIncl h i * s⁻¹), ?_⟩
    rw [ineIncl_inePart, hdegc]
    simp
  have hgen : ∀ s : Weil h, ∃ n : ℤ, ∃ i ∈ (ineIncl h).range, s = frob h ^ n * i := by
    intro s
    refine ⟨deg s, _, ⟨inePart (deg_frob (h := h)) s, rfl⟩, ?_⟩
    rw [ineIncl_inePart, mul_inv_cancel_left]
  obtain ⟨P, hP1, hP2⟩ := tri_core (r.comp (Weil h).subtype)
    (fun i => (τ i).comp (Weil h).subtype) (ineIncl h).range hN (frob h) hgen g (by
      rintro _ ⟨i, rfl⟩
      exact hg i i.2)
  obtain ⟨η, hη⟩ := tri_chars ((MulAut.conj P).toMonoidHom.comp (r.comp (Weil h).subtype)) hP1
  refine ⟨η, fun i s => ?_, fun s => ?_⟩
  · apply Units.ext
    rw [hη]
    exact hP2 _ ⟨s, rfl⟩ i
  · have := tri_charpoly P (r s) (hP1 s)
    rw [this]
    simp only [hη]
    rfl
