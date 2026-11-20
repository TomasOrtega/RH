import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.VacuumIwasawa.EmEqInr

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Avac

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

abbrev Jm (n : ℕ) (ε : AE F E) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E) := Matrix.fromBlocks 0 1 (ε • 1) 0

/- English proof (translation)
Establish `e1 : (incM F d.b.1).map (cA σ) = incM F (d.b.1.map σ)`. Use extensionality with `i j`. Simplify using `[incM, cA, inclR, Algebra.TensorProduct.map_tmul]`. Establish `e2 : dbl (incM F d.Y.J) = incM F (dbl d.Y.J)`. Simplify using `[dbl, incM, Matrix.fromBlocks_map, Matrix.map_neg]`.

Establish `key : incM F (d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ) = (incM F d.b.1)ᵀ * incM F (dbl d.Y.J) * incM F (d.b.1.map σ)`. Simplify using `only [incM, Matrix.map_mul, Matrix.transpose_map]`. Rewrite using `[e1, e2, ← key, h]`. Use extensionality with `(i | i) (j | j)`. Simplify using `[incM, Jm]`.

Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using `[incM, Jm]`. Simplify using `[incM, Jm, Matrix.one_apply_ne hij]`. Distinguish the cases in `hij : i = j`.

Substitute `hij` using the available equality. Simplify using `[incM, Jm, map_intCast]`. Simplify using `[incM, Jm, Matrix.one_apply_ne hij]`. Simplify using `[incM, Jm]`.
-/
theorem frame_formE (d : SD σ) (ε : ℤˣ)
    (h : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) :
    (incM F d.b.1)ᵀ * dbl (incM F d.Y.J) * (incM F d.b.1).map (cA σ) = Jm d.n ((ε : ℤ) : AE F E) := by
  have e1 : (incM F d.b.1).map (cA σ) = incM F (d.b.1.map σ) := by
    ext i j
    simp [incM, cA, inclR, Algebra.TensorProduct.map_tmul]
  have e2 : dbl (incM F d.Y.J) = incM F (dbl d.Y.J) := by
    simp [dbl, incM, Matrix.fromBlocks_map, Matrix.map_neg]
  have key : incM F (d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ) =
      (incM F d.b.1)ᵀ * incM F (dbl d.Y.J) * incM F (d.b.1.map σ) := by
    simp only [incM, Matrix.map_mul, Matrix.transpose_map]
  rw [e1, e2, ← key, h]
  ext (i | i) (j | j)
  · simp [incM, Jm]
  · by_cases hij : i = j
    · subst hij; simp [incM, Jm]
    · simp [incM, Jm, Matrix.one_apply_ne hij]
  · by_cases hij : i = j
    · subst hij; simp [incM, Jm, map_intCast]
    · simp [incM, Jm, Matrix.one_apply_ne hij]
  · simp [incM, Jm]

/- English proof (translation)
Rewrite using `[Matrix.mul_apply, Fintype.sum_sum_type, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Simplify using `only [Jm, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.transpose_apply, Matrix.map_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.smul_apply, Matrix.one_apply, mul_zero, Finset.sum_con …`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem form_apply {n : ℕ} (c : AE F E →+* AE F E) (ε : AE F E)
    (N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) (x y : Fin n ⊕ Fin n) :
    (Nᵀ * Jm n ε * N.map c) x y =
      ∑ k, (ε * N (Sum.inr k) x * c (N (Sum.inl k) y) + N (Sum.inl k) x * c (N (Sum.inr k) y)) := by
  rw [Matrix.mul_apply, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Jm, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.transpose_apply, Matrix.map_apply, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.smul_apply,
    Matrix.one_apply, mul_zero, Finset.sum_const_zero, zero_add, add_zero, smul_eq_mul, mul_ite, mul_one,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

/- English proof (translation)
Apply the tactic sequence `rcases Int.units_eq_one_or ε with h | h <;> simp [h]`.
-/
theorem unit_int (ε : ℤˣ) : IsUnit (((ε : ℤ) : AE F E)) := by
  rcases Int.units_eq_one_or ε with h | h <;> simp [h]

/- English proof (translation)
Introduce `b hb`. Establish `e` using `congrFun (congrFun hM b) (Sum.inl i₀)`. Rewrite `e` using `[form_apply, Finset.sum_eq_single i₀]`. Simplify using `only [hcol, if_true, Sum.inr.injEq, reduceCtorEq, if_false, map_zero, mul_zero, add_zero] at e`. Establish `hr : Jm n ((ε : ℤ) : AE F E) b (Sum.inl i₀) = 0`.

Break down `b with b | b` into its components or cases. Simplify using the standard rewrite rules. Establish `: b ≠ i₀` using `fun h => hb (h ▸ rfl)`. Simplify using `[Matrix.one_apply_ne this]`. Rewrite `e` using `[hr]`.

Establish `hu : IsUnit (((ε : ℤ) : AE F E) * c lam)` using `(unit_int ε).mul ((Units.map c.toMonoidHom lam).isUnit)`. Establish `: ((ε : ℤ) : AE F E) * c lam * M (Sum.inr i₀) b = 0` using `by rw [← e]; ring`. Conclude with `(hu.mul_right_eq_zero).1 this`. Introduce `k _ hk`. Simplify using `[hcol, hk]`.

Simplify using the standard rewrite rules. Use `local notation:70 X:70 " ⬝ " Y:71 => @HMul.hMul _ _ _ Matrix.instHMulOfFintypeOfMulOfAddCommMonoid X Y`.
-/
theorem row_zero {n : ℕ} {i₀ : Fin n} (c : AE F E →+* AE F E) (ε : ℤˣ)
    {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)} {lam : (AE F E)ˣ}
    (hM : Mᵀ * Jm n ((ε : ℤ) : AE F E) * M.map c = Jm n ((ε : ℤ) : AE F E))
    (hcol : ∀ a, M a (Sum.inl i₀) = if a = Sum.inl i₀ then (lam : AE F E) else 0) :
    ∀ b, b ≠ Sum.inr i₀ → M (Sum.inr i₀) b = 0 := by
  intro b hb
  have e := congrFun (congrFun hM b) (Sum.inl i₀)
  rw [form_apply, Finset.sum_eq_single i₀] at e
  · simp only [hcol, if_true, Sum.inr.injEq, reduceCtorEq, if_false, map_zero, mul_zero, add_zero] at e
    have hr : Jm n ((ε : ℤ) : AE F E) b (Sum.inl i₀) = 0 := by
      rcases b with b | b
      · simp
      · have : b ≠ i₀ := fun h => hb (h ▸ rfl)
        simp [Matrix.one_apply_ne this]
    rw [hr] at e
    have hu : IsUnit (((ε : ℤ) : AE F E) * c lam) := (unit_int ε).mul ((Units.map c.toMonoidHom lam).isUnit)
    have : ((ε : ℤ) : AE F E) * c lam * M (Sum.inr i₀) b = 0 := by rw [← e]; ring
    exact (hu.mul_right_eq_zero).1 this
  · intro k _ hk
    simp [hcol, hk]
  · simp

local notation:70 X:70 " ⬝ " Y:71 => @HMul.hMul _ _ _ Matrix.instHMulOfFintypeOfMulOfAddCommMonoid X Y

/- English proof (translation)
Use extensionality with `x y`. Rewrite using `[Matrix.submatrix_apply, form_apply, form_apply]`. Establish `hx : Sum.map L.em L.em x ≠ Sum.inr L.i₀`. Break down `x with x | x` into its components or cases. Simplify using the standard rewrite rules.

Simplify using `using (L.rng (L.em x)).2 ⟨x, rfl⟩`. Establish `hy : Sum.map L.em L.em y ≠ Sum.inr L.i₀`. Break down `y with y | y` into its components or cases. Simplify using the standard rewrite rules. Simplify using `using (L.rng (L.em y)).2 ⟨y, rfl⟩`.

Use `Fintype.sum_of_injective L.em L.inj _ _ (fun k hk => ?_) (fun k => rfl)` and prove the remaining obligations. Establish `: k = L.i₀` using `by by_contra h; exact hk ((L.rng k).1 h)`. Substitute `this` using the available equality. Rewrite using `[hr _ hx, hr _ hy, map_zero]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sub_form {d : SD σ} (L : LD d) (c : AE F E →+* AE F E) (ε : AE F E)
    (M : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E))
    (hr : ∀ b, b ≠ Sum.inr L.i₀ → M (Sum.inr L.i₀) b = 0) :
    (M.submatrix (Sum.map L.em L.em) (Sum.map L.em L.em))ᵀ * Jm L.n ε *
        (M.submatrix (Sum.map L.em L.em) (Sum.map L.em L.em)).map c =
      (Mᵀ * Jm d.n ε * M.map c).submatrix (Sum.map L.em L.em) (Sum.map L.em L.em) := by
  ext x y
  rw [Matrix.submatrix_apply, form_apply, form_apply]
  have hx : Sum.map L.em L.em x ≠ Sum.inr L.i₀ := by
    rcases x with x | x
    · simp
    · simpa using (L.rng (L.em x)).2 ⟨x, rfl⟩
  have hy : Sum.map L.em L.em y ≠ Sum.inr L.i₀ := by
    rcases y with y | y
    · simp
    · simpa using (L.rng (L.em y)).2 ⟨y, rfl⟩
  refine Fintype.sum_of_injective L.em L.inj _ _ (fun k hk => ?_) (fun k => rfl)
  have : k = L.i₀ := by by_contra h; exact hk ((L.rng k).1 h)
  subst this
  rw [hr _ hx, hr _ hy, map_zero]; ring

/- English proof (translation)
Apply the tactic sequence `ext (i | i) (j | j) <;> simp [Jm, Matrix.one_apply, L.inj.eq_iff]`.
-/
theorem sub_J {d : SD σ} (L : LD d) (ε : AE F E) :
    (Jm d.n ε).submatrix (Sum.map L.em L.em) (Sum.map L.em L.em) = Jm L.n ε := by
  ext (i | i) (j | j) <;> simp [Jm, Matrix.one_apply, L.inj.eq_iff]

/- English proof (translation)
Establish `hε : ((ε : ℤ) : AE F E) * ((ε : ℤ) : AE F E) = 1`. Apply the tactic sequence `rcases Int.units_eq_one_or ε with h | h <;> simp [h]`. Apply the tactic sequence `ext (i | i) (j | j) <;>`. Simplify using `[Jm, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, Matrix.smul_apply, ← mul_assoc, hε]`.
-/
theorem Jm_sq (n : ℕ) (ε : ℤˣ) : Jm n ((ε : ℤ) : AE F E) * (((ε : ℤ) : AE F E) • Jm n ((ε : ℤ) : AE F E)) = 1 := by
  have hε : ((ε : ℤ) : AE F E) * ((ε : ℤ) : AE F E) = 1 := by
    rcases Int.units_eq_one_or ε with h | h <;> simp [h]
  ext (i | i) (j | j) <;>
    simp [Jm, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, Matrix.smul_apply, ← mul_assoc, hε]

/- English proof (translation)
Use `set J := Jm d.n ((ε : ℤ) : AE F E) with hJdef`. Establish `hNu : IsUnit N.det`. Establish `e : Nᵀ * (J * N.map (cA σ).toRingHom * (((ε : ℤ) : AE F E) • J)) = 1`. Combine the equalities or inequalities in the displayed calculation. Use `congrArg Matrix.det e` as an intermediate fact.

Rewrite `this` using `[Matrix.det_mul, Matrix.det_transpose, Matrix.det_one]`. Conclude with `isUnit_iff_exists_inv.2 ⟨_, this⟩`. Establish `hBm : IsUnit (incM F d.b.1)` using `(Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_exists_inv.2 ⟨_, by rw [← Matrix.det_mul, KWhit.incM_mul_inv d, Matrix.det_one]⟩)`. Establish `hBi : IsUnit (incM F (d.b⁻¹).1)` using `(Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_exists_inv.2 ⟨_, by rw [← Matrix.det_mul, KWhit.incM_inv_mul d, Matrix.det_one]⟩)`. Establish `hM0u : IsUnit (incM F d.b.1 * N * incM F (d.b⁻¹).1)` using `(hBm.mul ((Matrix.isUnit_iff_isUnit_det _).2 hNu)).mul hBi`.

Establish `hf' : (incM F d.b.1)ᵀ * dbl (incM F d.Y.J) * (incM F d.b.1).map (cA σ).toRingHom = J` using `hf`. Rewrite `hN` using `[← hf']`. Establish `hM0mem` using `KWhit.form_conj_out (cA σ).toRingHom (KWhit.incM_mul_inv d) hN`. Set `u : GL (Fin d.n ⊕ Fin d.n) (AE F E)` to `hM0u.unit`. Establish `hu : (u : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) = incM F d.b.1 * N * incM F (d.b⁻¹).1` using `IsUnit.unit_spec hM0u`.

Establish `hmem : u ∈ UG (cA σ) (dbl (incM F d.Y.J))` using `by show (u : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E))ᵀ * dbl (incM F d.Y.J) * (u : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)).map (cA σ) = dbl (incM F d.Y.J)`. Rewrite using `[hu]`. Conclude with `hM0mem`. Use `⟨⟨u, hmem⟩, ?_⟩` and prove the remaining obligations. Use `show incM F (d.b⁻¹).1 * (u : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) * incM F d.b.1 = N`.

Rewrite using `[hu]`. Simplify using `only [← Matrix.mul_assoc, KWhit.incM_inv_mul d, Matrix.one_mul]`. Rewrite using `[Matrix.mul_assoc, KWhit.incM_inv_mul d, Matrix.mul_one]`.
-/
theorem mkG (d : SD σ) (ε : ℤˣ)
    (hf : (incM F d.b.1)ᵀ * dbl (incM F d.Y.J) * (incM F d.b.1).map (cA σ) = Jm d.n ((ε : ℤ) : AE F E))
    (N : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E))
    (hN : Nᵀ * Jm d.n ((ε : ℤ) : AE F E) * N.map (cA σ).toRingHom = Jm d.n ((ε : ℤ) : AE F E)) :
    ∃ g : d.G, inFrame d.b g = N := by
  set J := Jm d.n ((ε : ℤ) : AE F E) with hJdef
  have hNu : IsUnit N.det := by
    have e : Nᵀ * (J * N.map (cA σ).toRingHom * (((ε : ℤ) : AE F E) • J)) = 1 := by
      calc Nᵀ * (J * N.map (cA σ).toRingHom * (((ε : ℤ) : AE F E) • J))
          = (Nᵀ * J * N.map (cA σ).toRingHom) * (((ε : ℤ) : AE F E) • J) := by simp only [Matrix.mul_assoc]
        _ = J * (((ε : ℤ) : AE F E) • J) := by rw [hN]
        _ = 1 := Jm_sq d.n ε
    have := congrArg Matrix.det e
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at this
    exact isUnit_iff_exists_inv.2 ⟨_, this⟩
  have hBm : IsUnit (incM F d.b.1) := (Matrix.isUnit_iff_isUnit_det _).2
    (isUnit_iff_exists_inv.2 ⟨_, by rw [← Matrix.det_mul, KWhit.incM_mul_inv d, Matrix.det_one]⟩)
  have hBi : IsUnit (incM F (d.b⁻¹).1) := (Matrix.isUnit_iff_isUnit_det _).2
    (isUnit_iff_exists_inv.2 ⟨_, by rw [← Matrix.det_mul, KWhit.incM_inv_mul d, Matrix.det_one]⟩)
  have hM0u : IsUnit (incM F d.b.1 * N * incM F (d.b⁻¹).1) :=
    (hBm.mul ((Matrix.isUnit_iff_isUnit_det _).2 hNu)).mul hBi
  have hf' : (incM F d.b.1)ᵀ * dbl (incM F d.Y.J) * (incM F d.b.1).map (cA σ).toRingHom = J := hf
  rw [← hf'] at hN
  have hM0mem := KWhit.form_conj_out (cA σ).toRingHom (KWhit.incM_mul_inv d) hN
  let u : GL (Fin d.n ⊕ Fin d.n) (AE F E) := hM0u.unit
  have hu : (u : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) =
      incM F d.b.1 * N * incM F (d.b⁻¹).1 := IsUnit.unit_spec hM0u
  have hmem : u ∈ UG (cA σ) (dbl (incM F d.Y.J)) := by
    show (u : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E))ᵀ * dbl (incM F d.Y.J) *
      (u : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)).map (cA σ) = dbl (incM F d.Y.J)
    rw [hu]
    exact hM0mem
  refine ⟨⟨u, hmem⟩, ?_⟩
  show incM F (d.b⁻¹).1 * (u : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) * incM F d.b.1 = N
  rw [hu]
  simp only [← Matrix.mul_assoc, KWhit.incM_inv_mul d, Matrix.one_mul]
  rw [Matrix.mul_assoc, KWhit.incM_inv_mul d, Matrix.mul_one]

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [Matrix.submatrix_apply, Matrix.mul_apply]`. Use `(Fintype.sum_of_injective e he _ _ (fun c hc => ?_) (fun c => rfl)).symm` and prove the remaining obligations. Establish `hcS : c ∈ S` using `by by_contra h'; exact hc ((hr c).1 h')`. Establish `hne : c ≠ e b` using `by rintro rfl; exact (hr _).2 ⟨b, rfl⟩ hcS`.

Rewrite using `[(h c hcS (e b)).1, Matrix.one_apply_ne hne, mul_zero]`.
-/
theorem IdI.sub_mul_right {ι κ R : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Semiring R]
    {S : Set ι} {H : Matrix ι ι R} (h : IdI S H) (X : Matrix ι ι R) {e : κ → ι} (he : Function.Injective e)
    (hr : ∀ c, c ∉ S ↔ c ∈ Set.range e) : (X * H).submatrix e e = X.submatrix e e * H.submatrix e e := by
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  refine (Fintype.sum_of_injective e he _ _ (fun c hc => ?_) (fun c => rfl)).symm
  have hcS : c ∈ S := by by_contra h'; exact hc ((hr c).1 h')
  have hne : c ≠ e b := by rintro rfl; exact (hr _).2 ⟨b, rfl⟩ hcS
  rw [(h c hcS (e b)).1, Matrix.one_apply_ne hne, mul_zero]

/- English proof (translation)
Use `set M := inFrame d.b p with hMdef`. Establish `hfd` using `frame_formE d ε hd`. Establish `hfL` using `frame_formE L.sd ε hL`. Establish `hMform : Mᵀ * Jm d.n ((ε : ℤ) : AE F E) * M.map (cA σ).toRingHom = Jm d.n ((ε : ℤ) : AE F E)`. Establish `hP : (mat2 p)ᵀ * dbl (incM F d.Y.J) * (mat2 p).map (cA σ).toRingHom = dbl (incM F d.Y.J)` using `p.2`.

Use `KWhit.form_conj_in (cA σ).toRingHom (KWhit.incM_mul_inv d) hP` as an intermediate fact. Establish `hfd' : (incM F d.b.1)ᵀ * dbl (incM F d.Y.J) * (incM F d.b.1).map (cA σ).toRingHom = Jm d.n ((ε : ℤ) : AE F E)` using `hfd`. Rewrite `this` using `[hfd']`. Conclude with `this`. Establish `hrow` using `row_zero (cA σ).toRingHom ε hMform hp`.

Establish `hsub` using `sub_form L (cA σ).toRingHom (((ε : ℤ) : AE F E)) M hrow`. Rewrite `hsub` using `[hMform, sub_J]`. Take `⟨g, hg⟩` from `mkG L.sd ε hfL _ hsub`. Use `⟨g, ?_⟩` and prove the remaining obligations. Rewrite using `[KWhit.inFrame_mul, ← map_inv]`.

Use `set H' := inFrame d.b (L.j g⁻¹) with hH'`. Establish `hI : IdI (I0 L.i₀) H'` using `idI_j L g⁻¹`. Establish `hsubH : H'.submatrix (Sum.map L.em L.em) (Sum.map L.em L.em) = inFrame L.b g⁻¹` using `L.j_in g⁻¹`. Establish `hinv : M.submatrix (Sum.map L.em L.em) (Sum.map L.em L.em) * inFrame L.b g⁻¹ = 1`. Establish `e` using `KWhit.inFrame_mul L.sd g g⁻¹`.

Rewrite `e` using `[mul_inv_cancel, inFrame_one]`. Rewrite using `[← hg]`. Conclude with `e.symm`. Use `⟨fun a b ha hb => ?_, fun a => ?_, fun b hb => ?_⟩` and prove the remaining obligations. Take `⟨a', rfl⟩` from `(emm_rng L a).1 ha`.

Take `⟨b', rfl⟩` from `(emm_rng L b).1 hb`. Establish `e` using `congrFun (congrFun (hI.sub_mul_right M (emm_inj L) (emm_rng L)) a') b'`. Rewrite `e` using `[Matrix.submatrix_apply, hsubH, hinv]`. Rewrite using `[e]`. Distinguish the cases in `hab : a' = b'`.

Substitute `hab` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[Matrix.one_apply_ne hab, Matrix.one_apply_ne ((emm_inj L).ne hab)]`. Rewrite using `[mul_col_one (fun v => (hI _ (Or.inl rfl) v).2)]`. Conclude with `hp a`.

Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single (Sum.inr L.i₀)]`. Rewrite using `[(hI _ (Or.inr rfl) b).1, Matrix.one_apply_ne (Ne.symm hb), mul_zero]`. Introduce `c _ hc`. Rewrite using `[show inFrame d.b p (Sum.inr L.i₀) c = 0 from hrow c hc, zero_mul]`. Simplify using the standard rewrite rules.
-/
theorem q_split' {d : SD σ} (L : LD d) (ε : ℤˣ)
    (hd : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0)
    (hL : L.b.1ᵀ * dbl L.Y.J * L.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0)
    (p : d.G) (lam : (AE F E)ˣ)
    (hp : ∀ a, inFrame d.b p a (Sum.inl L.i₀) = if a = Sum.inl L.i₀ then (lam : AE F E) else 0) :
    ∃ g : L.sd.G, IsQ F E L.i₀ (inFrame d.b (p * (L.j g)⁻¹)) lam := by
  set M := inFrame d.b p with hMdef
  have hfd := frame_formE d ε hd
  have hfL := frame_formE L.sd ε hL
  have hMform : Mᵀ * Jm d.n ((ε : ℤ) : AE F E) * M.map (cA σ).toRingHom = Jm d.n ((ε : ℤ) : AE F E) := by
    have hP : (mat2 p)ᵀ * dbl (incM F d.Y.J) * (mat2 p).map (cA σ).toRingHom = dbl (incM F d.Y.J) := p.2
    have := KWhit.form_conj_in (cA σ).toRingHom (KWhit.incM_mul_inv d) hP
    have hfd' : (incM F d.b.1)ᵀ * dbl (incM F d.Y.J) * (incM F d.b.1).map (cA σ).toRingHom =
        Jm d.n ((ε : ℤ) : AE F E) := hfd
    rw [hfd'] at this
    exact this
  have hrow := row_zero (cA σ).toRingHom ε hMform hp
  have hsub := sub_form L (cA σ).toRingHom (((ε : ℤ) : AE F E)) M hrow
  rw [hMform, sub_J] at hsub
  obtain ⟨g, hg⟩ := mkG L.sd ε hfL _ hsub
  refine ⟨g, ?_⟩
  rw [KWhit.inFrame_mul, ← map_inv]
  set H' := inFrame d.b (L.j g⁻¹) with hH'
  have hI : IdI (I0 L.i₀) H' := idI_j L g⁻¹
  have hsubH : H'.submatrix (Sum.map L.em L.em) (Sum.map L.em L.em) = inFrame L.b g⁻¹ := L.j_in g⁻¹
  have hinv : M.submatrix (Sum.map L.em L.em) (Sum.map L.em L.em) * inFrame L.b g⁻¹ = 1 := by
    have e := KWhit.inFrame_mul L.sd g g⁻¹
    rw [mul_inv_cancel, inFrame_one] at e
    rw [← hg]; exact e.symm
  refine ⟨fun a b ha hb => ?_, fun a => ?_, fun b hb => ?_⟩
  · obtain ⟨a', rfl⟩ := (emm_rng L a).1 ha
    obtain ⟨b', rfl⟩ := (emm_rng L b).1 hb
    have e := congrFun (congrFun (hI.sub_mul_right M (emm_inj L) (emm_rng L)) a') b'
    rw [Matrix.submatrix_apply, hsubH, hinv] at e
    rw [e]
    by_cases hab : a' = b'
    · subst hab; simp
    · rw [Matrix.one_apply_ne hab, Matrix.one_apply_ne ((emm_inj L).ne hab)]
  · rw [mul_col_one (fun v => (hI _ (Or.inl rfl) v).2)]
    exact hp a
  · rw [Matrix.mul_apply, Finset.sum_eq_single (Sum.inr L.i₀)]
    · rw [(hI _ (Or.inr rfl) b).1, Matrix.one_apply_ne (Ne.symm hb), mul_zero]
    · intro c _ hc
      rw [show inFrame d.b p (Sum.inr L.i₀) c = 0 from hrow c hc, zero_mul]
    · simp

end PositivityTheory.SiegelWeilFormula.Avac

end
