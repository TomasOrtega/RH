import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.IwasawaCompletion.FlDefs

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.SmGL
open scoped ComplexOrder

namespace PositivityTheory.Rg.Rs.C3.Fl

/- English proof (translation)
Set `g' : Matrix (Fin N)ᵒᵈ (Fin N)ᵒᵈ ℂ` to `g`. Establish `hg' : IsUnit g'` using `hg`. Establish `hinj : Function.Injective fun v => v ᵥ* g'`. Take `⟨u, hu⟩` from `hg'`. Introduce `v w hvw`.

Use `congrArg (fun x => x ᵥ* (u⁻¹ : (Matrix (Fin N)ᵒᵈ (Fin N)ᵒᵈ ℂ)ˣ).1) hvw` as an intermediate fact. Simplify `this` using `[← hu, vecMul_vecMul]`. Establish `hS : (g' * g'ᴴ).PosDef` using `PosDef.mul_conjTranspose_self g' hinj`. Use `set L := LDL.lowerInv hS with hL`. Establish `hD : LDL.diag hS = L * (g' * g'ᴴ) * Lᴴ` using `LDL.diag_eq_lowerInv_conj hS`.

Establish `hLinj : Function.Injective fun v => v ᵥ* L`. Introduce `v w hvw`. Use `congrArg (fun x => x ᵥ* ⅟L) hvw` as an intermediate fact. Simplify `this` using `[vecMul_vecMul]`. Establish `hDpos : (L * (g' * g'ᴴ) * Lᴴ).PosDef` using `hS.mul_mul_conjTranspose_same hLinj`.

Use `set d := LDL.diagEntries hS`. Establish `hd : ∀ i, 0 < (d i).re ∧ (d i).im = 0`. Introduce `i`. Use `hDpos.diag_pos (i := i)` as an intermediate fact. Rewrite `this` using `[← hD]`.

Simplify using `only [LDL.diag, diagonal_apply_eq] at this`. Conclude with `⟨(Complex.pos_iff.1 this).1, (Complex.pos_iff.1 this).2.symm⟩`. Set `s : (Fin N)ᵒᵈ → ℂ` to `fun i => (((Real.sqrt (d i).re)⁻¹ : ℝ) : ℂ)`. Set `T' : Matrix (Fin N)ᵒᵈ (Fin N)ᵒᵈ ℂ` to `diagonal s * L`. Establish `hT : T' * (g' * g'ᴴ) * T'ᴴ = 1`.

Establish `e1 : T' * (g' * g'ᴴ) * T'ᴴ = diagonal s * LDL.diag hS * diagonal (star s)`. Rewrite using `[hD]`. Simplify using `only [T', conjTranspose_mul, diagonal_conjTranspose, Matrix.mul_assoc]`. Rewrite using `[e1, LDL.diag, diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]`. Use `congr 1`.

Use function extensionality and compare the values at `i`. Establish `hdi : d i = ((d i).re : ℂ)` using `Complex.ext rfl (by simp [(hd i).2])`. Establish `hr` using `(hd i).1`. Express the relevant statement in the definitionally equal form `(((Real.sqrt (d i).re)⁻¹ : ℝ) : ℂ) * d i * star (((Real.sqrt (d i).re)⁻¹ : ℝ) : ℂ) = 1`. Rewrite using `[Complex.star_def, Complex.conj_ofReal]`.

Generalize the expression as in `(d i).re = r at hdi hr ⊢`. Rewrite using `[hdi]`. Establish `hsq : Real.sqrt r * Real.sqrt r = r` using `Real.mul_self_sqrt hr.le`. Establish `hne : Real.sqrt r ≠ 0` using `(Real.sqrt_pos.2 hr).ne'`. Rewrite using `[← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_one]`.

Use `congr 1`. Clear the denominators using the available nonvanishing facts. Rewrite using `[Real.sq_sqrt hr.le]`. Use `⟨T', ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : T' * (g' * (T' * g')ᴴ) = 1`.

Rewrite using `[conjTranspose_mul, ← hT]`. Simplify using `only [Matrix.mul_assoc]`. Conclude with `⟨⟨T', _, h1, mul_eq_one_comm.1 h1⟩, rfl⟩`. Introduce `i j hij`. Establish `h0 : L (OrderDual.toDual i) (OrderDual.toDual j) = 0` using `LDL.lowerInv_triangular hS hij`.

Express the relevant statement in the definitionally equal form `(diagonal s * L) (OrderDual.toDual i) (OrderDual.toDual j) = 0`. Rewrite using `[diagonal_mul]`. Conclude with `mul_eq_zero_of_right _ h0`. Rewrite using `[mem_unitaryGroup_iff, star_eq_conjTranspose]`. Establish `: T' * g' * (T' * g')ᴴ = 1`.

Rewrite using `[conjTranspose_mul, ← hT]`. Simplify using `only [Matrix.mul_assoc]`. Conclude with `this`.
-/
theorem exists_upper_unitary_complex {N : ℕ} (g : Matrix (Fin N) (Fin N) ℂ) (hg : IsUnit g) :
    ∃ T : Matrix (Fin N) (Fin N) ℂ, IsUnit T ∧ (∀ i j : Fin N, j < i → T i j = 0) ∧
      T * g ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  let g' : Matrix (Fin N)ᵒᵈ (Fin N)ᵒᵈ ℂ := g
  have hg' : IsUnit g' := hg
  have hinj : Function.Injective fun v => v ᵥ* g' := by
    obtain ⟨u, hu⟩ := hg'
    intro v w hvw
    have := congrArg (fun x => x ᵥ* (u⁻¹ : (Matrix (Fin N)ᵒᵈ (Fin N)ᵒᵈ ℂ)ˣ).1) hvw
    simpa [← hu, vecMul_vecMul] using this
  have hS : (g' * g'ᴴ).PosDef := PosDef.mul_conjTranspose_self g' hinj
  set L := LDL.lowerInv hS with hL
  have hD : LDL.diag hS = L * (g' * g'ᴴ) * Lᴴ := LDL.diag_eq_lowerInv_conj hS
  have hLinj : Function.Injective fun v => v ᵥ* L := by
    intro v w hvw
    have := congrArg (fun x => x ᵥ* ⅟L) hvw
    simpa [vecMul_vecMul] using this
  have hDpos : (L * (g' * g'ᴴ) * Lᴴ).PosDef := hS.mul_mul_conjTranspose_same hLinj
  set d := LDL.diagEntries hS
  have hd : ∀ i, 0 < (d i).re ∧ (d i).im = 0 := by
    intro i
    have := hDpos.diag_pos (i := i)
    rw [← hD] at this
    simp only [LDL.diag, diagonal_apply_eq] at this
    exact ⟨(Complex.pos_iff.1 this).1, (Complex.pos_iff.1 this).2.symm⟩
  let s : (Fin N)ᵒᵈ → ℂ := fun i => (((Real.sqrt (d i).re)⁻¹ : ℝ) : ℂ)
  let T' : Matrix (Fin N)ᵒᵈ (Fin N)ᵒᵈ ℂ := diagonal s * L
  have hT : T' * (g' * g'ᴴ) * T'ᴴ = 1 := by
    have e1 : T' * (g' * g'ᴴ) * T'ᴴ = diagonal s * LDL.diag hS * diagonal (star s) := by
      rw [hD]; simp only [T', conjTranspose_mul, diagonal_conjTranspose, Matrix.mul_assoc]
    rw [e1, LDL.diag, diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    have hdi : d i = ((d i).re : ℂ) := Complex.ext rfl (by simp [(hd i).2])
    have hr := (hd i).1
    change (((Real.sqrt (d i).re)⁻¹ : ℝ) : ℂ) * d i * star (((Real.sqrt (d i).re)⁻¹ : ℝ) : ℂ) = 1
    rw [Complex.star_def, Complex.conj_ofReal]
    generalize (d i).re = r at hdi hr ⊢
    rw [hdi]
    have hsq : Real.sqrt r * Real.sqrt r = r := Real.mul_self_sqrt hr.le
    have hne : Real.sqrt r ≠ 0 := (Real.sqrt_pos.2 hr).ne'
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_one]
    congr 1
    field_simp
    rw [Real.sq_sqrt hr.le]
  refine ⟨T', ?_, ?_, ?_⟩
  · have h1 : T' * (g' * (T' * g')ᴴ) = 1 := by
      rw [conjTranspose_mul, ← hT]; simp only [Matrix.mul_assoc]
    exact ⟨⟨T', _, h1, mul_eq_one_comm.1 h1⟩, rfl⟩
  · intro i j hij
    have h0 : L (OrderDual.toDual i) (OrderDual.toDual j) = 0 := LDL.lowerInv_triangular hS hij
    change (diagonal s * L) (OrderDual.toDual i) (OrderDual.toDual j) = 0
    rw [diagonal_mul]
    exact mul_eq_zero_of_right _ h0
  · rw [mem_unitaryGroup_iff, star_eq_conjTranspose]
    have : T' * g' * (T' * g')ᴴ = 1 := by
      rw [conjTranspose_mul, ← hT]; simp only [Matrix.mul_assoc]
    exact this

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

omit [NumberField E] [IsTotallyComplex E] in

/- English proof (translation)
Set `ev : InfinitePlace E → Cinf E →+* ℂ` to `fun τ => Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) τ`. Establish `hu : ∀ τ, IsUnit ((y : Matrix (Fin N) (Fin N) (Cinf E)).map (ev τ))` using `fun τ => (GeneralLinearGroup.map (ev τ) y).isUnit`. Use `choose T _ hTup hTun using fun τ => exists_upper_unitary_complex _ (hu τ)`. Set `T' : Matrix (Fin N) (Fin N) (Cinf E)` to `fun i j τ => T τ i j`. Establish `hev : ∀ τ, T'.map (ev τ) = T τ` using `fun τ => rfl`.

Establish `key : T' * (y : Matrix (Fin N) (Fin N) (Cinf E)) * star (T' * (y : Matrix (Fin N) (Fin N) (Cinf E))) = 1`. Establish `hmap : ∀ τ, (T' * (y : Matrix (Fin N) (Fin N) (Cinf E)) * star (T' * (y : Matrix (Fin N) (Fin N) (Cinf E)))).map (ev τ) = 1`. Introduce `τ`. Establish `e1 : (T' * (y : Matrix (Fin N) (Fin N) (Cinf E))).map (ev τ) = T τ * (y : Matrix (Fin N) (Fin N) (Cinf E)).map (ev τ)`. Rewrite using `[Matrix.map_mul, hev]`.

Establish `e2 : (star (T' * (y : Matrix (Fin N) (Fin N) (Cinf E)))).map (ev τ) = star ((T' * (y : Matrix (Fin N) (Fin N) (Cinf E))).map (ev τ))`. Use extensionality with `i j`. Both sides reduce to the same expression. Rewrite using `[Matrix.map_mul, e2, e1]`. Conclude with `mem_unitaryGroup_iff.1 (hTun τ)`.

Use extensionality with `i j τ`. Use `congrFun (congrFun (hmap τ) i) j` as an intermediate fact. Rewrite `this` using `[Matrix.map_apply]`. Express the relevant statement in the definitionally equal form `((T' * (y : Matrix (Fin N) (Fin N) (Cinf E)) * star (T' * (y : Matrix (Fin N) (Fin N) (Cinf E)))) i j) τ = _`. Use `this.trans ?_` and prove the remaining obligations.

Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Matrix.one_apply_ne hij]`. Establish `h1 : T' * ((y : Matrix (Fin N) (Fin N) (Cinf E)) * star (T' * (y : Matrix (Fin N) (Fin N) (Cinf E)))) = 1`.

Rewrite using `[← Matrix.mul_assoc, key]`. Set `U : (Matrix (Fin N) (Fin N) (Cinf E))ˣ` to `⟨T', _, h1, mul_eq_one_comm.1 h1⟩`. Establish `hk : T' * (y : Matrix (Fin N) (Fin N) (Cinf E)) ∈ Matrix.unitaryGroup (Fin N) (Cinf E)` using `mem_unitaryGroup_iff.2 key`. Use `⟨U⁻¹, ⟨_, hk⟩, ?_, ?_⟩` and prove the remaining obligations. Establish `hT : T'.BlockTriangular id` using `fun i j hij => funext fun τ => hTup τ i j hij`.

Establish `: Invertible T'` using `U.invertible`. Establish `hinv` using `blockTriangular_inv_of_blockTriangular hT`. Introduce `i j hij`. Rewrite using `[Matrix.coe_units_inv]`. Conclude with `hinv hij`.

Use `Units.ext ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(y : Matrix (Fin N) (Fin N) (Cinf E)) = ((U⁻¹ : (Matrix (Fin N) (Fin N) (Cinf E))ˣ) : Matrix (Fin N) (Fin N) (Cinf E)) * (T' * (y : Matrix (Fin N) (Fin N) (Cinf E)))`. Rewrite using `[← Matrix.mul_assoc]`. Express the relevant statement in the definitionally equal form `_ = ((U⁻¹ * U : (Matrix (Fin N) (Fin N) (Cinf E))ˣ) : Matrix (Fin N) (Fin N) (Cinf E)) * (y : Matrix (Fin N) (Fin N) (Cinf E))`. Rewrite using `[inv_mul_cancel, Units.val_one, Matrix.one_mul]`.
-/
theorem exists_borel_unitary {N : ℕ} (y : GL (Fin N) (Cinf E)) :
    ∃ (b : GL (Fin N) (Cinf E)) (k : Kinf E N),
      (∀ i j : Fin N, j < i → (b : Matrix (Fin N) (Fin N) (Cinf E)) i j = 0) ∧ y = b * Unitary.toUnits k := by
  classical
  let ev : InfinitePlace E → Cinf E →+* ℂ := fun τ => Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) τ
  have hu : ∀ τ, IsUnit ((y : Matrix (Fin N) (Fin N) (Cinf E)).map (ev τ)) := fun τ =>
    (GeneralLinearGroup.map (ev τ) y).isUnit
  choose T _ hTup hTun using fun τ => exists_upper_unitary_complex _ (hu τ)
  let T' : Matrix (Fin N) (Fin N) (Cinf E) := fun i j τ => T τ i j
  have hev : ∀ τ, T'.map (ev τ) = T τ := fun τ => rfl
  have key : T' * (y : Matrix (Fin N) (Fin N) (Cinf E)) * star (T' * (y : Matrix (Fin N) (Fin N) (Cinf E))) = 1 := by
    have hmap : ∀ τ, (T' * (y : Matrix (Fin N) (Fin N) (Cinf E)) *
        star (T' * (y : Matrix (Fin N) (Fin N) (Cinf E)))).map (ev τ) = 1 := by
      intro τ
      have e1 : (T' * (y : Matrix (Fin N) (Fin N) (Cinf E))).map (ev τ) = T τ * (y : Matrix (Fin N) (Fin N) (Cinf E)).map (ev τ) := by
        rw [Matrix.map_mul, hev]
      have e2 : (star (T' * (y : Matrix (Fin N) (Fin N) (Cinf E)))).map (ev τ) =
          star ((T' * (y : Matrix (Fin N) (Fin N) (Cinf E))).map (ev τ)) := by
        ext i j; rfl
      rw [Matrix.map_mul, e2, e1]
      exact mem_unitaryGroup_iff.1 (hTun τ)
    ext i j τ
    have := congrFun (congrFun (hmap τ) i) j
    rw [Matrix.map_apply] at this
    change ((T' * (y : Matrix (Fin N) (Fin N) (Cinf E)) * star (T' * (y : Matrix (Fin N) (Fin N) (Cinf E)))) i j) τ = _
    refine this.trans ?_
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij]
  have h1 : T' * ((y : Matrix (Fin N) (Fin N) (Cinf E)) * star (T' * (y : Matrix (Fin N) (Fin N) (Cinf E)))) = 1 := by
    rw [← Matrix.mul_assoc, key]
  let U : (Matrix (Fin N) (Fin N) (Cinf E))ˣ := ⟨T', _, h1, mul_eq_one_comm.1 h1⟩
  have hk : T' * (y : Matrix (Fin N) (Fin N) (Cinf E)) ∈ Matrix.unitaryGroup (Fin N) (Cinf E) :=
    mem_unitaryGroup_iff.2 key
  refine ⟨U⁻¹, ⟨_, hk⟩, ?_, ?_⟩
  · have hT : T'.BlockTriangular id := fun i j hij => funext fun τ => hTup τ i j hij
    have : Invertible T' := U.invertible
    have hinv := blockTriangular_inv_of_blockTriangular hT
    intro i j hij
    rw [Matrix.coe_units_inv]
    exact hinv hij
  · refine Units.ext ?_
    change (y : Matrix (Fin N) (Fin N) (Cinf E)) =
      ((U⁻¹ : (Matrix (Fin N) (Fin N) (Cinf E))ˣ) : Matrix (Fin N) (Fin N) (Cinf E)) * (T' * (y : Matrix (Fin N) (Fin N) (Cinf E)))
    rw [← Matrix.mul_assoc]
    change _ = ((U⁻¹ * U : (Matrix (Fin N) (Fin N) (Cinf E))ˣ) : Matrix (Fin N) (Fin N) (Cinf E)) * (y : Matrix (Fin N) (Fin N) (Cinf E))
    rw [inv_mul_cancel, Units.val_one, Matrix.one_mul]

/- English proof (translation)
Rewrite using `[← Fin.sum_univ_eq_sum_range (fun k => if h : k < c then d ⟨k, h⟩ else 0) m]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[dif_pos (lt_of_lt_of_le x.2 hm)]`. Both sides reduce to the same expression.
-/
theorem sum_castLE_eq {c : ℕ} (d : Fin c → ℕ) {m : ℕ} (hm : m ≤ c) :
    ∑ x : Fin m, d (Fin.castLE hm x) = ∑ k ∈ Finset.range m, (if h : k < c then d ⟨k, h⟩ else 0) := by
  rw [← Fin.sum_univ_eq_sum_range (fun k => if h : k < c then d ⟨k, h⟩ else 0) m]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [dif_pos (lt_of_lt_of_le x.2 hm)]
  rfl

/- English proof (translation)
Take `⟨⟨a, i'⟩, rfl⟩` from `(stdBlocks n h).surjective i`. Take `⟨⟨b, j'⟩, rfl⟩` from `(stdBlocks n h).surjective j`. Simplify using `only [blk_apply] at hij`. Rewrite using `[Fin.lt_def, stdBlocks_val, stdBlocks_val, sum_castLE_eq, sum_castLE_eq]`. Establish `h1 : ∑ k ∈ Finset.range (b + 1), (if h : k < c then n ⟨k, h⟩ else 0) ≤ ∑ k ∈ Finset.range a, (if h : k < c then n ⟨k, h⟩ else 0)` using `Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 hij)`.

Rewrite `h1` using `[Finset.sum_range_succ, dif_pos b.2]`. Simplify using `only [Fin.eta] at h1`. Establish `h2 : (j' : ℕ) < n b` using `j'.2`. Use linear arithmetic over natural numbers and integers.
-/
theorem blk_lt_stdBlocks {c N : ℕ} (n : Fin c → ℕ) (h : ∑ i, n i = N) {i j : Fin N}
    (hij : blk (stdBlocks n h) j < blk (stdBlocks n h) i) : j < i := by
  obtain ⟨⟨a, i'⟩, rfl⟩ := (stdBlocks n h).surjective i
  obtain ⟨⟨b, j'⟩, rfl⟩ := (stdBlocks n h).surjective j
  simp only [blk_apply] at hij
  rw [Fin.lt_def, stdBlocks_val, stdBlocks_val, sum_castLE_eq, sum_castLE_eq]
  have h1 : ∑ k ∈ Finset.range (b + 1), (if h : k < c then n ⟨k, h⟩ else 0) ≤
      ∑ k ∈ Finset.range a, (if h : k < c then n ⟨k, h⟩ else 0) :=
    Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 hij)
  rw [Finset.sum_range_succ, dif_pos b.2] at h1
  simp only [Fin.eta] at h1
  have h2 : (j' : ℕ) < n b := j'.2
  omega

/- English proof (translation)
The claim follows from `mem_parab.2 fun i j hij => hg i j (blk_lt_stdBlocks n h hij)`.
-/
theorem mem_parab_of_upper (R : Type) [CommRing R] {c N : ℕ} {n : Fin c → ℕ} (h : ∑ i, n i = N) {g : GL (Fin N) R}
    (hg : ∀ i j : Fin N, j < i → (g : Matrix (Fin N) (Fin N) R) i j = 0) : g ∈ parab R (stdBlocks n h) :=
  mem_parab.2 fun i j hij => hg i j (blk_lt_stdBlocks n h hij)

end PositivityTheory.Rg.Rs.C3.Fl

end
