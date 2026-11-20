import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.LevelTorusLeTorus
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.HodgeTateFromSandwich

noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;>`. Simplify using `[th', th, GlobalTheory.CuspRep.invT, Phi, MulAut.conj, Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMul, dotProduct]`.
-/
private theorem nu_eq_one_of_mem_n_of_good_of_ok {k : Type} [Field k] (g : GL (Fin 3) k) :
    (th' k g).1 =
      !![(g⁻¹).1 2 2, -(g⁻¹).1 1 2, (g⁻¹).1 0 2;
        -(g⁻¹).1 2 1, (g⁻¹).1 1 1, -(g⁻¹).1 0 1;
        (g⁻¹).1 2 0, -(g⁻¹).1 1 0, (g⁻¹).1 0 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [th', th, GlobalTheory.CuspRep.invT, Phi, MulAut.conj, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.vecMul, dotProduct]

/- English proof (translation)
Rewrite using `[← map_inv, nu_eq_one_of_mem_n_of_good_of_ok, inv_inv]`.
-/
private theorem nu_eq_one_of_mem_mu_of_good_of_deep {k : Type} [Field k] (g : GL (Fin 3) k) :
    ((th' k g)⁻¹).1 =
      !![g.1 2 2, -g.1 1 2, g.1 0 2;
        -g.1 2 1, g.1 1 1, -g.1 0 1;
        g.1 2 0, -g.1 1 0, g.1 0 0] := by
  rw [← map_inv, nu_eq_one_of_mem_n_of_good_of_ok, inv_inv]

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[nu_eq_one_of_mem_n_of_good_of_ok, ← map_inv, val_diagT, val_diagT]`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]`.
-/
private theorem mul_self_eq_one_and_nu_neg_one_of_isCC {k : Type} [Field k] (t : Fin 3 → kˣ) :
    th' k (diagT k (Fin 3) t) = diagT k (Fin 3) ![(t 2)⁻¹, (t 1)⁻¹, (t 0)⁻¹] := by
  apply Units.ext
  rw [nu_eq_one_of_mem_n_of_good_of_ok, ← map_inv, val_diagT, val_diagT]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]

/- English proof (translation)
Rewrite `hg`, the goal using `[GlAx.mem_Kc]`. Take `⟨h1, h2⟩` from `hg`. Simplify using `only [GlAx.Bd] at h1 h2 ⊢`. Use `⟨fun i j => ?_, fun i j => ?_⟩` and prove the remaining obligations. Apply the tactic sequence `rw [nu_eq_one_of_mem_n_of_good_of_ok] fin_cases i <;> fin_cases j <;> first`.

Consider the case `simpa [Matrix.one_apply] using h2 0 0`. Consider the case `simpa [Matrix.one_apply] using h2 0 1`. Consider the case `simpa [Matrix.one_apply] using h2 0 2`. Consider the case `simpa [Matrix.one_apply] using h2 1 0`. Consider the case `simpa [Matrix.one_apply] using h2 1 1`.

Consider the case `simpa [Matrix.one_apply] using h2 1 2`. Consider the case `simpa [Matrix.one_apply] using h2 2 0`. Consider the case `simpa [Matrix.one_apply] using h2 2 1`. Consider the case `simpa [Matrix.one_apply] using h2 2 2`. Apply the tactic sequence `rw [nu_eq_one_of_mem_mu_of_good_of_deep] fin_cases i <;> fin_cases j <;> first`.

Consider the case `simpa [Matrix.one_apply] using h1 0 0`. Consider the case `simpa [Matrix.one_apply] using h1 0 1`. Consider the case `simpa [Matrix.one_apply] using h1 0 2`. Consider the case `simpa [Matrix.one_apply] using h1 1 0`. Consider the case `simpa [Matrix.one_apply] using h1 1 1`.

Consider the case `simpa [Matrix.one_apply] using h1 1 2`. Consider the case `simpa [Matrix.one_apply] using h1 2 0`. Consider the case `simpa [Matrix.one_apply] using h1 2 1`. Consider the case `simpa [Matrix.one_apply] using h1 2 2`.
-/
private theorem exists_rt_ne_cycF_of_good_of_ok {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (c : ℕ) (g : GL (Fin 3) k) (hg : g ∈ Kc k 3 c) :
    th' k g ∈ Kc k 3 c := by
  rw [GlAx.mem_Kc] at hg ⊢
  obtain ⟨h1, h2⟩ := hg
  simp only [GlAx.Bd] at h1 h2 ⊢
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [nu_eq_one_of_mem_n_of_good_of_ok]
    fin_cases i <;> fin_cases j <;>
      first
        | simpa [Matrix.one_apply] using h2 0 0
        | simpa [Matrix.one_apply] using h2 0 1
        | simpa [Matrix.one_apply] using h2 0 2
        | simpa [Matrix.one_apply] using h2 1 0
        | simpa [Matrix.one_apply] using h2 1 1
        | simpa [Matrix.one_apply] using h2 1 2
        | simpa [Matrix.one_apply] using h2 2 0
        | simpa [Matrix.one_apply] using h2 2 1
        | simpa [Matrix.one_apply] using h2 2 2
  · rw [nu_eq_one_of_mem_mu_of_good_of_deep]
    fin_cases i <;> fin_cases j <;>
      first
        | simpa [Matrix.one_apply] using h1 0 0
        | simpa [Matrix.one_apply] using h1 0 1
        | simpa [Matrix.one_apply] using h1 0 2
        | simpa [Matrix.one_apply] using h1 1 0
        | simpa [Matrix.one_apply] using h1 1 1
        | simpa [Matrix.one_apply] using h1 1 2
        | simpa [Matrix.one_apply] using h1 2 0
        | simpa [Matrix.one_apply] using h1 2 1
        | simpa [Matrix.one_apply] using h1 2 2

/- English proof (translation)
Establish `hg' : g ∈ unipB k (Fin 3) ⊓ KO k (Fin 3)` using `hg`. Use `show th' k g ∈ unipB k (Fin 3) ⊓ KO k (Fin 3)`. Take `⟨hu, hk⟩` from `Subgroup.mem_inf.1 hg'`. Use `Subgroup.mem_inf.2 ⟨?_, ?_⟩` and prove the remaining obligations. Take `⟨hl, hd⟩` from `(mem_unipB k).1 (inv_mem hu)`.

Establish `a` using `hl 1 0 (by decide)`. Establish `b` using `hl 2 0 (by decide)`. Establish `c` using `hl 2 1 (by decide)`. Establish `d0` using `hd 0`. Establish `d1` using `hd 1`.

Establish `d2` using `hd 2`. Use `clear hl hd`. Rewrite using `[mem_unipB]`. Use `⟨fun i j hij => ?_, fun i => ?_⟩` and prove the remaining obligations. Apply the tactic sequence `rw [nu_eq_one_of_mem_n_of_good_of_ok] fin_cases i <;> fin_cases j <;> simp_all`.

Apply the tactic sequence `rw [nu_eq_one_of_mem_n_of_good_of_ok] fin_cases i <;> simp_all`. Rewrite `hk`, the goal using `[← GlAx.Kc_zero]`. Conclude with `exists_rt_ne_cycF_of_good_of_ok 0 g hk`.
-/
private theorem th'_mem_n {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (g : GL (Fin 3) k) (hg : g ∈ (glIwa k 3).N) :
    th' k g ∈ (glIwa k 3).N := by
  have hg' : g ∈ unipB k (Fin 3) ⊓ KO k (Fin 3) := hg
  show th' k g ∈ unipB k (Fin 3) ⊓ KO k (Fin 3)
  obtain ⟨hu, hk⟩ := Subgroup.mem_inf.1 hg'
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · obtain ⟨hl, hd⟩ := (mem_unipB k).1 (inv_mem hu)
    have a := hl 1 0 (by decide)
    have b := hl 2 0 (by decide)
    have c := hl 2 1 (by decide)
    have d0 := hd 0
    have d1 := hd 1
    have d2 := hd 2
    clear hl hd
    rw [mem_unipB]
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · rw [nu_eq_one_of_mem_n_of_good_of_ok]
      fin_cases i <;> fin_cases j <;> simp_all
    · rw [nu_eq_one_of_mem_n_of_good_of_ok]
      fin_cases i <;> simp_all
  · rw [← GlAx.Kc_zero] at hk ⊢
    exact exists_rt_ne_cycF_of_good_of_ok 0 g hk

/- English proof (translation)
Establish `hg' : g ∈ Subgroup.comap (GlobalTheory.CuspRep.invT 3 k) (unipB k (Fin 3)) ⊓ Kc k 3 (c + 1)` using `hg`. Use `show th' k g ∈ Subgroup.comap (GlobalTheory.CuspRep.invT 3 k) (unipB k (Fin 3)) ⊓ Kc k 3 (c + 1)`. Take `⟨hu, hk⟩` from `Subgroup.mem_inf.1 hg'`. Use `Subgroup.mem_inf.2 ⟨?_, exists_rt_ne_cycF_of_good_of_ok _ g hk⟩` and prove the remaining obligations. Take `⟨hl, hd⟩` from `GlAx.mem_low.1 (inv_mem hu)`.

Establish `a` using `hl 0 1 (by decide)`. Establish `b` using `hl 0 2 (by decide)`. Establish `e` using `hl 1 2 (by decide)`. Establish `d0` using `hd 0`. Establish `d1` using `hd 1`.

Establish `d2` using `hd 2`. Use `clear hl hd`. Rewrite using `[GlAx.mem_low]`. Use `⟨fun i j hij => ?_, fun i => ?_⟩` and prove the remaining obligations. Apply the tactic sequence `rw [nu_eq_one_of_mem_n_of_good_of_ok] fin_cases i <;> fin_cases j <;> simp_all`.

Apply the tactic sequence `rw [nu_eq_one_of_mem_n_of_good_of_ok] fin_cases i <;> simp_all`.
-/
private theorem th'_mem_nm {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (c : ℕ) (g : GL (Fin 3) k) (hg : g ∈ (glIwa k 3).Nm c) :
    th' k g ∈ (glIwa k 3).Nm c := by
  have hg' : g ∈ Subgroup.comap (GlobalTheory.CuspRep.invT 3 k) (unipB k (Fin 3)) ⊓ Kc k 3 (c + 1) := hg
  show th' k g ∈ Subgroup.comap (GlobalTheory.CuspRep.invT 3 k) (unipB k (Fin 3)) ⊓ Kc k 3 (c + 1)
  obtain ⟨hu, hk⟩ := Subgroup.mem_inf.1 hg'
  refine Subgroup.mem_inf.2 ⟨?_, exists_rt_ne_cycF_of_good_of_ok _ g hk⟩
  obtain ⟨hl, hd⟩ := GlAx.mem_low.1 (inv_mem hu)
  have a := hl 0 1 (by decide)
  have b := hl 0 2 (by decide)
  have e := hl 1 2 (by decide)
  have d0 := hd 0
  have d1 := hd 1
  have d2 := hd 2
  clear hl hd
  rw [GlAx.mem_low]
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [nu_eq_one_of_mem_n_of_good_of_ok]
    fin_cases i <;> fin_cases j <;> simp_all
  · rw [nu_eq_one_of_mem_n_of_good_of_ok]
    fin_cases i <;> simp_all

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use `show ((g : Matrix (Fin n) (Fin n) k)ᵀ)ᵀ = g`. Conclude with `Matrix.transpose_transpose _`.
-/
private theorem th_th' {k : Type} [Field k] (n : ℕ) (g : GL (Fin n) k) :
    th k n (th k n g) = g := by
  apply Units.ext
  show ((g : Matrix (Fin n) (Fin n) k)ᵀ)ᵀ = g
  exact Matrix.transpose_transpose _

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Rewrite using `[nu_eq_one_of_mem_n_of_good_of_ok, ← map_inv, nu_eq_one_of_mem_n_of_good_of_ok, inv_inv]`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp`.
-/
private theorem th'_th' {k : Type} [Field k] (g : GL (Fin 3) k) :
    th' k (th' k g) = g := by
  apply Units.ext
  ext i j
  rw [nu_eq_one_of_mem_n_of_good_of_ok, ← map_inv, nu_eq_one_of_mem_n_of_good_of_ok, inv_inv]
  fin_cases i <;> fin_cases j <;> simp

/- English proof (translation)
Establish `e1 : ∀ g : GL (Fin 3) k, (th' k g).1 = (Phi k).1 * ((g⁻¹).1)ᵀ * ((Phi k)⁻¹).1` using `fun g => rfl`. Establish `e2 : ∀ g : GL (Fin 3) k, ((th' k g)⁻¹).1 = (Phi k).1 * (g.1)ᵀ * ((Phi k)⁻¹).1`. Introduce `g`. Rewrite using `[← map_inv, e1, inv_inv]`. Use `Units.continuous_iff.2 ⟨?_, ?_⟩` and prove the remaining obligations.

Simplify using `only [Function.comp_def, e1]`. Conclude with `(continuous_const.matrix_mul Units.continuous_coe_inv.matrix_transpose).matrix_mul continuous_const`. Simplify using `only [e2]`. Conclude with `(continuous_const.matrix_mul Units.continuous_val.matrix_transpose).matrix_mul continuous_const`.
-/
private theorem continuous_th'' {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : Continuous (th' k) := by
  have e1 : ∀ g : GL (Fin 3) k, (th' k g).1 = (Phi k).1 * ((g⁻¹).1)ᵀ * ((Phi k)⁻¹).1 := fun g => rfl
  have e2 : ∀ g : GL (Fin 3) k, ((th' k g)⁻¹).1 = (Phi k).1 * (g.1)ᵀ * ((Phi k)⁻¹).1 := by
    intro g
    rw [← map_inv, e1, inv_inv]
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · simp only [Function.comp_def, e1]
    exact (continuous_const.matrix_mul Units.continuous_coe_inv.matrix_transpose).matrix_mul
      continuous_const
  · simp only [e2]
    exact (continuous_const.matrix_mul Units.continuous_val.matrix_transpose).matrix_mul
      continuous_const

/- English proof (translation)
Introduce `k _ _ _ _ V`. Establish `hT : ∀ g ∈ V.TH 3, th' k g ∈ V.TH 3`. Introduce `g hg`. Unfold `Lev.TH at hg ⊢`. Take `⟨t, ht, rfl⟩` from `Subgroup.mem_map.1 hg`.

Rewrite using `[mul_self_eq_one_and_nu_neg_one_of_isCC]`. Use `Subgroup.mem_map.2 ⟨_, ?_, rfl⟩` and prove the remaining obligations. Rewrite `ht`, the goal using `[Subgroup.mem_pi]`. Introduce `i _`. Apply the tactic sequence `fin_cases i <;> simp <;> first`.

Consider the case `exact ht _ (Set.mem_univ _)`. Consider the case `exact inv_mem (ht _ (Set.mem_univ _))`. Establish `hP : Pres V (th' k)` using `⟨continuous_th'', th'_th', th'_mem_n, hT, th'_mem_nm, exists_rt_ne_cycF_of_good_of_ok⟩`. Use `⟨hP, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `hJ : V.J 3 ≤ (V.J 3).comap (th' k)`.

Use `sup_le (sup_le ?_ ?_) ?_` and prove the remaining obligations. Introduce `g hg`. Conclude with `V.N_le (th'_mem_n g hg)`. Introduce `g hg`. Conclude with `V.TH_le (hT g hg)`.

Introduce `g hg`. Conclude with `V.Nm_le (th'_mem_nm V.c g hg)`. Introduce `g hg`. Conclude with `hJ hg`. Introduce `x y z`.

Simplify using `[dg, mul_self_eq_one_and_nu_neg_one_of_isCC]`. Conclude with `th_th'`. Apply `Units.ext show (!![0, 0, 1; 0, -1, 0; 1, 0, 0] : Matrix (Fin 3) (Fin 3) k)ᵀ = !![0, 0, 1; 0, -1, 0; 1, 0, 0]` to reduce the goal to its premises. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp`.

Apply `Units.ext` to reduce the goal to its premises. Both sides reduce to the same expression. Introduce `g`. Simplify using `[th', MulAut.conj_apply, mul_assoc]`.
-/
theorem UpperTheory.V.Z.Sym.Sig.thFacts : UpperTheory.V.Z.Sym.Sig.ThFacts := by
  intro k _ _ _ _ V
  have hT : ∀ g ∈ V.TH 3, th' k g ∈ V.TH 3 := by
    intro g hg
    unfold Lev.TH at hg ⊢
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hg
    rw [mul_self_eq_one_and_nu_neg_one_of_isCC]
    refine Subgroup.mem_map.2 ⟨_, ?_, rfl⟩
    rw [Subgroup.mem_pi] at ht ⊢
    intro i _
    fin_cases i <;> simp <;>
      first
        | exact ht _ (Set.mem_univ _)
        | exact inv_mem (ht _ (Set.mem_univ _))
  have hP : Pres V (th' k) :=
    ⟨continuous_th'', th'_th', th'_mem_n, hT, th'_mem_nm, exists_rt_ne_cycF_of_good_of_ok⟩
  refine ⟨hP, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hJ : V.J 3 ≤ (V.J 3).comap (th' k) := by
      refine sup_le (sup_le ?_ ?_) ?_
      · intro g hg
        exact V.N_le (th'_mem_n g hg)
      · intro g hg
        exact V.TH_le (hT g hg)
      · intro g hg
        exact V.Nm_le (th'_mem_nm V.c g hg)
    intro g hg
    exact hJ hg
  · intro x y z
    simp [dg, mul_self_eq_one_and_nu_neg_one_of_isCC]
  · exact th_th'
  · apply Units.ext
    show (!![0, 0, 1; 0, -1, 0; 1, 0, 0] : Matrix (Fin 3) (Fin 3) k)ᵀ = !![0, 0, 1; 0, -1, 0; 1, 0, 0]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · apply Units.ext
    rfl
  · intro g
    simp [th', MulAut.conj_apply, mul_assoc]

end
