import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.StGenusOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.DictPlan

noncomputable section

namespace PIW.AdelClassFin

open Formalism.MainNotions.S PI.AdelClassFin NumberField
open scoped TensorProduct Matrix

def StLatFin : Prop :=
  ∀ (I : AutInst) (g : ℕ), 1 ≤ g → ∃ R : Finset (Fin I.n → I.E ⊗[I.F] Af I.F), (∀ r ∈ R, r ∈ I.Lf) ∧
    ∀ y ∈ I.Lf, ∃ r ∈ R, ∃ z ∈ I.Lf, y - r = (g : I.E ⊗[I.F] Af I.F) • z

/- English proof (translation)
The claim follows from `(hk y).mp hy`.
-/
theorem kset_mulVec_mem (I : AutInst) {k : I.Gf} (hk : k ∈ I.Kset) {y : Fin I.n → I.E ⊗[I.F] Af I.F}
    (hy : y ∈ I.Lf) : I.fmat k *ᵥ y ∈ I.Lf := (hk y).mp hy

/- English proof (translation)
Use `show ((k⁻¹ : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) ∈ Formalism.UG.stabGL I.Lf`. Rewrite using `[Subgroup.coe_inv]`. Conclude with `Subgroup.inv_mem _ hk`.
-/
theorem kset_inv (I : AutInst) {k : I.Gf} (hk : k ∈ I.Kset) : k⁻¹ ∈ I.Kset := by
  show ((k⁻¹ : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) ∈ Formalism.UG.stabGL I.Lf
  rw [Subgroup.coe_inv]
  exact Subgroup.inv_mem _ hk

/- English proof (translation)
Use `show ((k * t : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) ∈ Formalism.UG.stabGL I.Lf`. Rewrite using `[Subgroup.coe_mul]`. Conclude with `Subgroup.mul_mem _ hk ht`.
-/
theorem kset_mul (I : AutInst) {k t : I.Gf} (hk : k ∈ I.Kset) (ht : t ∈ I.Kset) : k * t ∈ I.Kset := by
  show ((k * t : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) ∈ Formalism.UG.stabGL I.Lf
  rw [Subgroup.coe_mul]
  exact Subgroup.mul_mem _ hk ht

/- English proof (translation)
Introduce `I g hg`. Take `⟨R, hRLf, hR⟩` from `hL I g hg`. Use `choose! rep hrepR z hz hrepEq using hR`. Set `Ψ : I.Kset → (R → R)` to `fun k r => ⟨rep (I.fmat k *ᵥ (r : Fin I.n → I.E ⊗[I.F] Af I.F)), hrepR _ (kset_mulVec_mem I k.2 (hRLf r r.2))⟩`. Use `⟨Finset.univ.image (fun φ : R → R => if h : ∃ k, Ψ k = φ then ((h.choose : I.Kset) : I.Gf) else 1), ?_⟩` and prove the remaining obligations.

Introduce `k hk`. Establish `hex : ∃ k', Ψ k' = Ψ ⟨k, hk⟩` using `⟨_, rfl⟩`. Take `⟨t, htdef⟩ : ∃ t : I.Kset, t = hex.choose` from `⟨_, rfl⟩`. Establish `htΨ : Ψ t = Ψ ⟨k, hk⟩` using `by rw [htdef]; exact hex.choose_spec`. Use `⟨(t : I.Gf), Finset.mem_image.mpr ⟨Ψ ⟨k, hk⟩, Finset.mem_univ _, by rw [dif_pos hex, htdef]⟩, (t : I.Gf)⁻¹ * k, ?_, (mul_inv_cancel_left (t : I.Gf) k).symm⟩` and prove the remaining obligations.

Use `⟨kset_mul I (kset_inv I t.2) hk, ?_⟩` and prove the remaining obligations. Introduce `y hy`. Establish `hrR : rep y ∈ R` using `hrepR y hy`. Establish `hkr` using `hrepEq (I.fmat k *ᵥ rep y) (kset_mulVec_mem I hk (hRLf _ hrR))`. Establish `htr` using `hrepEq (I.fmat t *ᵥ rep y) (kset_mulVec_mem I t.2 (hRLf _ hrR))`.

Establish `hrep_eq : rep (I.fmat k *ᵥ rep y) = rep (I.fmat t *ᵥ rep y)`. Establish `h1` using `congrFun htΨ ⟨rep y, hrR⟩`. Conclude with `(congrArg Subtype.val h1).symm`. Establish `hfu : I.fmat ((t : I.Gf)⁻¹ * k) = I.fmat (t : I.Gf)⁻¹ * I.fmat k`. Simplify using `only [Formalism.MainNotions.S.AutInst.fmat, Subgroup.coe_mul, Units.val_mul]`.

Establish `hinv : I.fmat (t : I.Gf)⁻¹ * I.fmat t = 1`. Simplify using `only [Formalism.MainNotions.S.AutInst.fmat, Subgroup.coe_inv, Units.inv_mul]`. Use `⟨I.fmat (t : I.Gf)⁻¹ *ᵥ ((z (I.fmat k *ᵥ rep y) - z (I.fmat t *ᵥ rep y)) + (I.fmat k *ᵥ z y - I.fmat t *ᵥ z y)), ?_, ?_⟩` and prove the remaining obligations. Apply `kset_mulVec_mem I (kset_inv I t.2)` to reduce the goal to its premises. Conclude with `I.Lf.add_mem (I.Lf.sub_mem (hz _ (kset_mulVec_mem I hk (hRLf _ hrR))) (hz _ (kset_mulVec_mem I t.2 (hRLf _ hrR)))) (I.Lf.sub_mem (kset_mulVec_mem I hk (hz y hy)) (kset_mulVec_mem I t.2 (hz y hy)))`.

Establish `hyd : y = rep y + (g : I.E ⊗[I.F] Af I.F) • z y` using `by rw [← hrepEq y hy, add_sub_cancel]`. Establish `hkrd : I.fmat k *ᵥ rep y = rep (I.fmat k *ᵥ rep y) + (g : I.E ⊗[I.F] Af I.F) • z (I.fmat k *ᵥ rep y)` using `by rw [← hkr, add_sub_cancel]`. Establish `htrd : I.fmat t *ᵥ rep y = rep (I.fmat t *ᵥ rep y) + (g : I.E ⊗[I.F] Af I.F) • z (I.fmat t *ᵥ rep y)` using `by rw [← htr, add_sub_cancel]`. Establish `hy' : y = I.fmat (t : I.Gf)⁻¹ *ᵥ (I.fmat t *ᵥ y)`. Rewrite using `[Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]`.

Establish `hdiff : I.fmat k *ᵥ y - I.fmat t *ᵥ y = (g : I.E ⊗[I.F] Af I.F) • ((z (I.fmat k *ᵥ rep y) - z (I.fmat t *ᵥ rep y)) + (I.fmat k *ᵥ z y - I.fmat t *ᵥ z y))` using `by conv_lhs => rw [hyd, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hkrd, htrd, hrep_eq]`. Rewrite using `[smul_add, smul_sub, smul_sub]`. Normalize the expressions using the abelian group laws. Rewrite using `[hfu, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, Matrix.one_mulVec]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← hy']`. Use `_ = I.fmat (t : I.Gf)⁻¹ *ᵥ (I.fmat k *ᵥ y - I.fmat t *ᵥ y) := (Matrix.mulVec_sub _ _ _).symm`. Use `_ = _ := by rw [hdiff, Matrix.mulVec_smul]`.
-/
theorem stKFin_of (hL : StLatFin) : StKFin := by
  classical
  intro I g hg
  obtain ⟨R, hRLf, hR⟩ := hL I g hg
  choose! rep hrepR z hz hrepEq using hR
  let Ψ : I.Kset → (R → R) := fun k r =>
    ⟨rep (I.fmat k *ᵥ (r : Fin I.n → I.E ⊗[I.F] Af I.F)),
      hrepR _ (kset_mulVec_mem I k.2 (hRLf r r.2))⟩
  refine ⟨Finset.univ.image (fun φ : R → R =>
    if h : ∃ k, Ψ k = φ then ((h.choose : I.Kset) : I.Gf) else 1), ?_⟩
  intro k hk
  have hex : ∃ k', Ψ k' = Ψ ⟨k, hk⟩ := ⟨_, rfl⟩
  obtain ⟨t, htdef⟩ : ∃ t : I.Kset, t = hex.choose := ⟨_, rfl⟩
  have htΨ : Ψ t = Ψ ⟨k, hk⟩ := by rw [htdef]; exact hex.choose_spec
  refine ⟨(t : I.Gf), Finset.mem_image.mpr ⟨Ψ ⟨k, hk⟩, Finset.mem_univ _, by rw [dif_pos hex, htdef]⟩,
    (t : I.Gf)⁻¹ * k, ?_, (mul_inv_cancel_left (t : I.Gf) k).symm⟩
  refine ⟨kset_mul I (kset_inv I t.2) hk, ?_⟩
  intro y hy
  have hrR : rep y ∈ R := hrepR y hy
  have hkr := hrepEq (I.fmat k *ᵥ rep y) (kset_mulVec_mem I hk (hRLf _ hrR))
  have htr := hrepEq (I.fmat t *ᵥ rep y) (kset_mulVec_mem I t.2 (hRLf _ hrR))
  have hrep_eq : rep (I.fmat k *ᵥ rep y) = rep (I.fmat t *ᵥ rep y) := by
    have h1 := congrFun htΨ ⟨rep y, hrR⟩
    exact (congrArg Subtype.val h1).symm
  have hfu : I.fmat ((t : I.Gf)⁻¹ * k) = I.fmat (t : I.Gf)⁻¹ * I.fmat k := by
    simp only [Formalism.MainNotions.S.AutInst.fmat, Subgroup.coe_mul, Units.val_mul]
  have hinv : I.fmat (t : I.Gf)⁻¹ * I.fmat t = 1 := by
    simp only [Formalism.MainNotions.S.AutInst.fmat, Subgroup.coe_inv, Units.inv_mul]
  refine ⟨I.fmat (t : I.Gf)⁻¹ *ᵥ ((z (I.fmat k *ᵥ rep y) - z (I.fmat t *ᵥ rep y)) +
      (I.fmat k *ᵥ z y - I.fmat t *ᵥ z y)), ?_, ?_⟩
  · apply kset_mulVec_mem I (kset_inv I t.2)
    exact I.Lf.add_mem (I.Lf.sub_mem (hz _ (kset_mulVec_mem I hk (hRLf _ hrR)))
      (hz _ (kset_mulVec_mem I t.2 (hRLf _ hrR))))
      (I.Lf.sub_mem (kset_mulVec_mem I hk (hz y hy)) (kset_mulVec_mem I t.2 (hz y hy)))
  · have hyd : y = rep y + (g : I.E ⊗[I.F] Af I.F) • z y := by rw [← hrepEq y hy, add_sub_cancel]
    have hkrd : I.fmat k *ᵥ rep y = rep (I.fmat k *ᵥ rep y) +
        (g : I.E ⊗[I.F] Af I.F) • z (I.fmat k *ᵥ rep y) := by rw [← hkr, add_sub_cancel]
    have htrd : I.fmat t *ᵥ rep y = rep (I.fmat t *ᵥ rep y) +
        (g : I.E ⊗[I.F] Af I.F) • z (I.fmat t *ᵥ rep y) := by rw [← htr, add_sub_cancel]
    have hy' : y = I.fmat (t : I.Gf)⁻¹ *ᵥ (I.fmat t *ᵥ y) := by
      rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
    have hdiff : I.fmat k *ᵥ y - I.fmat t *ᵥ y = (g : I.E ⊗[I.F] Af I.F) •
        ((z (I.fmat k *ᵥ rep y) - z (I.fmat t *ᵥ rep y)) + (I.fmat k *ᵥ z y - I.fmat t *ᵥ z y)) := by
      conv_lhs => rw [hyd, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
        hkrd, htrd, hrep_eq]
      rw [smul_add, smul_sub, smul_sub]
      abel
    rw [hfu, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, Matrix.one_mulVec]
    calc I.fmat (t : I.Gf)⁻¹ *ᵥ (I.fmat k *ᵥ y) - y
        = I.fmat (t : I.Gf)⁻¹ *ᵥ (I.fmat k *ᵥ y) - I.fmat (t : I.Gf)⁻¹ *ᵥ (I.fmat t *ᵥ y) := by
          rw [← hy']
      _ = I.fmat (t : I.Gf)⁻¹ *ᵥ (I.fmat k *ᵥ y - I.fmat t *ᵥ y) := (Matrix.mulVec_sub _ _ _).symm
      _ = _ := by rw [hdiff, Matrix.mulVec_smul]

/- English proof (translation)
Establish `hZfg : (I.L.restrictScalars ℤ).FG` using `I.L_fg.restrictScalars`. Take `⟨m, s, hs⟩` from `Submodule.fg_iff_exists_fin_generating_family.mp hZfg`. Establish `hmem : ∀ v, v ∈ I.L ↔ ∃ c : Fin m → ℤ, ∑ i, c i • s i = v`. Introduce `v`. Rewrite using `[← Submodule.restrictScalars_mem ℤ, ← hs, Submodule.mem_span_range_iff_exists_fun]`.

Establish `hsL : ∀ i, s i ∈ I.L` using `fun i => (hmem (s i)).mpr ⟨Pi.single i 1, by simp [Pi.single_apply]⟩`. Establish `hcomb : ∀ c : Fin m → ℤ, ∑ i, c i • s i ∈ I.L` using `fun c => (hmem _).mpr ⟨c, rfl⟩`. Use `⟨(Fintype.piFinset fun _ : Fin m => Finset.range g).image (fun c : Fin m → ℕ => ∑ i, ((c i : ℕ) : ℤ) • s i), ?_, ?_⟩` and prove the remaining obligations. Introduce `r hr`. Take `⟨c, -, rfl⟩` from `Finset.mem_image.mp hr`.

Conclude with `hcomb _`. Introduce `l hl`. Take `⟨c, rfl⟩` from `(hmem l).mp hl`. Establish `hg0 : (g : ℤ) ≠ 0` using `by exact_mod_cast hgpos.ne'`. Use `⟨∑ i, (((c i % g).toNat : ℕ) : ℤ) • s i, Finset.mem_image.mpr ⟨fun i => (c i % g).toNat, ?_, rfl⟩, ∑ i, (c i / g) • s i, hcomb _, ?_⟩` and prove the remaining obligations.

Rewrite using `[Fintype.mem_piFinset]`. Introduce `i`. Rewrite using `[Finset.mem_range]`. Establish `h1` using `Int.emod_nonneg (c i) hg0`. Establish `h2` using `Int.emod_lt_of_pos (c i) (by exact_mod_cast hgpos : (0 : ℤ) < g)`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[Finset.smul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[smul_smul, ← add_smul, Int.toNat_of_nonneg (Int.emod_nonneg (c i) hg0), add_comm, Int.mul_ediv_add_emod]`.
-/
theorem lat_mod_fin (I : AutInst) (g : ℕ) (hgpos : 0 < g) : ∃ R : Finset (Fin I.n → I.E), (∀ r ∈ R, r ∈ I.L) ∧
    ∀ l ∈ I.L, ∃ r ∈ R, ∃ l' ∈ I.L, l = r + (g : ℤ) • l' := by
  classical
  have hZfg : (I.L.restrictScalars ℤ).FG := I.L_fg.restrictScalars
  obtain ⟨m, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hZfg
  have hmem : ∀ v, v ∈ I.L ↔ ∃ c : Fin m → ℤ, ∑ i, c i • s i = v := by
    intro v
    rw [← Submodule.restrictScalars_mem ℤ, ← hs, Submodule.mem_span_range_iff_exists_fun]
  have hsL : ∀ i, s i ∈ I.L := fun i => (hmem (s i)).mpr ⟨Pi.single i 1, by simp [Pi.single_apply]⟩
  have hcomb : ∀ c : Fin m → ℤ, ∑ i, c i • s i ∈ I.L := fun c => (hmem _).mpr ⟨c, rfl⟩
  refine ⟨(Fintype.piFinset fun _ : Fin m => Finset.range g).image
    (fun c : Fin m → ℕ => ∑ i, ((c i : ℕ) : ℤ) • s i), ?_, ?_⟩
  · intro r hr
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hr
    exact hcomb _
  · intro l hl
    obtain ⟨c, rfl⟩ := (hmem l).mp hl
    have hg0 : (g : ℤ) ≠ 0 := by exact_mod_cast hgpos.ne'
    refine ⟨∑ i, (((c i % g).toNat : ℕ) : ℤ) • s i, Finset.mem_image.mpr ⟨fun i => (c i % g).toNat, ?_, rfl⟩,
      ∑ i, (c i / g) • s i, hcomb _, ?_⟩
    · rw [Fintype.mem_piFinset]
      intro i
      rw [Finset.mem_range]
      have h1 := Int.emod_nonneg (c i) hg0
      have h2 := Int.emod_lt_of_pos (c i) (by exact_mod_cast hgpos : (0 : ℤ) < g)
      omega
    · rw [Finset.smul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul, ← add_smul, Int.toNat_of_nonneg (Int.emod_nonneg (c i) hg0), add_comm, Int.mul_ediv_add_emod]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[iv, zsmul_eq_mul]`.
-/
theorem iv_add_smul (I : AutInst) (r l : Fin I.n → I.E) (g : ℕ) :
    iv I (r + (g : ℤ) • l) = iv I r + (g : I.E ⊗[I.F] Af I.F) • iv I l := by
  funext i
  simp [iv, zsmul_eq_mul]

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨⟨l, hl⟩, rfl⟩`.
-/
theorem iv_mem (I : AutInst) {l : Fin I.n → I.E} (hl : l ∈ I.L) : iv I l ∈ I.Lf := Submodule.subset_span ⟨⟨l, hl⟩, rfl⟩

/- English proof (translation)
Introduce `I g hg`. Take `⟨R, hRL, hR⟩` from `lat_mod_fin I g (by omega)`. Use `⟨R.image (iv I), ?_, ?_⟩` and prove the remaining obligations. Introduce `r hr`. Take `⟨r0, hr0, rfl⟩` from `Finset.mem_image.mp hr`.

Conclude with `iv_mem I (hRL r0 hr0)`. Introduce `y hy`. Take `⟨l, hl, y', hy', hyeq⟩` from `h I g (by omega) y hy`. Take `⟨r, hr, l', hl', hleq⟩` from `hR l hl`. Use `⟨iv I r, Finset.mem_image_of_mem _ hr, iv I l' + y', I.Lf.add_mem (iv_mem I hl') hy', ?_⟩` and prove the remaining obligations.

Rewrite using `[hyeq, hleq, iv_add_smul, smul_add]`. Normalize the expressions using the abelian group laws.
-/
theorem stLatFin_of (h : LDense) : StLatFin := by
  intro I g hg
  obtain ⟨R, hRL, hR⟩ := lat_mod_fin I g (by omega)
  classical
  refine ⟨R.image (iv I), ?_, ?_⟩
  · intro r hr
    obtain ⟨r0, hr0, rfl⟩ := Finset.mem_image.mp hr
    exact iv_mem I (hRL r0 hr0)
  · intro y hy
    obtain ⟨l, hl, y', hy', hyeq⟩ := h I g (by omega) y hy
    obtain ⟨r, hr, l', hl', hleq⟩ := hR l hl
    refine ⟨iv I r, Finset.mem_image_of_mem _ hr, iv I l' + y', I.Lf.add_mem (iv_mem I hl') hy', ?_⟩
    rw [hyeq, hleq, iv_add_smul, smul_add]
    abel

/- English proof (translation)
The claim follows from `stKFin_of (stLatFin_of h)`.
-/
theorem stKFin_of_dense (h : LDense) : StKFin := stKFin_of (stLatFin_of h)

end PIW.AdelClassFin
