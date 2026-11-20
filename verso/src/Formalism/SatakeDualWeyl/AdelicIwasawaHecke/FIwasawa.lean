import Formalism.SatakeDualWeyl.StatementF
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FIwasawaE

open Formalism.UG Matrix

namespace Formalism.UG.P

section FIwasawaFinal

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

/- English proof (translation)
Establish `hx' : Valued.v x ≠ 0` using `(Valuation.ne_zero_iff _).mpr hx`. Establish `hy' : Valued.v y ≠ 0` using `(Valuation.ne_zero_iff _).mpr hy`. Establish `hxy' : Valued.v (x * y) ≠ 0` using `by rw [map_mul]; exact mul_ne_zero hx' hy'`. Unfold `Formalism.UG.ordL`. Rewrite using `[dif_neg hxy', dif_neg hx', dif_neg hy']`.

Establish `key : WithZero.unzero hxy' = WithZero.unzero hx' * WithZero.unzero hy'`. Apply `WithZero.coe_injective` to reduce the goal to its premises. Simplify using `only [WithZero.coe_mul, WithZero.coe_unzero, map_mul]`. Rewrite using `[key, toAdd_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fIwasawa_ordL_mul (x y : L) (hx : x ≠ 0) (hy : y ≠ 0) :
    ordL (x * y) = ordL x + ordL y := by
  have hx' : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  have hy' : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).mpr hy
  have hxy' : Valued.v (x * y) ≠ 0 := by rw [map_mul]; exact mul_ne_zero hx' hy'
  unfold Formalism.UG.ordL
  rw [dif_neg hxy', dif_neg hx', dif_neg hy']
  have key : WithZero.unzero hxy' = WithZero.unzero hx' * WithZero.unzero hy' := by
    apply WithZero.coe_injective
    simp only [WithZero.coe_mul, WithZero.coe_unzero, map_mul]
  rw [key, toAdd_mul]
  ring

/- English proof (translation)
Establish `h1 : Valued.v y * Valued.v x = 1`. Use `congrArg Valued.v hxy` as an intermediate fact. Rewrite `this` using `[map_mul, map_one]`. Then use the resulting hypothesis. Establish `hge : 1 ≤ Valued.v x`. Combine the equalities or inequalities in the displayed calculation.

Establish `hv : Valued.v x = 1` using `le_antisymm hx hge`. Establish `hne : Valued.v x ≠ 0` using `by rw [hv]; exact one_ne_zero`. Unfold `Formalism.UG.ordL`. Rewrite using `[dif_neg hne]`. Establish `key : WithZero.unzero hne = 1`.

Apply `WithZero.coe_injective` to reduce the goal to its premises. Rewrite using `[WithZero.coe_unzero, hv, WithZero.coe_one]`. Rewrite using `[key, toAdd_one, neg_zero]`.
-/
theorem fIwasawa_ordL_unit (x y : L) (hx : Valued.v x ≤ 1) (hy : Valued.v y ≤ 1)
    (hxy : y * x = 1) : ordL x = 0 := by
  have h1 : Valued.v y * Valued.v x = 1 := by
    have := congrArg Valued.v hxy
    rwa [map_mul, map_one] at this
  have hge : 1 ≤ Valued.v x :=
    calc (1 : WithZero (Multiplicative ℤ)) = Valued.v y * Valued.v x := h1.symm
      _ ≤ 1 * Valued.v x := by gcongr
      _ = Valued.v x := one_mul _
  have hv : Valued.v x = 1 := le_antisymm hx hge
  have hne : Valued.v x ≠ 0 := by rw [hv]; exact one_ne_zero
  unfold Formalism.UG.ordL
  rw [dif_neg hne]
  have key : WithZero.unzero hne = 1 := by
    apply WithZero.coe_injective
    rw [WithZero.coe_unzero, hv, WithZero.coe_one]
  rw [key, toAdd_one, neg_zero]

variable (σ : L →+* L) {n m : ℕ} (q : ℕ) (α : Fin m → ℂ)

/- English proof (translation)
Rewrite using `[Matrix.mul_apply]`. Apply `Finset.sum_eq_single i` to reduce the goal to its premises. Introduce `k _ hki`. Break down `lt_or_gt_of_ne hki with h | h` into its components or cases. Rewrite using `[hB (show id k < id i from h), zero_mul]`.

Rewrite using `[hC (show id i < id k from h), mul_zero]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ i) h`.
-/
private lemma blockTriangular_mul_diag (B C : Matrix (Fin n) (Fin n) L)
    (hB : B.BlockTriangular id) (hC : C.BlockTriangular id) (i : Fin n) :
    (B * C) i i = B i i * C i i := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_single i
  · intro k _ hki
    rcases lt_or_gt_of_ne hki with h | h
    · rw [hB (show id k < id i from h), zero_mul]
    · rw [hC (show id i < id k from h), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

/- English proof (translation)
Establish `hdet : (g : Matrix (Fin n) (Fin n) L).det ≠ 0`. Introduce `h0`. Establish `h1` using `congrArg Matrix.det (Units.mul_inv g)`. Rewrite `h1` using `[Matrix.det_mul, h0, zero_mul, Matrix.det_one]`. Conclude with `zero_ne_one h1`.

Rewrite `hdet` using `[Matrix.det_of_upperTriangular hg]`. Conclude with `Finset.prod_ne_zero_iff.mp hdet i (Finset.mem_univ _)`.
-/
private lemma GL_blockTriangular_diag_ne_zero (g : GL (Fin n) L)
    (hg : (g : Matrix (Fin n) (Fin n) L).BlockTriangular id) (i : Fin n) :
    (g : Matrix (Fin n) (Fin n) L) i i ≠ 0 := by
  have hdet : (g : Matrix (Fin n) (Fin n) L).det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det (Units.mul_inv g)
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h1
    exact zero_ne_one h1
  rw [Matrix.det_of_upperTriangular hg] at hdet
  exact Finset.prod_ne_zero_iff.mp hdet i (Finset.mem_univ _)

/- English proof (translation)
Establish `hdb` using `GL_blockTriangular_diag_ne_zero (b : GL (Fin n) L) hb`. Establish `hdc` using `GL_blockTriangular_diag_ne_zero (c : GL (Fin n) L) hc`. Establish `hbc : ∀ i : Fin n, (((b * c : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i = ((b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i * ((c : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i` using `fun i => blockTriangular_mul_diag _ _ hb hc i`. Unfold `Formalism.UG.chiDeltaU`. Rewrite using `[← Finset.prod_mul_distrib]`.

Use `Finset.prod_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Use `split_ifs with h`. Rewrite using `[hbc ⟨i.val, h⟩, fIwasawa_ordL_mul _ _ (hdb ⟨i.val, h⟩) (hdc ⟨i.val, h⟩)]`. Rewrite using `[zpow_add₀ (hα i), neg_add, add_mul, zpow_add₀ hq]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[mul_one]`.
-/
theorem fIwasawa_chi_mul (hα : ∀ i, α i ≠ 0) (hq : (q : ℂ) ≠ 0) (b c : GU σ n)
    (hb : ((b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).BlockTriangular id)
    (hc : ((c : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).BlockTriangular id) :
    chiDeltaU q α (b * c) = chiDeltaU q α b * chiDeltaU q α c := by
  have hdb := GL_blockTriangular_diag_ne_zero (b : GL (Fin n) L) hb
  have hdc := GL_blockTriangular_diag_ne_zero (c : GL (Fin n) L) hc
  have hbc : ∀ i : Fin n, (((b * c : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i =
      ((b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i * ((c : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i :=
    fun i => blockTriangular_mul_diag _ _ hb hc i
  unfold Formalism.UG.chiDeltaU
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  split_ifs with h
  · rw [hbc ⟨i.val, h⟩, fIwasawa_ordL_mul _ _ (hdb ⟨i.val, h⟩) (hdc ⟨i.val, h⟩)]
    rw [zpow_add₀ (hα i), neg_add, add_mul, zpow_add₀ hq]
    ring
  · rw [mul_one]

/- English proof (translation)
Rewrite using `[Matrix.coe_units_inv]`. Conclude with `Matrix.blockTriangular_inv_of_blockTriangular hg`.
-/
private lemma GL_inv_blockTriangular (g : GL (Fin n) L)
    (hg : (g : Matrix (Fin n) (Fin n) L).BlockTriangular id) :
    ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).BlockTriangular id := by
  rw [Matrix.coe_units_inv]
  exact Matrix.blockTriangular_inv_of_blockTriangular hg

/- English proof (translation)
Rewrite `hg` using `[Formalism.UG.KU, Subgroup.mem_subgroupOf, Formalism.UG.intPts, Subgroup.mem_inf]`. Take `⟨g', hg'⟩` from `MonoidHom.mem_range.mp hg.2`. Rewrite using `[← hg', ← map_inv]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Conclude with `(Valuation.mem_integer_iff _ _).mp ((g' : Matrix (Fin n) (Fin n) (intL L)) i j).2`.

Conclude with `(Valuation.mem_integer_iff _ _).mp (((g'⁻¹ : GL (Fin n) (intL L)) : Matrix (Fin n) (Fin n) (intL L)) i j).2`.
-/
private lemma KU_entries_valuation_le_one (g : GU σ n) (hg : g ∈ KU σ n) (i j : Fin n) :
    Valued.v (((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j) ≤ 1 ∧
    Valued.v ((((g : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j) ≤ 1 := by
  rw [Formalism.UG.KU, Subgroup.mem_subgroupOf, Formalism.UG.intPts, Subgroup.mem_inf] at hg
  obtain ⟨g', hg'⟩ := MonoidHom.mem_range.mp hg.2
  rw [← hg', ← map_inv]
  refine ⟨?_, ?_⟩
  · exact (Valuation.mem_integer_iff _ _).mp ((g' : Matrix (Fin n) (Fin n) (intL L)) i j).2
  · exact (Valuation.mem_integer_iff _ _).mp
      (((g'⁻¹ : GL (Fin n) (intL L)) : Matrix (Fin n) (Fin n) (intL L)) i j).2

/- English proof (translation)
Establish `hbinv` using `GL_inv_blockTriangular (b : GL (Fin n) L) hb`. Unfold `Formalism.UG.chiDeltaU`. Apply `Finset.prod_eq_one` to reduce the goal to its premises. Introduce `i _`. Use `split_ifs with h`.

Establish `h0 : ordL (((b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) ⟨i.val, h⟩ ⟨i.val, h⟩) = 0`. Apply `fIwasawa_ordL_unit _ ((((b : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) ⟨i.val, h⟩ ⟨i.val, h⟩) (KU_entries_valuation_le_one σ b hk _ _).1 (KU_entries_valuation_le_one σ b hk _ _).2` to reduce the goal to its premises. Rewrite using `[← blockTriangular_mul_diag _ _ hbinv hb, Units.inv_mul]`. Conclude with `Matrix.one_apply_eq _`. Rewrite using `[h0]`.

Simplify using the standard rewrite rules. Both sides reduce to the same expression.
-/
theorem fIwasawa_chi_int (b : GU σ n)
    (hb : ((b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).BlockTriangular id) (hk : b ∈ KU σ n) :
    chiDeltaU q α b = 1 := by
  have hbinv := GL_inv_blockTriangular (b : GL (Fin n) L) hb
  unfold Formalism.UG.chiDeltaU
  apply Finset.prod_eq_one
  intro i _
  split_ifs with h
  · have h0 : ordL (((b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) ⟨i.val, h⟩ ⟨i.val, h⟩) = 0 := by
      apply fIwasawa_ordL_unit _ ((((b : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) ⟨i.val, h⟩ ⟨i.val, h⟩)
        (KU_entries_valuation_le_one σ b hk _ _).1 (KU_entries_valuation_le_one σ b hk _ _).2
      rw [← blockTriangular_mul_diag _ _ hbinv hb, Units.inv_mul]
      exact Matrix.one_apply_eq _
    rw [h0]
    simp
  · rfl

/- English proof (translation)
Take `⟨k, hk, hup⟩` from `fIwasawa_upper σ hσ hσv _ (fIwasawa_mem_un σ g⁻¹)`. Establish `hkG : fIwasawaMk σ k hk.1 ∈ KU σ n` using `fIwasawa_mk_mem_K σ hσv k hk.1 hk.2`. Use `⟨(fIwasawaMk σ k hk.1 * g⁻¹)⁻¹, fIwasawaMk σ k hk.1, ?_, hkG, by group⟩` and prove the remaining obligations. Establish `h1 : (((fIwasawaMk σ k hk.1 * g⁻¹ : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).BlockTriangular id`. Rewrite using `[Subgroup.coe_mul, Units.val_mul, fIwasawa_mk_val]`.

Conclude with `hup`. Establish `h2` using `spherical_upper_inv _ h1`. Rewrite `h2` using `[← Subgroup.coe_inv]`. Conclude with `(spherical_upper_iff _).2 h2`.
-/
theorem fIwasawa_iwasawa (hσ : ∀ x, σ (σ x) = x) (hσv : ∀ x, Valued.v (σ x) = Valued.v x)
    (g : GU σ n) : ∃ b k : GU σ n, IsBorelU b ∧ k ∈ KU σ n ∧ g = b * k := by
  obtain ⟨k, hk, hup⟩ := fIwasawa_upper σ hσ hσv _ (fIwasawa_mem_un σ g⁻¹)
  have hkG : fIwasawaMk σ k hk.1 ∈ KU σ n := fIwasawa_mk_mem_K σ hσv k hk.1 hk.2
  refine ⟨(fIwasawaMk σ k hk.1 * g⁻¹)⁻¹, fIwasawaMk σ k hk.1, ?_, hkG, by group⟩
  have h1 : (((fIwasawaMk σ k hk.1 * g⁻¹ : GU σ n) : GL (Fin n) L) :
      Matrix (Fin n) (Fin n) L).BlockTriangular id := by
    rw [Subgroup.coe_mul, Units.val_mul, fIwasawa_mk_val]; exact hup
  have h2 := spherical_upper_inv _ h1
  rw [← Subgroup.coe_inv] at h2
  exact (spherical_upper_iff _).2 h2

/- English proof (translation)
Establish `hc_eq : b = b' * (k' * k⁻¹)`. Combine the equalities or inequalities in the displayed calculation. Establish `hkk : k' * k⁻¹ ∈ KU σ n` using `(KU σ n).mul_mem hk' ((KU σ n).inv_mem hk)`. Establish `hc_eq2 : k' * k⁻¹ = b'⁻¹ * b` using `by rw [hc_eq]; group`. Establish `htri : (((k' * k⁻¹ : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).BlockTriangular id`.

Rewrite using `[hc_eq2]`. Conclude with `Matrix.BlockTriangular.mul (GL_inv_blockTriangular (b' : GL (Fin n) L) hb') hb`. Rewrite using `[hc_eq, fIwasawa_chi_mul σ q α hα hq b' (k' * k⁻¹) hb' htri, fIwasawa_chi_int σ q α (k' * k⁻¹) htri hkk, mul_one]`.
-/
theorem fIwasawa_wd (hα : ∀ i, α i ≠ 0) (hq : (q : ℂ) ≠ 0) (b b' k k' : GU σ n)
    (hb : ((b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).BlockTriangular id)
    (hb' : ((b' : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).BlockTriangular id)
    (hk : k ∈ KU σ n) (hk' : k' ∈ KU σ n) (h : b * k = b' * k') :
    chiDeltaU q α b = chiDeltaU q α b' := by
  have hc_eq : b = b' * (k' * k⁻¹) := by
    calc b = b * k * k⁻¹ := by group
      _ = b' * k' * k⁻¹ := by rw [h]
      _ = b' * (k' * k⁻¹) := by group
  have hkk : k' * k⁻¹ ∈ KU σ n := (KU σ n).mul_mem hk' ((KU σ n).inv_mem hk)
  have hc_eq2 : k' * k⁻¹ = b'⁻¹ * b := by rw [hc_eq]; group
  have htri : (((k' * k⁻¹ : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).BlockTriangular id := by
    rw [hc_eq2]
    exact Matrix.BlockTriangular.mul (GL_inv_blockTriangular (b' : GL (Fin n) L) hb') hb
  rw [hc_eq, fIwasawa_chi_mul σ q α hα hq b' (k' * k⁻¹) hb' htri,
    fIwasawa_chi_int σ q α (k' * k⁻¹) htri hkk, mul_one]

end FIwasawaFinal

/- English proof (translation)
Introduce `L _ _ _ ϖ σ q n m hU hmn hnm α hα`. Take `⟨hσ, hσv, -, -, -, hq2, -⟩` from `hU`. Establish `hq : (q : ℂ) ≠ 0` using `by exact_mod_cast (show q ≠ 0 by omega)`. Use `choose B K hB hK hBK using fIwasawa_iwasawa (n := n) σ hσ hσv`. Establish `htri : ∀ g : GU σ n, IsBorelU g → (((g : GL (Fin n) L)) : Matrix (Fin n) (Fin n) L).BlockTriangular id`.

Introduce `g hg i j hij`. Conclude with `hg i j hij`. Establish `h1tri : (((1 : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).BlockTriangular id` using `Matrix.blockTriangular_one`. Use `⟨fun g => chiDeltaU q α (B g), ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `b g k hb hk`.

Establish `e : b * g * k = (b * B g) * (K g * k)` using `by conv_lhs => rw [hBK g]`. Simplify using `only [mul_assoc]`. Establish `hbB : (((b * B g : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).BlockTriangular id` using `Matrix.BlockTriangular.mul (htri b hb) (htri _ (hB g))`. Establish `hKk : K g * k ∈ KU σ n` using `(KU σ n).mul_mem (hK g) hk`. Use `show chiDeltaU q α (B (b * g * k)) = chiDeltaU q α b * chiDeltaU q α (B g)`.

Rewrite using `[fIwasawa_wd σ q α hα hq (B (b * g * k)) (b * B g) (K (b * g * k)) (K g * k) (htri _ (hB _)) hbB (hK _) hKk (by rw [← hBK, e])]`. Conclude with `fIwasawa_chi_mul σ q α hα hq b (B g) (htri b hb) (htri _ (hB g))`. Use `show chiDeltaU q α (B 1) = 1`. Rewrite using `[fIwasawa_wd σ q α hα hq (B 1) 1 (K 1) 1 (htri _ (hB 1)) h1tri (hK 1) (KU σ n).one_mem (by rw [← hBK, mul_one])]`. Conclude with `fIwasawa_chi_int σ q α 1 h1tri (KU σ n).one_mem`.

Introduce `ψ hψ`. Use function extensionality and compare the values at `g`. Establish `hg` using `hψ (B g) 1 (K g) (hB g) (hK g)`. Rewrite `hg` using `[mul_one, ← hBK]`. Rewrite using `[hg]`.

Conclude with `mul_comm _ _`.
-/
theorem exists_spherical_function_unitary : Formalism.UG.SphericalExistsU := by
  intro L _ _ _ ϖ σ q n m hU hmn hnm α hα
  obtain ⟨hσ, hσv, -, -, -, hq2, -⟩ := hU
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  choose B K hB hK hBK using fIwasawa_iwasawa (n := n) σ hσ hσv
  have htri : ∀ g : GU σ n, IsBorelU g →
      (((g : GL (Fin n) L)) : Matrix (Fin n) (Fin n) L).BlockTriangular id := by
    intro g hg i j hij
    exact hg i j hij
  have h1tri : (((1 : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).BlockTriangular id :=
    Matrix.blockTriangular_one
  refine ⟨fun g => chiDeltaU q α (B g), ?_, ?_, ?_⟩
  · intro b g k hb hk
    have e : b * g * k = (b * B g) * (K g * k) := by
      conv_lhs => rw [hBK g]
      simp only [mul_assoc]
    have hbB : (((b * B g : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).BlockTriangular id :=
      Matrix.BlockTriangular.mul (htri b hb) (htri _ (hB g))
    have hKk : K g * k ∈ KU σ n := (KU σ n).mul_mem (hK g) hk
    show chiDeltaU q α (B (b * g * k)) = chiDeltaU q α b * chiDeltaU q α (B g)
    rw [fIwasawa_wd σ q α hα hq (B (b * g * k)) (b * B g) (K (b * g * k)) (K g * k)
      (htri _ (hB _)) hbB (hK _) hKk (by rw [← hBK, e])]
    exact fIwasawa_chi_mul σ q α hα hq b (B g) (htri b hb) (htri _ (hB g))
  · show chiDeltaU q α (B 1) = 1
    rw [fIwasawa_wd σ q α hα hq (B 1) 1 (K 1) 1 (htri _ (hB 1)) h1tri (hK 1) (KU σ n).one_mem
      (by rw [← hBK, mul_one])]
    exact fIwasawa_chi_int σ q α 1 h1tri (KU σ n).one_mem
  · intro ψ hψ
    funext g
    have hg := hψ (B g) 1 (K g) (hB g) (hK g)
    rw [mul_one, ← hBK] at hg
    rw [hg]
    exact mul_comm _ _

end Formalism.UG.P
