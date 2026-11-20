import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.PartShortOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.HformSmulRight

noncomputable section

namespace PIW.AdelClassFin

open Formalism.UG NumberField
open scoped Matrix

section GD

variable {E : Type} [Field E] [NumberField E] [StarRing E] {m : ℕ} (J : Matrix (Fin m) (Fin m) E)

/- English proof (translation)
Use extensionality with `i`. Simplify using `[Rat.smul_def]`.
-/
theorem gd_qsmul (q : ℚ) (x : Fin m → E) : q • x = ((q : E)) • x := by
  ext i
  simp [Rat.smul_def]

/- English proof (translation)
Use `first`. Consider the case `exact star_ratCast q`. Consider the case `simpa [starRingEnd_apply] using map_ratCast (starRingEnd E) q`.
-/
theorem gd_star_rat (q : ℚ) : star ((q : E)) = (q : E) := by
  first
    | exact star_ratCast q
    | simpa [starRingEnd_apply] using map_ratCast (starRingEnd E) q

def gdLeft (y : Fin m → E) : (Fin m → E) →ₗ[ℚ] ℚ where
  toFun x := Algebra.trace ℚ E (hform (starRingEnd E) J x y)
  map_add' x x' := by rw [hform_add_left', map_add]
  map_smul' q x := by
    rw [gd_qsmul, hform_smul_left', gd_star_rat, RingHom.id_apply, smul_eq_mul, ← Rat.smul_def, map_smul,
      smul_eq_mul]

def gdRight (x : Fin m → E) : (Fin m → E) →ₗ[ℚ] ℚ where
  toFun y := Algebra.trace ℚ E (hform (starRingEnd E) J x y)
  map_add' y y' := by rw [hform_add_right', map_add]
  map_smul' q y := by
    rw [gd_qsmul, hform_smul_right', RingHom.id_apply, smul_eq_mul, ← Rat.smul_def, map_smul, smul_eq_mul]

/- English proof (translation)
Rewrite using `[gd_qsmul, Rat.cast_intCast]`.
-/
theorem gd_int_smul (c : ℤ) (x : Fin m → E) : ((c : E)) • x = ((c : ℚ)) • x := by
  rw [gd_qsmul, Rat.cast_intCast]

end GD

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ cm m d δ hd hδ hcod p hp e hli he hspan`. Simplify using `only [Lat, Set.mem_setOf_eq] at hp`. Take `⟨hJh, hJdet, -, -, hMint, hMdual⟩` from `hp`. Use `set J := p.1 with hJdef`. Use `set M := p.2 with hMdef`.

Establish `hO : ∀ b : E, b ∈ (algebraMap (𝓞 E) E).range → star b ∈ (algebraMap (𝓞 E) E).range`. Introduce `b hb`. Take `⟨β, rfl⟩` from `RingHom.mem_range.mp hb`. Establish `hint : IsIntegral ℤ (starRingEnd E (algebraMap (𝓞 E) E β))` using `IsIntegral.map (starRingEnd E).toIntAlgHom β.isIntegral_coe`. Conclude with `RingHom.mem_range.mpr ((IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).mp hint)`.

Establish `F1 : ∀ x y : Fin m → E, hform (starRingEnd E) J x y = (fun i => starRingEnd E (x i)) ⬝ᵥ (J *ᵥ y)`. Introduce `x y`. Simplify using `only [hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]`. Establish `hsingle : ∀ (i : Fin m) (v : Fin m → E), hform (starRingEnd E) J (Pi.single i 1) v = (J *ᵥ v) i`. Introduce `i v`.

Rewrite using `[F1]`. Establish `hs : (fun a => starRingEnd E ((Pi.single i (1 : E) : Fin m → E) a)) = Pi.single i 1`. Use function extensionality and compare the values at `a`. Distinguish the cases in `h : a = i`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, h]`. Rewrite using `[hs]`. Use `first`. Consider the case `rw [single_dotProduct, one_mul]`.

Consider the case `simp [dotProduct, Pi.single_apply]`. Establish `hnd : ∀ y : Fin m → E, (∀ x, hform (starRingEnd E) J x y = 0) → y = 0`. Introduce `y hy`. Establish `hJy : J *ᵥ y = 0`. Use function extensionality and compare the values at `i`.

Rewrite using `[← hsingle, Pi.zero_apply]`. Conclude with `hy _`. Establish `h6 : y = J⁻¹ *ᵥ (J *ᵥ y)`. Rewrite using `[Matrix.mulVec_mulVec y J⁻¹ J, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hJdet), Matrix.one_mulVec]`. Rewrite using `[h6, hJy, Matrix.mulVec_zero]`.

Establish `htr : ∀ z : E, (∀ b : E, Algebra.trace ℚ E (b * z) = 0) → z = 0`. Introduce `z hz`. Assume the negation of the conclusion as `hne`. Establish `h1` using `hz z⁻¹`. Rewrite `h1` using `[inv_mul_cancel₀ hne, ← map_one (algebraMap ℚ E), Algebra.trace_algebraMap, nsmul_eq_mul, mul_one, Nat.cast_eq_zero]`.

Conclude with `(Module.finrank_pos (R := ℚ) (M := E)).ne' h1`. Establish `hRt : ∀ x y, gdRight J x y = Algebra.trace ℚ E (hform (starRingEnd E) J x y)` using `fun x y => rfl`. Establish `hLt : ∀ x y, gdLeft J y x = Algebra.trace ℚ E (hform (starRingEnd E) J x y)` using `fun x y => rfl`. Establish `Br : ∀ (x : Fin m → E) (q : Fin (m * Module.finrank ℚ E) → ℚ), Algebra.trace ℚ E (hform (starRingEnd E) J x (∑ k, q k • e k)) = ∑ k, q k * Algebra.trace ℚ E (hform (starRingEnd E) J x (e k))`. Introduce `x q`.

Rewrite using `[← hRt, map_sum]`. Simplify using `only [map_smul, smul_eq_mul]`. Simplify using `only [hRt]`. Establish `Bl : ∀ (y : Fin m → E) (q : Fin (m * Module.finrank ℚ E) → ℚ), Algebra.trace ℚ E (hform (starRingEnd E) J (∑ k, q k • e k) y) = ∑ k, q k * Algebra.trace ℚ E (hform (starRingEnd E) J (e k) y)`. Introduce `y q`.

Rewrite using `[← hLt, map_sum]`. Simplify using `only [map_smul, smul_eq_mul]`. Simplify using `only [hLt]`. Establish `hGe : ∀ i j, gramTr J e i j = Algebra.trace ℚ E (hform (starRingEnd E) J (e i) (e j))` using `fun i j => rfl`. Establish `hdetG : (gramTr J e).det ≠ 0`.

Break down `isEmpty_or_nonempty (Fin (m * Module.finrank ℚ E)) with hE | hE` into its components or cases. Rewrite using `[Matrix.det_isEmpty]`. Conclude with `one_ne_zero`. Establish `hcard : Fintype.card (Fin (m * Module.finrank ℚ E)) = Module.finrank ℚ (Fin m → E)`. Rewrite using `[Fintype.card_fin]`.

Use `first`. Consider the case `simp [Module.finrank_pi_fintype]`. Consider the case `rw [Module.finrank_pi_fintype]`. Simplify using the standard rewrite rules. Set `bs` to `basisOfLinearIndependentOfCardEqFinrank hli hcard`.

Establish `hbs : ∀ i, bs i = e i` using `fun i => by simp [bs]`. Rewrite using `[Ne, ← Matrix.exists_mulVec_eq_zero_iff]`. Introduce and unpack `⟨v, hv0, hv⟩`. Establish `hy : ∑ j, v j • e j = 0`. Apply `hnd` to reduce the goal to its premises.

Introduce `x`. Apply `htr` to reduce the goal to its premises. Introduce `b`. Establish `e1 : b * hform (starRingEnd E) J x (∑ j, v j • e j) = hform (starRingEnd E) J (star b • x) (∑ j, v j • e j)`. Rewrite using `[hform_smul_left', star_star]`.

Rewrite using `[e1]`. Establish `hf : gdLeft J (∑ j, v j • e j) = 0`. Use `bs.ext fun i => ?_` and prove the remaining obligations. Rewrite using `[hbs, LinearMap.zero_apply, hLt, Br]`. Establish `h2` using `congrFun hv i`.

Rewrite `h2` using `[Pi.zero_apply]`. Use `Eq.trans ?_ h2` and prove the remaining obligations. Simplify using `only [Matrix.mulVec, dotProduct]`. Conclude with `Finset.sum_congr rfl fun k _ => by rw [hGe, mul_comm]`. Establish `h3` using `LinearMap.congr_fun hf (star b • x)`.

Rewrite `h3` using `[LinearMap.zero_apply, hLt]`. Conclude with `h3`. Apply `hv0` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Conclude with `(Fintype.linearIndependent_iff.mp hli) v hy i`.

Use `⟨hdetG, ?_⟩` and prove the remaining obligations. Use `set Gi := (gramTr J e)⁻¹ with hGi`. Establish `hGGi : gramTr J e * Gi = 1` using `Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdetG)`. Take `⟨w, hw⟩ : ∃ w : Fin (m * Module.finrank ℚ E) → Fin m → E, ∀ j, w j = ∑ k, Gi k j • e k` from `⟨_, fun j => rfl⟩`. Establish `hBw : ∀ i j, Algebra.trace ℚ E (hform (starRingEnd E) J (e i) (w j)) = (1 : Matrix (Fin (m * Module.finrank ℚ E)) (Fin (m * Module.finrank ℚ E)) ℚ) i j`.

Introduce `i j`. Rewrite using `[hw, Br, ← hGGi, Matrix.mul_apply]`. Conclude with `Finset.sum_congr rfl fun k _ => by rw [hGe, mul_comm]`. Establish `hint : ∀ x ∈ M, ∀ j, Algebra.trace ℚ E (hform (starRingEnd E) J x (w j)) ∈ (algebraMap ℤ ℚ).range`. Introduce `x hx j`.

Take `⟨c, rfl⟩` from `hspan x hx`. Establish `e2 : ∑ i, ((c i : ℤ) : E) • e i = ∑ i, ((c i : ℚ)) • e i` using `Finset.sum_congr rfl fun i _ => gd_int_smul _ _`. Rewrite using `[e2, Bl]`. Simplify using `only [hBw, Matrix.one_apply]`. Use `RingHom.mem_range.mpr ⟨c j, ?_⟩` and prove the remaining obligations.

Simplify using the standard rewrite rules. Establish `hdual : ∀ j, (d : E) • ((δ : E) • w j) ∈ M`. Introduce `j`. Apply `hMdual` to reduce the goal to its premises. Introduce `x hx`.

Rewrite using `[hform_smul_right']`. Apply `hcod` to reduce the goal to its premises. Introduce `a`. Establish `hsa : star (algebraMap (𝓞 E) E a) • x ∈ M`. Take `⟨a', ha'⟩` from `RingHom.mem_range.mp (hO _ (RingHom.mem_range.mpr ⟨a, rfl⟩))`.

Rewrite using `[← ha', algebraMap_smul]`. Conclude with `M.smul_mem a' hx`. Establish `e3 : algebraMap (𝓞 E) E a * hform (starRingEnd E) J x (w j) = hform (starRingEnd E) J (star (algebraMap (𝓞 E) E a) • x) (w j)`. Rewrite using `[hform_smul_left', star_star]`. Rewrite using `[e3]`.

Conclude with `hint _ hsa j`. Establish `hn : ∀ (n : ℕ) (v : Fin m → E), (n : E) • v = (n : ℚ) • v` using `fun n v => by`. Rewrite using `[gd_qsmul, Rat.cast_natCast]`. Establish `hC : ∀ j, ∃ C : Fin (m * Module.finrank ℚ E) → ℤ, ∀ k, (C k : ℚ) = (d : ℚ) * (δ : ℚ) * Gi k j`. Introduce `j`.

Take `⟨C, hCe⟩` from `hspan _ (hdual j)`. Use `⟨C, ?_⟩` and prove the remaining obligations. Establish `e4 : (d : E) • ((δ : E) • w j) = ∑ k, ((d : ℚ) * (δ : ℚ) * Gi k j) • e k`. Rewrite using `[hn, hn, hw, Finset.smul_sum, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[smul_smul, smul_smul, mul_assoc]`. Establish `e5 : ∑ k, ((C k : ℚ) - (d : ℚ) * (δ : ℚ) * Gi k j) • e k = 0`. Simplify using `only [sub_smul, Finset.sum_sub_distrib]`. Rewrite using `[sub_eq_zero, ← e4, hCe]`. Conclude with `Finset.sum_congr rfl fun k _ => (gd_int_smul _ _).symm`.

Introduce `k`. Conclude with `sub_eq_zero.mp ((Fintype.linearIndependent_iff.mp hli) _ e5 k)`. Use `choose C hCj using hC`. Use `set C' : Matrix (Fin (m * Module.finrank ℚ E)) (Fin (m * Module.finrank ℚ E)) ℤ := Matrix.of fun k j => C j k with hC'`. Establish `hdq : (0 : ℚ) < (d : ℚ) * (δ : ℚ)`.

Establish `h1 : (0 : ℚ) < d` using `Nat.cast_pos.mpr hd`. Establish `h2 : (0 : ℚ) < δ` using `Nat.cast_pos.mpr hδ`. Check the signs of the components of the expression. Establish `hCm : C'.map (Int.cast : ℤ → ℚ) = ((d : ℚ) * (δ : ℚ)) • Gi`. Use extensionality with `k j`.

Simplify using `[hC', hCj]`. Establish `hdetC : ((C'.det : ℤ) : ℚ) = ((d : ℚ) * (δ : ℚ)) ^ (m * Module.finrank ℚ E) * ((gramTr J e).det)⁻¹`. Establish `h1 : ((C'.det : ℤ) : ℚ) = (C'.map (Int.cast : ℤ → ℚ)).det` using `(Int.castRingHom ℚ).map_det C'`. Rewrite using `[h1, hCm, Matrix.det_smul, Fintype.card_fin, hGi, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']`. Establish `hCne : C'.det ≠ 0`.

Introduce `h0`. Rewrite `hdetC` using `[h0, Int.cast_zero]`. Conclude with `mul_ne_zero (pow_ne_zero _ hdq.ne') (inv_ne_zero hdetG) hdetC.symm`. Establish `h1 : (1 : ℚ) ≤ |((C'.det : ℤ) : ℚ)|` using `by exact_mod_cast Int.one_le_abs hCne`. Establish `hpos : 0 < |(gramTr J e).det|` using `abs_pos.mpr hdetG`.

Use `set X := ((d : ℚ) * (δ : ℚ)) ^ (m * Module.finrank ℚ E) with hX`. Establish `hXpos : 0 < X` using `pow_pos hdq _`. Rewrite `h1` using `[hdetC, abs_mul, abs_inv, abs_of_pos hXpos]`. Establish `key : |(gramTr J e).det| ≤ X`. Establish `h2` using `mul_le_mul_of_nonneg_left h1 hpos.le`.

Rewrite `h2` using `[mul_one, mul_comm X, ← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]`. Then use the resulting hypothesis. Rewrite `key` using `[hX]`. Use `push_cast`. Conclude with `key`.
-/
theorem successive_vector_gram_det : SvGramDet := by
  classical
  intro F E _ _ _ _ _ _ cm m d δ hd hδ hcod p hp e hli he hspan
  simp only [Lat, Set.mem_setOf_eq] at hp
  obtain ⟨hJh, hJdet, -, -, hMint, hMdual⟩ := hp
  set J := p.1 with hJdef
  set M := p.2 with hMdef
  have hO : ∀ b : E, b ∈ (algebraMap (𝓞 E) E).range → star b ∈ (algebraMap (𝓞 E) E).range := by
    intro b hb
    obtain ⟨β, rfl⟩ := RingHom.mem_range.mp hb
    have hint : IsIntegral ℤ (starRingEnd E (algebraMap (𝓞 E) E β)) :=
      IsIntegral.map (starRingEnd E).toIntAlgHom β.isIntegral_coe
    exact RingHom.mem_range.mpr ((IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).mp hint)
  have F1 : ∀ x y : Fin m → E,
      hform (starRingEnd E) J x y = (fun i => starRingEnd E (x i)) ⬝ᵥ (J *ᵥ y) := by
    intro x y
    simp only [hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have hsingle : ∀ (i : Fin m) (v : Fin m → E), hform (starRingEnd E) J (Pi.single i 1) v = (J *ᵥ v) i := by
    intro i v
    rw [F1]
    have hs : (fun a => starRingEnd E ((Pi.single i (1 : E) : Fin m → E) a)) = Pi.single i 1 := by
      funext a
      by_cases h : a = i
      · subst h
        simp
      · simp [Pi.single_apply, h]
    rw [hs]
    first
      | rw [single_dotProduct, one_mul]
      | simp [dotProduct, Pi.single_apply]
  have hnd : ∀ y : Fin m → E, (∀ x, hform (starRingEnd E) J x y = 0) → y = 0 := by
    intro y hy
    have hJy : J *ᵥ y = 0 := by
      funext i
      rw [← hsingle, Pi.zero_apply]
      exact hy _
    have h6 : y = J⁻¹ *ᵥ (J *ᵥ y) := by
      rw [Matrix.mulVec_mulVec y J⁻¹ J, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hJdet),
        Matrix.one_mulVec]
    rw [h6, hJy, Matrix.mulVec_zero]
  have htr : ∀ z : E, (∀ b : E, Algebra.trace ℚ E (b * z) = 0) → z = 0 := by
    intro z hz
    by_contra hne
    have h1 := hz z⁻¹
    rw [inv_mul_cancel₀ hne, ← map_one (algebraMap ℚ E), Algebra.trace_algebraMap, nsmul_eq_mul,
      mul_one, Nat.cast_eq_zero] at h1
    exact (Module.finrank_pos (R := ℚ) (M := E)).ne' h1
  have hRt : ∀ x y, gdRight J x y = Algebra.trace ℚ E (hform (starRingEnd E) J x y) := fun x y => rfl
  have hLt : ∀ x y, gdLeft J y x = Algebra.trace ℚ E (hform (starRingEnd E) J x y) := fun x y => rfl
  have Br : ∀ (x : Fin m → E) (q : Fin (m * Module.finrank ℚ E) → ℚ),
      Algebra.trace ℚ E (hform (starRingEnd E) J x (∑ k, q k • e k)) =
        ∑ k, q k * Algebra.trace ℚ E (hform (starRingEnd E) J x (e k)) := by
    intro x q
    rw [← hRt, map_sum]
    simp only [map_smul, smul_eq_mul]
    simp only [hRt]
  have Bl : ∀ (y : Fin m → E) (q : Fin (m * Module.finrank ℚ E) → ℚ),
      Algebra.trace ℚ E (hform (starRingEnd E) J (∑ k, q k • e k) y) =
        ∑ k, q k * Algebra.trace ℚ E (hform (starRingEnd E) J (e k) y) := by
    intro y q
    rw [← hLt, map_sum]
    simp only [map_smul, smul_eq_mul]
    simp only [hLt]
  have hGe : ∀ i j, gramTr J e i j = Algebra.trace ℚ E (hform (starRingEnd E) J (e i) (e j)) :=
    fun i j => rfl
  have hdetG : (gramTr J e).det ≠ 0 := by
    rcases isEmpty_or_nonempty (Fin (m * Module.finrank ℚ E)) with hE | hE
    · rw [Matrix.det_isEmpty]
      exact one_ne_zero
    have hcard : Fintype.card (Fin (m * Module.finrank ℚ E)) = Module.finrank ℚ (Fin m → E) := by
      rw [Fintype.card_fin]
      first
        | simp [Module.finrank_pi_fintype]
        | rw [Module.finrank_pi_fintype]; simp
    let bs := basisOfLinearIndependentOfCardEqFinrank hli hcard
    have hbs : ∀ i, bs i = e i := fun i => by simp [bs]
    rw [Ne, ← Matrix.exists_mulVec_eq_zero_iff]
    rintro ⟨v, hv0, hv⟩
    have hy : ∑ j, v j • e j = 0 := by
      apply hnd
      intro x
      apply htr
      intro b
      have e1 : b * hform (starRingEnd E) J x (∑ j, v j • e j) =
          hform (starRingEnd E) J (star b • x) (∑ j, v j • e j) := by
        rw [hform_smul_left', star_star]
      rw [e1]
      have hf : gdLeft J (∑ j, v j • e j) = 0 := by
        refine bs.ext fun i => ?_
        rw [hbs, LinearMap.zero_apply, hLt, Br]
        have h2 := congrFun hv i
        rw [Pi.zero_apply] at h2
        refine Eq.trans ?_ h2
        simp only [Matrix.mulVec, dotProduct]
        exact Finset.sum_congr rfl fun k _ => by rw [hGe, mul_comm]
      have h3 := LinearMap.congr_fun hf (star b • x)
      rw [LinearMap.zero_apply, hLt] at h3
      exact h3
    apply hv0
    funext i
    exact (Fintype.linearIndependent_iff.mp hli) v hy i
  refine ⟨hdetG, ?_⟩
  set Gi := (gramTr J e)⁻¹ with hGi
  have hGGi : gramTr J e * Gi = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdetG)
  obtain ⟨w, hw⟩ : ∃ w : Fin (m * Module.finrank ℚ E) → Fin m → E,
      ∀ j, w j = ∑ k, Gi k j • e k := ⟨_, fun j => rfl⟩
  have hBw : ∀ i j, Algebra.trace ℚ E (hform (starRingEnd E) J (e i) (w j)) =
      (1 : Matrix (Fin (m * Module.finrank ℚ E)) (Fin (m * Module.finrank ℚ E)) ℚ) i j := by
    intro i j
    rw [hw, Br, ← hGGi, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun k _ => by rw [hGe, mul_comm]
  have hint : ∀ x ∈ M, ∀ j, Algebra.trace ℚ E (hform (starRingEnd E) J x (w j)) ∈
      (algebraMap ℤ ℚ).range := by
    intro x hx j
    obtain ⟨c, rfl⟩ := hspan x hx
    have e2 : ∑ i, ((c i : ℤ) : E) • e i = ∑ i, ((c i : ℚ)) • e i :=
      Finset.sum_congr rfl fun i _ => gd_int_smul _ _
    rw [e2, Bl]
    simp only [hBw, Matrix.one_apply]
    refine RingHom.mem_range.mpr ⟨c j, ?_⟩
    simp
  have hdual : ∀ j, (d : E) • ((δ : E) • w j) ∈ M := by
    intro j
    apply hMdual
    intro x hx
    rw [hform_smul_right']
    apply hcod
    intro a
    have hsa : star (algebraMap (𝓞 E) E a) • x ∈ M := by
      obtain ⟨a', ha'⟩ := RingHom.mem_range.mp (hO _ (RingHom.mem_range.mpr ⟨a, rfl⟩))
      rw [← ha', algebraMap_smul]
      exact M.smul_mem a' hx
    have e3 : algebraMap (𝓞 E) E a * hform (starRingEnd E) J x (w j) =
        hform (starRingEnd E) J (star (algebraMap (𝓞 E) E a) • x) (w j) := by
      rw [hform_smul_left', star_star]
    rw [e3]
    exact hint _ hsa j
  have hn : ∀ (n : ℕ) (v : Fin m → E), (n : E) • v = (n : ℚ) • v := fun n v => by
    rw [gd_qsmul, Rat.cast_natCast]
  have hC : ∀ j, ∃ C : Fin (m * Module.finrank ℚ E) → ℤ,
      ∀ k, (C k : ℚ) = (d : ℚ) * (δ : ℚ) * Gi k j := by
    intro j
    obtain ⟨C, hCe⟩ := hspan _ (hdual j)
    refine ⟨C, ?_⟩
    have e4 : (d : E) • ((δ : E) • w j) = ∑ k, ((d : ℚ) * (δ : ℚ) * Gi k j) • e k := by
      rw [hn, hn, hw, Finset.smul_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_smul, smul_smul, mul_assoc]
    have e5 : ∑ k, ((C k : ℚ) - (d : ℚ) * (δ : ℚ) * Gi k j) • e k = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [sub_eq_zero, ← e4, hCe]
      exact Finset.sum_congr rfl fun k _ => (gd_int_smul _ _).symm
    intro k
    exact sub_eq_zero.mp ((Fintype.linearIndependent_iff.mp hli) _ e5 k)
  choose C hCj using hC
  set C' : Matrix (Fin (m * Module.finrank ℚ E)) (Fin (m * Module.finrank ℚ E)) ℤ :=
    Matrix.of fun k j => C j k with hC'
  have hdq : (0 : ℚ) < (d : ℚ) * (δ : ℚ) := by
    have h1 : (0 : ℚ) < d := Nat.cast_pos.mpr hd
    have h2 : (0 : ℚ) < δ := Nat.cast_pos.mpr hδ
    positivity
  have hCm : C'.map (Int.cast : ℤ → ℚ) = ((d : ℚ) * (δ : ℚ)) • Gi := by
    ext k j
    simp [hC', hCj]
  have hdetC : ((C'.det : ℤ) : ℚ) =
      ((d : ℚ) * (δ : ℚ)) ^ (m * Module.finrank ℚ E) * ((gramTr J e).det)⁻¹ := by
    have h1 : ((C'.det : ℤ) : ℚ) = (C'.map (Int.cast : ℤ → ℚ)).det := (Int.castRingHom ℚ).map_det C'
    rw [h1, hCm, Matrix.det_smul, Fintype.card_fin, hGi, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  have hCne : C'.det ≠ 0 := by
    intro h0
    rw [h0, Int.cast_zero] at hdetC
    exact mul_ne_zero (pow_ne_zero _ hdq.ne') (inv_ne_zero hdetG) hdetC.symm
  have h1 : (1 : ℚ) ≤ |((C'.det : ℤ) : ℚ)| := by exact_mod_cast Int.one_le_abs hCne
  have hpos : 0 < |(gramTr J e).det| := abs_pos.mpr hdetG
  set X := ((d : ℚ) * (δ : ℚ)) ^ (m * Module.finrank ℚ E) with hX
  have hXpos : 0 < X := pow_pos hdq _
  rw [hdetC, abs_mul, abs_inv, abs_of_pos hXpos] at h1
  have key : |(gramTr J e).det| ≤ X := by
    have h2 := mul_le_mul_of_nonneg_left h1 hpos.le
    rwa [mul_one, mul_comm X, ← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul] at h2
  rw [hX] at key
  push_cast
  exact key

end PIW.AdelClassFin

end
