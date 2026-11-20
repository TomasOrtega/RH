import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.IntegralJetEntries

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions

noncomputable section

namespace GlobalTheory.JetTieCompare

open GlobalTheory.IndefiniteRowSideFullHecke.IntegralJetEntries (IsRBasis)

variable {p : ℕ} [Fact p.Prime]

/- English proof (translation)
Rewrite using `[PadicComplexInt, Valuation.mem_valuationSubring_iff, PadicComplex.norm_eq_norm, Valuation.norm_def, PadicComplex.RankOne.hom_eq_embedding, Valuation.embedding_restrict]`. Conclude with `Iff.rfl` after adjusting the coercions.
-/
theorem mem_int_iff (x : ℂ_[p]) : x ∈ 𝓞_ℂ_[p] ↔ ‖x‖ ≤ 1 := by
  rw [PadicComplexInt, Valuation.mem_valuationSubring_iff, PadicComplex.norm_eq_norm, Valuation.norm_def,
    PadicComplex.RankOne.hom_eq_embedding, Valuation.embedding_restrict]
  exact_mod_cast Iff.rfl

/- English proof (translation)
Establish `h : IsIntegral 𝓞_ℂ_[p] (ρ (x : E))` using `IsIntegral.map_of_comp_eq (Int.castRingHom _) ρ (RingHom.ext_int _ _) x.isIntegral_coe`. Conclude with `(mem_int_iff _).1 ((PadicComplexInt.integers p).mem_of_integral h)`.
-/
theorem norm_int_le {E : Type} [Field E] (ρ : E →+* ℂ_[p]) (x : 𝓞 E) : ‖ρ (x : E)‖ ≤ 1 := by
  have h : IsIntegral 𝓞_ℂ_[p] (ρ (x : E)) :=
    IsIntegral.map_of_comp_eq (Int.castRingHom _) ρ (RingHom.ext_int _ _) x.isIntegral_coe
  exact (mem_int_iff _).1 ((PadicComplexInt.integers p).mem_of_integral h)

/- English proof (translation)
Set `I : Ideal (𝓞 E)` to `{ carrier := {y | ‖ρ (y : E)‖ < 1} zero_mem' := by simp add_mem' := fun {a b} ha hb => by`. Simplify using `only [Set.mem_setOf_eq, map_add] at ha hb ⊢`. Conclude with `lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)`. Use the proof step `smul_mem' := fun c {a} ha => by`. Simplify using `only [Set.mem_setOf_eq, smul_eq_mul, map_mul, norm_mul] at ha ⊢`.

Conclude with `mul_lt_one_of_nonneg_of_lt_one_right (norm_int_le ρ c) (norm_nonneg _) ha }`. Establish `hI : ∀ y : 𝓞 E, y ∉ I ↔ ‖ρ (y : E)‖ = 1` using `fun y => ⟨fun h => le_antisymm (norm_int_le ρ y) (not_lt.1 h), fun h h' => absurd h (ne_of_lt h')⟩`. Establish `hp : I.IsPrime`. Use `⟨(Ideal.ne_top_iff_one _).2 ((hI 1).2 (by simp)), fun {a b} hab => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hc`.

Rewrite `hc` using `[not_or, hI, hI]`. Conclude with `(hI (a * b)).2 (by simp [hc.1, hc.2]) hab`. Establish `hpI : ((p : ℕ) : 𝓞 E) ∈ I`. Express the relevant statement in the definitionally equal form `‖ρ (((p : ℕ) : 𝓞 E) : E)‖ < 1`. Establish `: ρ (((p : ℕ) : 𝓞 E) : E) = algebraMap ℚ_[p] ℂ_[p] (p : ℚ_[p])` using `by simp`.

Rewrite using `[this, norm_algebraMap']`. Conclude with `Padic.norm_p_lt_one`. Establish `hne : I ≠ ⊥` using `fun h => by`. Rewrite `hpI` using `[h, Ideal.mem_bot]`. Conclude with `(Fact.out : p.Prime).ne_zero (by exact_mod_cast hpI)`.

Take `⟨n, d, h | h⟩` from `(⟨I, hp, hne⟩ : HeightOneSpectrum (𝓞 E)).exists_primeCompl_mul_eq_or_mul_eq (K := E) x`. Conclude with `⟨d, n, (hI _).1 d.2, by rw [mul_comm]; exact h⟩`. Use `⟨n, d, le_antisymm (norm_int_le ρ n) ?_, by rw [mul_comm]; exact h⟩` and prove the remaining obligations. Establish `h1 : ‖ρ x‖ * ‖ρ (n : E)‖ = 1`. Rewrite using `[← norm_mul, ← map_mul, ← (hI _).1 d.2]`.

Conclude with `congrArg (fun y => ‖ρ y‖) h`. Use polynomial arithmetic with `[norm_nonneg (ρ (n : E)), norm_nonneg (ρ x)]`.
-/
theorem exists_denom {E : Type} [Field E] [NumberField E] (ρ : E →+* ℂ_[p]) (x : E) (hx : ‖ρ x‖ ≤ 1) :
    ∃ s n : 𝓞 E, ‖ρ (s : E)‖ = 1 ∧ (s : E) * x = n := by
  let I : Ideal (𝓞 E) :=
    { carrier := {y | ‖ρ (y : E)‖ < 1}
      zero_mem' := by simp
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_add] at ha hb ⊢
        exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
      smul_mem' := fun c {a} ha => by
        simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul, norm_mul] at ha ⊢
        exact mul_lt_one_of_nonneg_of_lt_one_right (norm_int_le ρ c) (norm_nonneg _) ha }
  have hI : ∀ y : 𝓞 E, y ∉ I ↔ ‖ρ (y : E)‖ = 1 := fun y =>
    ⟨fun h => le_antisymm (norm_int_le ρ y) (not_lt.1 h), fun h h' => absurd h (ne_of_lt h')⟩
  have hp : I.IsPrime := by
    refine ⟨(Ideal.ne_top_iff_one _).2 ((hI 1).2 (by simp)), fun {a b} hab => ?_⟩
    by_contra hc
    rw [not_or, hI, hI] at hc
    exact (hI (a * b)).2 (by simp [hc.1, hc.2]) hab
  have hpI : ((p : ℕ) : 𝓞 E) ∈ I := by
    change ‖ρ (((p : ℕ) : 𝓞 E) : E)‖ < 1
    have : ρ (((p : ℕ) : 𝓞 E) : E) = algebraMap ℚ_[p] ℂ_[p] (p : ℚ_[p]) := by simp
    rw [this, norm_algebraMap']
    exact Padic.norm_p_lt_one
  have hne : I ≠ ⊥ := fun h => by
    rw [h, Ideal.mem_bot] at hpI
    exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast hpI)
  obtain ⟨n, d, h | h⟩ := (⟨I, hp, hne⟩ : HeightOneSpectrum (𝓞 E)).exists_primeCompl_mul_eq_or_mul_eq (K := E) x
  · exact ⟨d, n, (hI _).1 d.2, by rw [mul_comm]; exact h⟩
  · refine ⟨n, d, le_antisymm (norm_int_le ρ n) ?_, by rw [mul_comm]; exact h⟩
    have h1 : ‖ρ x‖ * ‖ρ (n : E)‖ = 1 := by
      rw [← norm_mul, ← map_mul, ← (hI _).1 d.2]
      exact congrArg (fun y => ‖ρ y‖) h
    nlinarith [norm_nonneg (ρ (n : E)), norm_nonneg (ρ x)]

/- English proof (translation)
Use `choose s n hs hn using fun a => exists_denom ρ (x a) (hx a)`. Use `⟨∏ a, s a, fun a => (∏ b ∈ Finset.univ.erase a, s b) * n a, ?_, fun a => ?_⟩` and prove the remaining obligations. Establish `: ((∏ a, s a : 𝓞 E) : E) = ∏ a, (s a : E)` using `map_prod (algebraMap (𝓞 E) E) _ _`. Rewrite using `[this, map_prod, norm_prod]`. Conclude with `Finset.prod_eq_one fun a _ => hs a`.

Rewrite using `[← Finset.prod_erase_mul _ _ (Finset.mem_univ a)]`. Express the relevant statement in the definitionally equal form `algebraMap (𝓞 E) E (_ * _) * _ = algebraMap (𝓞 E) E (_ * _)`. Rewrite using `[map_mul, map_mul, mul_assoc]`. Conclude with `congrArg _ (hn a)`.
-/
theorem exists_common_denom {E : Type} [Field E] [NumberField E] (ρ : E →+* ℂ_[p]) {N : ℕ} (x : Fin N → E)
    (hx : ∀ a, ‖ρ (x a)‖ ≤ 1) : ∃ (s : 𝓞 E) (n : Fin N → 𝓞 E), ‖ρ (s : E)‖ = 1 ∧ ∀ a, (s : E) * x a = n a := by
  classical
  choose s n hs hn using fun a => exists_denom ρ (x a) (hx a)
  refine ⟨∏ a, s a, fun a => (∏ b ∈ Finset.univ.erase a, s b) * n a, ?_, fun a => ?_⟩
  · have : ((∏ a, s a : 𝓞 E) : E) = ∏ a, (s a : E) := map_prod (algebraMap (𝓞 E) E) _ _
    rw [this, map_prod, norm_prod]
    exact Finset.prod_eq_one fun a _ => hs a
  · rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ a)]
    change algebraMap (𝓞 E) E (_ * _) * _ = algebraMap (𝓞 E) E (_ * _)
    rw [map_mul, map_mul, mul_assoc]
    exact congrArg _ (hn a)

/- English proof (translation)
Take `⟨s, rfl⟩` from `hfg`. Rewrite `hsp` using `[Submodule.span_span_of_tower]`. Set `M : (Fin N → s) → Matrix (Fin N) (Fin N) D.host.E` to `fun f => Matrix.of fun k a => (f a).1 k`. Choose the witnesses or unpack the hypotheses as in `⟨f₀, hf₀⟩ : ∃ f, (M f).det ≠ 0 := by`. Take `⟨b, hbs, hb, hli⟩` from `exists_linearIndependent D.host.E (s : Set (Fin N → D.host.E))`.

Set `B : Module.Basis b D.host.E (Fin N → D.host.E)` to `Module.Basis.mk hli (by simp [hb, hsp])`. Set `e` to `B.indexEquiv (Pi.basisFun D.host.E (Fin N))`. Use `⟨fun a => ⟨(e.symm a).1, hbs (e.symm a).2⟩, ?_⟩` and prove the remaining obligations. Establish `h` using `(Matrix.linearIndependent_cols_iff_isUnit (A := M fun a => ⟨(e.symm a).1, hbs (e.symm a).2⟩)).1 (hli.comp _ e.symm.injective)`. Conclude with `((Matrix.isUnit_iff_isUnit_det _).1 h).ne_zero`.

Use `haveI : Nonempty (Fin N → s) := ⟨f₀⟩`. Take `⟨f, hf⟩` from `Finite.exists_max fun f => ‖ρ (M f).det‖`. Establish `hpos : 0 < ‖ρ (M f).det‖` using `lt_of_lt_of_le (norm_pos_iff.2 ((map_ne_zero ρ).2 hf₀)) (hf f₀)`. Establish `hdet : (M f).det ≠ 0` using `(map_ne_zero ρ).1 (norm_pos_iff.1 hpos)`. Use `⟨M f, hdet, fun a => ⟨1, by simp, ?_⟩, fun x hx => ?_⟩` and prove the remaining obligations.

Rewrite using `[one_smul]`. Conclude with `Submodule.subset_span (f a).2`. Establish `key : ∃ c : Fin N → D.host.E, (∀ a, ‖ρ (c a)‖ ≤ 1) ∧ x = (M f).mulVec c`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`.

Use `⟨((M f).det)⁻¹ • (M f).cramer y, fun a => ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : (M f).updateCol a y = M (Function.update f a ⟨y, hy⟩)`. Use extensionality with `k b`. Distinguish the cases in `hb : b = a`. Substitute `hb` using the available equality.

Simplify using `[M]`. Simplify using `[M, Matrix.updateCol_ne hb, Function.update_of_ne hb]`. Rewrite using `[Pi.smul_apply, smul_eq_mul, Matrix.cramer_apply, h1, map_mul, map_inv₀, norm_mul, norm_inv, inv_mul_le_iff₀ hpos, mul_one]`. Conclude with `hf _`. Rewrite using `[Matrix.mulVec_smul, Matrix.mulVec_cramer, smul_smul, inv_mul_cancel₀ hdet, one_smul]`.

Consider the case `zero => exact ⟨0, by simp, by simp⟩`. Consider the case `add y z _ _ hy hz`. Take `⟨c, hc, rfl⟩` from `hy`. Take `⟨c', hc', rfl⟩` from `hz`. Use `⟨c + c', fun a => ?_, by rw [Matrix.mulVec_add]⟩` and prove the remaining obligations.

Rewrite using `[Pi.add_apply, map_add]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hc a) (hc' a))`. Consider the case `smul r y _ hy`. Take `⟨c, hc, rfl⟩` from `hy`. Use `⟨(r : D.host.E) • c, fun a => ?_, by rw [Matrix.mulVec_smul]; rfl⟩` and prove the remaining obligations.

Rewrite using `[Pi.smul_apply, smul_eq_mul, map_mul, norm_mul]`. Conclude with `mul_le_one₀ (norm_int_le ρ r) (norm_nonneg _) (hc a)`. Take `⟨c, hc, rfl⟩` from `key`. Take `⟨t, n, ht, hn⟩` from `exists_common_denom ρ c hc`. Use `⟨t, ht, n, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `k`. Rewrite using `[Finset.sum_apply]`. Express the relevant statement in the definitionally equal form `(t : D.host.E) * (∑ a, M f k a * c a) = ∑ a, (n a : D.host.E) * M f k a`. Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun a _ => by rw [← hn a]; ring`.
-/
theorem exists_locBasis (D : D7) (ρ : D.host.E →+* ℂ_[p]) {N : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (hfg : L.FG) (hsp : Submodule.span D.host.E (L : Set (Fin N → D.host.E)) = ⊤) :
    ∃ P, TaylorLogMetric.LocBasisW D ρ L P := by
  classical
  obtain ⟨s, rfl⟩ := hfg
  rw [Submodule.span_span_of_tower] at hsp
  let M : (Fin N → s) → Matrix (Fin N) (Fin N) D.host.E := fun f => Matrix.of fun k a => (f a).1 k
  obtain ⟨f₀, hf₀⟩ : ∃ f, (M f).det ≠ 0 := by
    obtain ⟨b, hbs, hb, hli⟩ := exists_linearIndependent D.host.E (s : Set (Fin N → D.host.E))
    let B : Module.Basis b D.host.E (Fin N → D.host.E) := Module.Basis.mk hli (by simp [hb, hsp])
    let e := B.indexEquiv (Pi.basisFun D.host.E (Fin N))
    refine ⟨fun a => ⟨(e.symm a).1, hbs (e.symm a).2⟩, ?_⟩
    have h := (Matrix.linearIndependent_cols_iff_isUnit (A := M fun a => ⟨(e.symm a).1, hbs (e.symm a).2⟩)).1
      (hli.comp _ e.symm.injective)
    exact ((Matrix.isUnit_iff_isUnit_det _).1 h).ne_zero
  haveI : Nonempty (Fin N → s) := ⟨f₀⟩
  obtain ⟨f, hf⟩ := Finite.exists_max fun f => ‖ρ (M f).det‖
  have hpos : 0 < ‖ρ (M f).det‖ := lt_of_lt_of_le (norm_pos_iff.2 ((map_ne_zero ρ).2 hf₀)) (hf f₀)
  have hdet : (M f).det ≠ 0 := (map_ne_zero ρ).1 (norm_pos_iff.1 hpos)
  refine ⟨M f, hdet, fun a => ⟨1, by simp, ?_⟩, fun x hx => ?_⟩
  · rw [one_smul]
    exact Submodule.subset_span (f a).2
  · have key : ∃ c : Fin N → D.host.E, (∀ a, ‖ρ (c a)‖ ≤ 1) ∧ x = (M f).mulVec c := by
      induction hx using Submodule.span_induction with
      | mem y hy =>
        refine ⟨((M f).det)⁻¹ • (M f).cramer y, fun a => ?_, ?_⟩
        · have h1 : (M f).updateCol a y = M (Function.update f a ⟨y, hy⟩) := by
            ext k b
            by_cases hb : b = a
            · subst hb; simp [M]
            · simp [M, Matrix.updateCol_ne hb, Function.update_of_ne hb]
          rw [Pi.smul_apply, smul_eq_mul, Matrix.cramer_apply, h1, map_mul, map_inv₀, norm_mul, norm_inv,
            inv_mul_le_iff₀ hpos, mul_one]
          exact hf _
        · rw [Matrix.mulVec_smul, Matrix.mulVec_cramer, smul_smul, inv_mul_cancel₀ hdet, one_smul]
      | zero => exact ⟨0, by simp, by simp⟩
      | add y z _ _ hy hz =>
        obtain ⟨c, hc, rfl⟩ := hy
        obtain ⟨c', hc', rfl⟩ := hz
        refine ⟨c + c', fun a => ?_, by rw [Matrix.mulVec_add]⟩
        rw [Pi.add_apply, map_add]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hc a) (hc' a))
      | smul r y _ hy =>
        obtain ⟨c, hc, rfl⟩ := hy
        refine ⟨(r : D.host.E) • c, fun a => ?_, by rw [Matrix.mulVec_smul]; rfl⟩
        rw [Pi.smul_apply, smul_eq_mul, map_mul, norm_mul]
        exact mul_le_one₀ (norm_int_le ρ r) (norm_nonneg _) (hc a)
    obtain ⟨c, hc, rfl⟩ := key
    obtain ⟨t, n, ht, hn⟩ := exists_common_denom ρ c hc
    refine ⟨t, ht, n, ?_⟩
    funext k
    rw [Finset.sum_apply]
    change (t : D.host.E) * (∑ a, M f k a * c a) = ∑ a, (n a : D.host.E) * M f k a
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [← hn a]; ring

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `h`. Use `⟨?_, le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)⟩` and prove the remaining obligations. Use `ρ.map_det P` as an intermediate fact. Rewrite `this` using `[RingHom.mapMatrix_apply]`. Rewrite using `[← this]`.

Conclude with `(map_ne_zero ρ).2 h1`. Introduce and unpack `_ ⟨a, rfl⟩`. Take `⟨s, hs, hL⟩` from `h2 a`. Establish `h0 : ρ (s : D.host.E) ≠ 0` using `norm_pos_iff.1 (by rw [hs]; exact one_pos)`. Establish `hm` using `Submodule.smul_mem _ (⟨(ρ (s : D.host.E))⁻¹, (mem_int_iff _).2 (by rw [norm_inv, hs, inv_one])⟩ : 𝓞_ℂ_[p]) (Submodule.subset_span (R := 𝓞_ℂ_[p]) (Set.mem_image_of_mem (fun (x : Fin N → D.host.E) k => ρ (x k)) (show _ ∈ (L : Set _) from hL)))`.

Use `Set.mem_of_eq_of_mem (funext fun k => ?_) hm` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `ρ (P k a) = (ρ (s : D.host.E))⁻¹ * ρ ((s : D.host.E) * P k a)`. Rewrite using `[map_mul, inv_mul_cancel_left₀ h0]`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Take `⟨s, hs, c, hc⟩` from `h3 x hx`.

Establish `h0 : ρ (s : D.host.E) ≠ 0` using `norm_pos_iff.1 (by rw [hs]; exact one_pos)`. Use `(Submodule.mem_span_range_iff_exists_fun _).2 ⟨fun a => ⟨(ρ (s : D.host.E))⁻¹ * ρ (c a : D.host.E), (mem_int_iff _).2 ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[norm_mul, norm_inv, hs, inv_one, one_mul]`. Conclude with `norm_int_le ρ _`. Use function extensionality and compare the values at `k`.

Establish `hk` using `congrFun hc k`. Rewrite `hk`, the goal using `[Finset.sum_apply]`. Express the relevant statement in the definitionally equal form `(s : D.host.E) * x k = ∑ a, (c a : D.host.E) * P k a at hk`. Express the relevant statement in the definitionally equal form `∑ a, (ρ (s : D.host.E))⁻¹ * ρ (c a : D.host.E) * ρ (P k a) = ρ (x k)`. Simplify using `only [mul_assoc, ← map_mul, ← Finset.mul_sum, ← map_sum]`.

Rewrite using `[← hk, map_mul, inv_mul_cancel_left₀ h0]`.
-/
theorem isRBasis_of_locBasis (D : D7) (ρ : D.host.E →+* ℂ_[p]) {N : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {P : Matrix (Fin N) (Fin N) D.host.E} (h : TaylorLogMetric.LocBasisW D ρ L P) : IsRBasis D ρ L (P.map ρ) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)⟩
  · have := ρ.map_det P
    rw [RingHom.mapMatrix_apply] at this
    rw [← this]
    exact (map_ne_zero ρ).2 h1
  · rintro _ ⟨a, rfl⟩
    obtain ⟨s, hs, hL⟩ := h2 a
    have h0 : ρ (s : D.host.E) ≠ 0 := norm_pos_iff.1 (by rw [hs]; exact one_pos)
    have hm := Submodule.smul_mem _ (⟨(ρ (s : D.host.E))⁻¹, (mem_int_iff _).2 (by rw [norm_inv, hs, inv_one])⟩ : 𝓞_ℂ_[p])
      (Submodule.subset_span (R := 𝓞_ℂ_[p])
        (Set.mem_image_of_mem (fun (x : Fin N → D.host.E) k => ρ (x k)) (show _ ∈ (L : Set _) from hL)))
    refine Set.mem_of_eq_of_mem (funext fun k => ?_) hm
    change ρ (P k a) = (ρ (s : D.host.E))⁻¹ * ρ ((s : D.host.E) * P k a)
    rw [map_mul, inv_mul_cancel_left₀ h0]
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨s, hs, c, hc⟩ := h3 x hx
    have h0 : ρ (s : D.host.E) ≠ 0 := norm_pos_iff.1 (by rw [hs]; exact one_pos)
    refine (Submodule.mem_span_range_iff_exists_fun _).2
      ⟨fun a => ⟨(ρ (s : D.host.E))⁻¹ * ρ (c a : D.host.E), (mem_int_iff _).2 ?_⟩, ?_⟩
    · rw [norm_mul, norm_inv, hs, inv_one, one_mul]
      exact norm_int_le ρ _
    · funext k
      have hk := congrFun hc k
      rw [Finset.sum_apply] at hk ⊢
      change (s : D.host.E) * x k = ∑ a, (c a : D.host.E) * P k a at hk
      change ∑ a, (ρ (s : D.host.E))⁻¹ * ρ (c a : D.host.E) * ρ (P k a) = ρ (x k)
      simp only [mul_assoc, ← map_mul, ← Finset.mul_sum, ← map_sum]
      rw [← hk, map_mul, inv_mul_cancel_left₀ h0]

/- English proof (translation)
Establish `h1 : (fun k => g k b) ∈ Submodule.span 𝓞_ℂ_[p] (Set.range fun a : Fin N => fun k => h k a)`. Rewrite using `[hh.2, ← hg.2]`. Conclude with `Submodule.subset_span ⟨b, rfl⟩`. Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun _).1 h1`. Establish `h2 : (fun k => g k b) = h.mulVec fun a => (c a : ℂ_[p])`.

Rewrite using `[← hc]`. Use function extensionality and compare the values at `k`. Rewrite using `[Finset.sum_apply]`. Conclude with `Finset.sum_congr rfl fun a _ => mul_comm _ _`. Establish `h3 : (h⁻¹ * g) a b = (h⁻¹.mulVec fun k => g k b) a` using `rfl`.

Rewrite using `[h3, h2, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (Ne.isUnit hh.1), Matrix.one_mulVec]`. Conclude with `(mem_int_iff _).1 (c a).2`.
-/
theorem transition_integral (D : D7) (ρ : D.host.E → ℂ_[p]) {N : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {g h : Matrix (Fin N) (Fin N) ℂ_[p]} (hg : IsRBasis D ρ L g) (hh : IsRBasis D ρ L h) (a b : Fin N) :
    ‖(h⁻¹ * g) a b‖ ≤ 1 := by
  have h1 : (fun k => g k b) ∈ Submodule.span 𝓞_ℂ_[p] (Set.range fun a : Fin N => fun k => h k a) := by
    rw [hh.2, ← hg.2]
    exact Submodule.subset_span ⟨b, rfl⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 h1
  have h2 : (fun k => g k b) = h.mulVec fun a => (c a : ℂ_[p]) := by
    rw [← hc]
    funext k
    rw [Finset.sum_apply]
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  have h3 : (h⁻¹ * g) a b = (h⁻¹.mulVec fun k => g k b) a := rfl
  rw [h3, h2, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (Ne.isUnit hh.1), Matrix.one_mulVec]
  exact (mem_int_iff _).1 (c a).2

/- English proof (translation)
Establish `h : ∀ x, TaylorLogMetric.embT D τ x ∈ TaylorLogMetric.Qbar` using `fun x => mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom (TaylorLogMetric.embT D τ).toRatAlgHom)`. Use `⟨lam.comp ((TaylorLogMetric.embT D τ).codRestrict TaylorLogMetric.Qbar h), funext fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[TaylorLogMetric.tauEmb, TaylorLogMetric.lamC, dif_pos (h x)]`. Both sides reduce to the same expression.
-/
theorem exists_tauHom (D : D7) (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (τ : D.what₂.Tau) :
    ∃ ρ : D.host.E →+* ℂ_[p], TaylorLogMetric.tauEmb D lam τ = ρ := by
  have h : ∀ x, TaylorLogMetric.embT D τ x ∈ TaylorLogMetric.Qbar := fun x =>
    mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom (TaylorLogMetric.embT D τ).toRatAlgHom)
  refine ⟨lam.comp ((TaylorLogMetric.embT D τ).codRestrict TaylorLogMetric.Qbar h), funext fun x => ?_⟩
  rw [TaylorLogMetric.tauEmb, TaylorLogMetric.lamC, dif_pos (h x)]
  rfl

end GlobalTheory.JetTieCompare
