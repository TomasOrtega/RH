import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CapRDefs
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.ContinuousLev
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.GoodSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransposeMulIncl
open MeasureTheory NumberField GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace UpperTheory.ConvolutionTheory.BW

section
open GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Cm GlobalTheory.GLSlice

variable {E : Type} [Field E] [NumberField E] {r s : ℕ}

/- English proof (translation)
Take `⟨D, hD, hsub⟩` from `exists_isCompact_superset_unipFundamentalDomain (K := E) (n := n) (r := r)`. Take `⟨M, hM⟩` from `CuspidalSpectrum.exists_height_le_of_isCompact (hD.image continuous_unipGL)`. Establish `hc0 : 0 ≤ heightConst E n` using `le_trans zero_le_one one_le_heightConst`. Establish `hfin : unipMeasure E n r (unipFundamentalDomain E n r) < ⊤` using `(measure_mono hsub).trans_lt hD.measure_lt_top`. Use `⟨|C| * (heightConst E n * |M|) ^ N * (unipMeasure E n r).real (unipFundamentalDomain E n r), by positivity, fun g => ?_⟩` and prove the remaining obligations.

Establish `hg` using `(height_pos g).le`. Establish `hb : ∀ X ∈ unipFundamentalDomain E n r, ‖φ (unipGL X * g)‖ ≤ |C| * (heightConst E n * |M| * AutomorphicForm.height g) ^ N`. Introduce `X hX`. Establish `h1 : AutomorphicForm.height (unipGL X * g) ≤ heightConst E n * |M| * AutomorphicForm.height g` using `(height_mul_le _ _).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ((hM _ ⟨X, hsub hX, rfl⟩).trans (le_abs_self M)) hc0) hg)`. Conclude with `(hφ _).trans (mul_le_mul (le_abs_self C) (pow_le_pow_left₀ (height_pos _).le h1 N) (pow_nonneg (height_pos _).le N) (abs_nonneg C))`.

Use `(norm_setIntegral_le_of_norm_le_const hfin hb).trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[mul_pow (heightConst E n * |M|)]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem ct_growth {n : ℕ} (r : ℕ) (φ : GA E n → ℂ) {C : ℝ} {N : ℕ} (hφ : ∀ g, ‖φ g‖ ≤ C * AutomorphicForm.height g ^ N) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ g, ‖constantTerm r φ g‖ ≤ B * AutomorphicForm.height g ^ N := by
  obtain ⟨D, hD, hsub⟩ := exists_isCompact_superset_unipFundamentalDomain (K := E) (n := n) (r := r)
  obtain ⟨M, hM⟩ := CuspidalSpectrum.exists_height_le_of_isCompact (hD.image continuous_unipGL)
  have hc0 : 0 ≤ heightConst E n := le_trans zero_le_one one_le_heightConst
  have hfin : unipMeasure E n r (unipFundamentalDomain E n r) < ⊤ := (measure_mono hsub).trans_lt hD.measure_lt_top
  refine ⟨|C| * (heightConst E n * |M|) ^ N * (unipMeasure E n r).real (unipFundamentalDomain E n r), by positivity, fun g => ?_⟩
  have hg := (height_pos g).le
  have hb : ∀ X ∈ unipFundamentalDomain E n r,
      ‖φ (unipGL X * g)‖ ≤ |C| * (heightConst E n * |M| * AutomorphicForm.height g) ^ N := by
    intro X hX
    have h1 : AutomorphicForm.height (unipGL X * g) ≤ heightConst E n * |M| * AutomorphicForm.height g :=
      (height_mul_le _ _).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left ((hM _ ⟨X, hsub hX, rfl⟩).trans (le_abs_self M)) hc0) hg)
    exact (hφ _).trans (mul_le_mul (le_abs_self C) (pow_le_pow_left₀ (height_pos _).le h1 N)
      (pow_nonneg (height_pos _).le N) (abs_nonneg C))
  refine (norm_setIntegral_le_of_norm_le_const hfin hb).trans (le_of_eq ?_)
  rw [mul_pow (heightConst E n * |M|)]
  ring

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Establish `hs : GlobalTheory.SmGL.stdSum (rfl : r + s = r + s) = finSumFinEquiv`. Apply the tactic sequence `ext (x | x) <;> simp`. Establish `hn : ∀ (q : Fin s) (p : Fin r), Fin.castAddEmb s p ≠ Fin.natAdd r q` using `fun q p h => by`. Use `congrArg Fin.val h` as an intermediate fact.

Use `p.isLt` as an intermediate fact. Simplify using `at *`. Use linear arithmetic over natural numbers and integers. Rewrite using `[GlobalTheory.SmGL.val_emb₂, hs, embGL_val]`. Use extensionality with `i j`.

Rewrite using `[Matrix.add_apply, Matrix.sub_apply]`. Proceed by induction on `i using Fin.addCases with`. Consider the case `left i`. Proceed by induction on `j using Fin.addCases with`. Consider the case `left j`.

Establish `h1` using `extN_apply_apply (R := R) (Fin.castAddEmb s) 1 i j`. Establish `h2` using `extN_apply_apply (R := R) (Fin.castAddEmb s) g.val i j`. Simplify using `only [Fin.castAddEmb_apply] at h1 h2`. Rewrite using `[h1, h2]`. Simplify using `[Matrix.one_apply]`.

Consider the case `right j`. Simplify using `only [extN_apply_right _ _ _ (hn j)]`. Use `hn j i` as an intermediate fact. Simplify using `only [Fin.castAddEmb_apply] at this`. Simplify using `[Matrix.one_apply, this]`.

Consider the case `right i`. Simplify using `only [extN_apply_left _ _ (hn i)]`. Proceed by induction on `j using Fin.addCases with`. Consider the case `left j`. Use `(hn i j).symm` as an intermediate fact.

Simplify using `only [Fin.castAddEmb_apply] at this`. Simplify using `[Matrix.one_apply, this]`. Consider the case `right j => simp [Matrix.one_apply]`.
-/
private theorem emb_eq {R : Type} [CommRing R] (g : GL (Fin r) R) : embGL (Fin.castAddEmb s) g = lev R r s (g, 1) := by
  apply Units.ext
  have hs : GlobalTheory.SmGL.stdSum (rfl : r + s = r + s) = finSumFinEquiv := by
    ext (x | x) <;> simp
  have hn : ∀ (q : Fin s) (p : Fin r), Fin.castAddEmb s p ≠ Fin.natAdd r q := fun q p h => by
    have := congrArg Fin.val h
    have := p.isLt
    simp at *
    omega
  rw [GlobalTheory.SmGL.val_emb₂, hs, embGL_val]
  ext i j
  rw [Matrix.add_apply, Matrix.sub_apply]
  induction i using Fin.addCases with
  | left i =>
    induction j using Fin.addCases with
    | left j =>
      have h1 := extN_apply_apply (R := R) (Fin.castAddEmb s) 1 i j
      have h2 := extN_apply_apply (R := R) (Fin.castAddEmb s) g.val i j
      simp only [Fin.castAddEmb_apply] at h1 h2
      rw [h1, h2]
      simp [Matrix.one_apply]
    | right j =>
      simp only [extN_apply_right _ _ _ (hn j)]
      have := hn j i
      simp only [Fin.castAddEmb_apply] at this
      simp [Matrix.one_apply, this]
  | right i =>
    simp only [extN_apply_left _ _ (hn i)]
    induction j using Fin.addCases with
    | left j =>
      have := (hn i j).symm
      simp only [Fin.castAddEmb_apply] at this
      simp [Matrix.one_apply, this]
    | right j => simp [Matrix.one_apply]

variable [IsTotallyComplex E]

/- English proof (translation)
Establish `hu : u ∈ Algebra.adjoin ℂ {x : UC E r | ∃ τ i j, x = genC τ i j}` using `by rw [adjoin_genC]; trivial`. Proceed by induction on `hu using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Take `⟨τ, i, j, rfl⟩` from `hx`. Conclude with `⟨genC τ (f i) (f j), fun F => by rw [uC_genC, uC_genC, Eop_slice]⟩`.

Consider the case `algebraMap c`. Conclude with `⟨algebraMap ℂ _ c, fun F => by`. Rewrite using `[AlgHom.commutes, AlgHom.commutes, Module.algebraMap_end_apply, Module.algebraMap_end_apply, map_smul]⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨a, ha⟩` from `hx`.

Take `⟨b, hb⟩` from `hy`. Conclude with `⟨a + b, fun F => by rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, map_add, ha, hb]⟩`. Consider the case `mul x y _ _ hx hy`. Take `⟨a, ha⟩` from `hx`. Take `⟨b, hb⟩` from `hy`.

Conclude with `⟨a * b, fun F => by rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hb, ha]⟩`.
-/
private theorem uc_slice (f : Fin r ↪ Fin (r + s)) (g : GA E (r + s)) (u : UC E r) :
    ∃ u' : UC E (r + s), ∀ F, uC E r u (GlobalTheory.GLSlice.slice f g F) = GlobalTheory.GLSlice.slice f g (uC E (r + s) u' F) := by
  have hu : u ∈ Algebra.adjoin ℂ {x : UC E r | ∃ τ i j, x = genC τ i j} := by rw [adjoin_genC]; trivial
  induction hu using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨τ, i, j, rfl⟩ := hx
    exact ⟨genC τ (f i) (f j), fun F => by rw [uC_genC, uC_genC, Eop_slice]⟩
  | algebraMap c =>
    exact ⟨algebraMap ℂ _ c, fun F => by
      rw [AlgHom.commutes, AlgHom.commutes, Module.algebraMap_end_apply, Module.algebraMap_end_apply, map_smul]⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, fun F => by rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, map_add, ha, hb]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a * b, fun F => by rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hb, ha]⟩

private def stab {n : ℕ} (ψ : Sm E n) : Subgroup (GL (Fin n) (Af E)) where
  carrier := {k | finRep E n k ψ = ψ}
  one_mem' := by simp
  mul_mem' := fun {x y} hx hy => by
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    rw [map_mul, Module.End.mul_apply, hy, hx]
  inv_mem' := fun {x} hx => by
    simp only [Set.mem_setOf_eq] at hx ⊢
    conv_lhs => rw [← hx]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

end

/- English proof (translation)
Introduce `E _ _ _ r s φ Φ x m _ hφ hx hΦ`. Take `⟨F, hF, -, hl, hu⟩` from `ctOps E r s φ hφ`. Establish `he : ∀ g, lev (Ad E) r s (x, m) * GlobalTheory.GLSlice.embGL (Fin.castAddEmb s) g = lev (Ad E) r s (x * g, m)` using `fun g => by`. Rewrite using `[emb_eq, ← map_mul, Prod.mk_mul_mk, mul_one]`. Establish `hs : Φ = GlobalTheory.GLSlice.slice (Fin.castAddEmb s) (lev (Ad E) r s (x, m)) F` using `Subtype.ext (funext fun g => by rw [GlobalTheory.GLSlice.slice_apply, he, hF, hΦ])`.

Use `⟨fun γ g => ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `h1` using `hl (γ, 1) (lev (Ad E) r s (x * g, m))`. Rewrite `h1` using `[← map_mul, Prod.mk_mul_mk, map_one, one_mul, ← mul_assoc, ← hx, mul_assoc, hF]`. Rewrite using `[hΦ, hΦ]`. Conclude with `h1`.

Establish `ho : IsOpen ((GlobalTheory.GLSlice.embGL (Fin.castAddEmb s)) ⁻¹' {k | finRep E (r + s) k φ = φ})` using `hφ.level.preimage (GlobalTheory.GLSlice.continuous_embGL _)`. Use `Subgroup.isOpen_of_mem_nhds (stab Φ) (g := 1) (Filter.mem_of_superset (ho.mem_nhds (by simp)) fun k hk => ?_)` and prove the remaining obligations. Use `Subtype.ext (funext fun g => ?_)` and prove the remaining obligations. Establish `hk' : ∀ y, φ.1 (y * finGL E (r + s) (GlobalTheory.GLSlice.embGL (Fin.castAddEmb s) k)) = φ.1 y` using `fun y => congrFun (congrArg Subtype.val hk) y`. Express the relevant statement in the definitionally equal form `Φ.1 (g * finGL E r k) = Φ.1 g`.

Rewrite using `[hΦ, hΦ, ← he, ← he, map_mul, GlobalTheory.GLSlice.embGL_finGL, ← mul_assoc]`. Unfold `AutomorphicForm.constantTerm`. Simplify using `only [← mul_assoc, hk']`. Take `⟨N, hN⟩` from `hφ.growth`. Use `⟨N, fun u => ?_⟩` and prove the remaining obligations.

Take `⟨u', hu'⟩` from `uc_slice (Fin.castAddEmb s) (lev (Ad E) r s (x, m)) u`. Take `⟨B, hB⟩` from `hN u'`. Take `⟨C, hC0, hC⟩` from `ct_growth r _ hB`. Use `⟨C * (AutomorphicForm.heightConst E (r + s) * (AutomorphicForm.heightConst E r * AutomorphicForm.height x) * AutomorphicForm.height m) ^ N, fun g => ?_⟩` and prove the remaining obligations. Rewrite using `[hs, hu', GlobalTheory.GLSlice.slice_apply, he, hu, mul_assoc, ← mul_pow]`.

Use `(hC _).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (AutomorphicForm.height_pos _).le ?_ N) hC0)` and prove the remaining obligations. Use `(Pair.height_lev _ _).trans ?_` and prove the remaining obligations. Establish `h0 : 0 ≤ AutomorphicForm.heightConst E (r + s)` using `zero_le_one.trans AutomorphicForm.one_le_heightConst`. Establish `h1` using `mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (AutomorphicForm.height_mul_le (K := E) x g) h0) (AutomorphicForm.height_pos (K := E) m).le`. Use `h1.trans (le_of_eq ?_)` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.constantTerm_leviRestriction_moderateGrowth :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r s : ℕ) (φ : Sm E (r + s)) (Φ : Sm E r) (x : GA E r) (m : GA E s), 0 < r → Umg φ →
          (∀ γ : GL (Fin r) E, x * ratGL E r γ = ratGL E r γ * x) →
          (∀ g, Φ.1 g = AutomorphicForm.constantTerm r φ.1 (lev (Ad E) r s (x * g, m))) → Umg Φ := by
  intro E _ _ _ r s φ Φ x m _ hφ hx hΦ
  obtain ⟨F, hF, -, hl, hu⟩ := ctOps E r s φ hφ
  have he : ∀ g, lev (Ad E) r s (x, m) * GlobalTheory.GLSlice.embGL (Fin.castAddEmb s) g = lev (Ad E) r s (x * g, m) := fun g => by
    rw [emb_eq, ← map_mul, Prod.mk_mul_mk, mul_one]
  have hs : Φ = GlobalTheory.GLSlice.slice (Fin.castAddEmb s) (lev (Ad E) r s (x, m)) F :=
    Subtype.ext (funext fun g => by rw [GlobalTheory.GLSlice.slice_apply, he, hF, hΦ])
  refine ⟨fun γ g => ?_, ?_, ?_⟩
  · have h1 := hl (γ, 1) (lev (Ad E) r s (x * g, m))
    rw [← map_mul, Prod.mk_mul_mk, map_one, one_mul, ← mul_assoc, ← hx, mul_assoc, hF] at h1
    rw [hΦ, hΦ]
    exact h1
  · have ho : IsOpen ((GlobalTheory.GLSlice.embGL (Fin.castAddEmb s)) ⁻¹' {k | finRep E (r + s) k φ = φ}) :=
      hφ.level.preimage (GlobalTheory.GLSlice.continuous_embGL _)
    refine Subgroup.isOpen_of_mem_nhds (stab Φ) (g := 1) (Filter.mem_of_superset (ho.mem_nhds (by simp)) fun k hk => ?_)
    refine Subtype.ext (funext fun g => ?_)
    have hk' : ∀ y, φ.1 (y * finGL E (r + s) (GlobalTheory.GLSlice.embGL (Fin.castAddEmb s) k)) = φ.1 y :=
      fun y => congrFun (congrArg Subtype.val hk) y
    change Φ.1 (g * finGL E r k) = Φ.1 g
    rw [hΦ, hΦ, ← he, ← he, map_mul, GlobalTheory.GLSlice.embGL_finGL, ← mul_assoc]
    unfold AutomorphicForm.constantTerm
    simp only [← mul_assoc, hk']
  · obtain ⟨N, hN⟩ := hφ.growth
    refine ⟨N, fun u => ?_⟩
    obtain ⟨u', hu'⟩ := uc_slice (Fin.castAddEmb s) (lev (Ad E) r s (x, m)) u
    obtain ⟨B, hB⟩ := hN u'
    obtain ⟨C, hC0, hC⟩ := ct_growth r _ hB
    refine ⟨C * (AutomorphicForm.heightConst E (r + s) * (AutomorphicForm.heightConst E r * AutomorphicForm.height x) *
      AutomorphicForm.height m) ^ N, fun g => ?_⟩
    rw [hs, hu', GlobalTheory.GLSlice.slice_apply, he, hu, mul_assoc, ← mul_pow]
    refine (hC _).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (AutomorphicForm.height_pos _).le ?_ N) hC0)
    refine (Pair.height_lev _ _).trans ?_
    have h0 : 0 ≤ AutomorphicForm.heightConst E (r + s) := zero_le_one.trans AutomorphicForm.one_le_heightConst
    have h1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (AutomorphicForm.height_mul_le (K := E) x g) h0)
      (AutomorphicForm.height_pos (K := E) m).le
    refine h1.trans (le_of_eq ?_)
    ring
