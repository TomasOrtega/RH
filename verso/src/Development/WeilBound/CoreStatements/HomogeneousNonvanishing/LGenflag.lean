import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjugateHermitianLineIsometries
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HodgeIPIffHodgeFormConj
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.LGenflagFld

open MvPolynomial AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp

namespace PositivityTheory.UnitarySelfGeneration

/- English proof (translation)
Introduce `k`. Rewrite using `[hA k]`. Repeatedly rewrite using `[hB, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]`.
-/
private theorem l_genflag_lemma_0 {Ω E : Type} [Field Ω] [AddCommGroup E] [Module Ω E] {n : ℕ}
    (c'' c' c : Fin n → E) {A B : Matrix (Fin n) (Fin n) Ω} (hA : ∀ k, c'' k = ∑ l, A l k • c' l)
    (hB : ∀ k, c' k = ∑ l, B l k • c l) : ∀ k, c'' k = ∑ p, (B * A) p k • c p := by
  intro k
  rw [hA k]
  simp_rw [hB, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]

/- English proof (translation)
Use `choose f hf using fun k => (Submodule.mem_span_range_iff_exists_fun Ω).1 (hc k)`. Conclude with `⟨Matrix.of fun l k => f k l, fun k => by simp only [Matrix.of_apply]; exact (hf k).symm⟩`.
-/
private theorem l_genflag_lemma {Ω E : Type} [Field Ω] [AddCommGroup E] [Module Ω E] {n : ℕ}
    (c c' : Fin n → E) (hc : ∀ k, c k ∈ Submodule.span Ω (Set.range c')) :
    ∃ h : Matrix (Fin n) (Fin n) Ω, ∀ k, c k = ∑ l, h l k • c' l := by
  choose f hf using fun k => (Submodule.mem_span_range_iff_exists_fun Ω).1 (hc k)
  exact ⟨Matrix.of fun l k => f k l, fun k => by simp only [Matrix.of_apply]; exact (hf k).symm⟩

/- English proof (translation)
Establish `key` using `l_genflag_lemma_0 c c' c hh hP`. Use extensionality with `p k`. Use `Fintype.linearIndependent_iff.1 hc (fun p => (P * h) p k - (1 : Matrix (Fin n) (Fin n) Ω) p k) (by simp [sub_smul, Finset.sum_sub_distrib, ← key k, Matrix.one_apply]) p` as an intermediate fact. Conclude with `sub_eq_zero.1 this`.
-/
private theorem l_genflag_lemma_2 {Ω E : Type} [Field Ω] [AddCommGroup E] [Module Ω E] {n : ℕ}
    (c c' : Fin n → E) (hc : LinearIndependent Ω c) {h P : Matrix (Fin n) (Fin n) Ω}
    (hh : ∀ k, c k = ∑ l, h l k • c' l) (hP : ∀ k, c' k = ∑ l, P l k • c l) : P * h = 1 := by
  have key := l_genflag_lemma_0 c c' c hh hP
  ext p k
  have := Fintype.linearIndependent_iff.1 hc (fun p => (P * h) p k - (1 : Matrix (Fin n) (Fin n) Ω) p k)
    (by simp [sub_smul, Finset.sum_sub_distrib, ← key k, Matrix.one_apply]) p
  exact sub_eq_zero.1 this

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨v, hv, rfl⟩`. Simplify using `only [SetLike.mem_coe]`. Proceed by induction on `hv using Submodule.span_induction with`.

Consider the case `mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩`. Consider the case `zero`. Use `(Submodule.span K ((fun v l => f (v l)) '' S)).zero_mem using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `l`. Simplify using the standard rewrite rules.

Consider the case `add x y _ _ hx hy`. Use `Submodule.add_mem _ hx hy using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `l`. Simplify using the standard rewrite rules. Consider the case `smul a x _ hx`.

Use `Submodule.smul_mem _ (f a) hx using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `l`. Simplify using the standard rewrite rules. Conclude with `Submodule.span_mono (Set.image_mono Submodule.subset_span)`.
-/
private theorem l_genflag_lemma_3 {F K : Type} [Field F] [Field K] (f : F →+* K) {n : ℕ} (S : Set (Fin n → F)) :
    Submodule.span K ((fun v l => f (v l)) '' (Submodule.span F S : Set (Fin n → F))) =
      Submodule.span K ((fun v l => f (v l)) '' S) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    simp only [SetLike.mem_coe]
    induction hv using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero =>
      convert (Submodule.span K ((fun v l => f (v l)) '' S)).zero_mem using 1
      funext l
      simp
    | add x y _ _ hx hy =>
      convert Submodule.add_mem _ hx hy using 1
      funext l
      simp
    | smul a x _ hx =>
      convert Submodule.smul_mem _ (f a) hx using 1
      funext l
      simp
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

/- English proof (translation)
Establish `key : ∀ N : Matrix (Fin n) (Fin n) F, GF.fl (N.map f) t = Submodule.span K ((fun v l => f (v l)) '' (GF.fl N t : Set (Fin n → F)))`. Introduce `N`. Simplify using `only [GF.fl, flagStep]`. Rewrite using `[l_genflag_lemma_3, Set.image_image]`. Both sides reduce to the same expression.

Rewrite using `[key, key, h]`.
-/
private theorem l_genflag_lemma_4 {F K : Type} [Field F] [Field K] (f : F →+* K) {n : ℕ}
    {M M' : Matrix (Fin n) (Fin n) F} {t : ℕ} (h : GF.fl M t = GF.fl M' t) :
    GF.fl (M.map f) t = GF.fl (M'.map f) t := by
  have key : ∀ N : Matrix (Fin n) (Fin n) F, GF.fl (N.map f) t =
      Submodule.span K ((fun v l => f (v l)) '' (GF.fl N t : Set (Fin n → F))) := by
    intro N
    simp only [GF.fl, flagStep]
    rw [l_genflag_lemma_3, Set.image_image]
    rfl
  rw [key, key, h]

/- English proof (translation)
Establish `key : ∀ M : Matrix (Fin n) (Fin n) F, GF.fl (N * M) t = (GF.fl M t).map (Matrix.mulVecLin N)`. Introduce `M`. Simplify using `only [GF.fl, flagStep, Submodule.map_span, Set.image_image]`. Use `congr 2`. Rewrite using `[key, key, h]`.
-/
private theorem l_genflag_lemma_5 {F : Type} [Field F] {n : ℕ} (N : Matrix (Fin n) (Fin n) F)
    {M M' : Matrix (Fin n) (Fin n) F} {t : ℕ} (h : GF.fl M t = GF.fl M' t) :
    GF.fl (N * M) t = GF.fl (N * M') t := by
  have key : ∀ M : Matrix (Fin n) (Fin n) F, GF.fl (N * M) t = (GF.fl M t).map (Matrix.mulVecLin N) := by
    intro M
    simp only [GF.fl, flagStep, Submodule.map_span, Set.image_image]
    congr 2
  rw [key, key, h]

open GF in
/- English proof (translation)
Introduce `Ω Ω₁ Ω₂ _ _ _ _ _ E E₁ E₂ _ _ _ _ _ _ j₁ j₂ S _ r V b₁ b₂ d₁ d₂ hG1 hG2`. Unfold `IsGenericFlag at hG1 hG2`. Take `⟨c1, u1, hc1, hj1, hjc1, -, hd1, hup1, hfl1, hai1, hdpos1, hrk1⟩` from `hG1`. Take `⟨c2, u2, hc2, hj2, hjc2, -, hd2, hup2, hfl2, hai2, hdpos2, hrk2⟩` from `hG2`. Establish `hU1 : ∀ σ, GF.Uni (u1 σ)` using `fun σ => ⟨hd1 σ, hup1 σ⟩`.

Establish `hU2 : ∀ σ, GF.Uni (u2 σ)` using `fun σ => ⟨hd2 σ, hup2 σ⟩`. Rewrite `hrk1` using `[GF.adjoin_all u1 hU1]`. Rewrite `hrk2` using `[GF.adjoin_all u2 hU2]`. Establish `hfd1 : FiniteDimensional (IntermediateField.adjoin Ω (Set.range (GF.ent u1))) Ω₁` using `Module.finite_of_finrank_pos (by rw [hrk1]; exact hdpos1)`. Establish `hfd2 : FiniteDimensional (IntermediateField.adjoin Ω (Set.range (GF.ent u2))) Ω₂` using `Module.finite_of_finrank_pos (by rw [hrk2]; exact hdpos2)`.

Establish `hA : ∀ σ, ∃ A : Matrix (Fin (r σ)) (Fin (r σ)) Ω, (∀ k, c2 σ k = ∑ l, A l k • c1 σ l) ∧ A.det ≠ 0`. Introduce `σ`. Take `⟨A, hA⟩` from `l_genflag_lemma (c2 σ) (c1 σ) (fun k => by rw [(hc1 σ).2, ← (hc2 σ).2]; exact Submodule.subset_span ⟨k, rfl⟩)`. Take `⟨B, hB⟩` from `l_genflag_lemma (c1 σ) (c2 σ) (fun k => by rw [(hc2 σ).2, ← (hc1 σ).2]; exact Submodule.subset_span ⟨k, rfl⟩)`. Use `⟨A, hA, fun h0 => ?_⟩` and prove the remaining obligations.

Establish `hBA` using `congrArg Matrix.det (l_genflag_lemma_2 (c2 σ) (c1 σ) (hc2 σ).1 hA hB)`. Rewrite `hBA` using `[Matrix.det_mul, Matrix.det_one, h0, mul_zero]`. Conclude with `zero_ne_one hBA`. Use `choose A hAc hAdet using hA`. Take `⟨u2', hU2', hai2', hadj, hfl2'⟩` from `GF.change u2 hU2 hai2 hfd2 A hAdet`.

Establish `hfd2' : FiniteDimensional (IntermediateField.adjoin Ω (Set.range (GF.ent u2'))) Ω₂`. Rewrite using `[hadj]`. Conclude with `hfd2`. Establish `hrk2' : Module.finrank (IntermediateField.adjoin Ω (Set.range (GF.ent u2'))) Ω₂ = d₂`. Rewrite using `[hadj]`.

Conclude with `hrk2`. Take `⟨Ω₃, hF3, i₁, i₂, hα, hq, n₁, n₂, hn, hdeg, hr1, hr2⟩` from `GF.compositum' (GF.ent u1) (GF.ent u2') hai1 hai2' hfd1 hfd2'`. Establish `hU : ∀ σ, (u1 σ).map i₁ = (u2' σ).map i₂`. Introduce `σ`. Use extensionality with `l k`.

Simplify using `only [Matrix.map_apply]`. Break down `lt_trichotomy k l with hkl | rfl | hlk` into its components or cases. Conclude with `hq ⟨σ, ⟨(l, k), hkl⟩⟩`. Rewrite using `[(hU1 σ).1 k, (hU2' σ).1 k, map_one, map_one]`. Rewrite using `[(hU1 σ).2 l k hlk, (hU2' σ).2 l k hlk, map_zero, map_zero]`.

Use `⟨Ω₃, hF3, i₁, i₂, RingHom.ext hα, ⟨n₁, n₂, hn, ?_, hr1, hr2⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← hrk1, ← hrk2', hdeg]`. Introduce `s c m₁ m₂ hc hspan hb1 hb2 i`. Take `⟨h1, hh1⟩` from `l_genflag_lemma c (c1 s) (fun k => by rw [(hc1 s).2, ← hspan]; exact Submodule.subset_span ⟨k, rfl⟩)`. Take `⟨P1, hP1⟩` from `l_genflag_lemma (c1 s) c (fun k => by rw [hspan, ← (hc1 s).2]; exact Submodule.subset_span ⟨k, rfl⟩)`.

Establish `hP2 : ∀ k, c2 s k = ∑ p, (P1 * A s) p k • c p` using `l_genflag_lemma_0 (c2 s) (c1 s) c (hAc s) hP1`. Take `⟨h2, hh2⟩` from `l_genflag_lemma c (c2 s) (fun k => by rw [(hc2 s).2, ← hspan]; exact Submodule.subset_span ⟨k, rfl⟩)`. Establish `e1 : P1 * h1 = 1` using `l_genflag_lemma_2 c (c1 s) hc hh1 hP1`. Establish `e2 : (P1 * A s) * h2 = 1` using `l_genflag_lemma_2 c (c2 s) hc hh2 hP2`. Establish `f1` using `GF.fl_coord j₁ hj1 (hjc1 s) hh1 hb1 (hfl1 s i)`.

Establish `f2` using `GF.fl_coord j₂ hj2 (hjc2 s) hh2 hb2 (hfl2 s i)`. Establish `g1 : GF.fl m₁ i = GF.fl (P1.map (algebraMap Ω Ω₁) * u1 s) i`. Use `l_genflag_lemma_5 (P1.map (algebraMap Ω Ω₁)) f1` as an intermediate fact. Rewrite `this` using `[← mul_assoc, ← Matrix.map_mul, e1, Matrix.map_one _ (map_zero _) (map_one _), one_mul]`. Then use the resulting hypothesis. Establish `g2 : GF.fl m₂ i = GF.fl ((P1 * A s).map (algebraMap Ω Ω₂) * u2 s) i`.

Use `l_genflag_lemma_5 ((P1 * A s).map (algebraMap Ω Ω₂)) f2` as an intermediate fact. Rewrite `this` using `[← mul_assoc, ← Matrix.map_mul, e2, Matrix.map_one _ (map_zero _) (map_one _), one_mul]`. Then use the resulting hypothesis. Express the relevant statement in the definitionally equal form `GF.fl (m₁.map i₁) i = GF.fl (m₂.map i₂) i`. Rewrite using `[l_genflag_lemma_4 i₁ g1, l_genflag_lemma_4 i₂ g2]`. Establish `hPβ : (P1.map (algebraMap Ω Ω₁)).map i₁ = (P1.map (algebraMap Ω Ω₂)).map i₂`.

Use extensionality with `l k`. Conclude with `hα (P1 l k)`. Establish `L : (P1.map (algebraMap Ω Ω₁) * u1 s).map i₁ = (P1.map (algebraMap Ω Ω₂)).map i₂ * (u2' s).map i₂`. Rewrite using `[Matrix.map_mul, hPβ, hU s]`. Establish `R : ((P1 * A s).map (algebraMap Ω Ω₂) * u2 s).map i₂ = (P1.map (algebraMap Ω Ω₂)).map i₂ * (((A s).map (algebraMap Ω Ω₂) * u2 s).map i₂)`.

Simplify using `only [Matrix.map_mul, mul_assoc]`. Rewrite using `[L, R]`. Conclude with `l_genflag_lemma_5 _ (l_genflag_lemma_4 i₂ (hfl2' s i))`.
-/
theorem l_genflag : ∀ (Ω Ω₁ Ω₂ : Type) [Field Ω] [Field Ω₁] [Field Ω₂] [Algebra Ω Ω₁] [Algebra Ω Ω₂] (E E₁ E₂ : Type) [AddCommGroup E] [Module Ω E] [AddCommGroup E₁] [Module Ω₁ E₁] [AddCommGroup E₂] [Module Ω₂ E₂] (j₁ : E →+ E₁) (j₂ : E →+ E₂) (S : Type) [Fintype S] (r : S → ℕ) (V : S → Submodule Ω E) (b₁ : ∀ s, Fin (r s) → E₁) (b₂ : ∀ s, Fin (r s) → E₂) (d₁ d₂ : ℕ), IsGenericFlag (Ω' := Ω₁) j₁ V b₁ d₁ → IsGenericFlag (Ω' := Ω₂) j₂ V b₂ d₂ → ∃ (Ω₃ : Type) (_ : Field Ω₃) (i₁ : Ω₁ →+* Ω₃) (i₂ : Ω₂ →+* Ω₃), i₁.comp (algebraMap Ω Ω₁) = i₂.comp (algebraMap Ω Ω₂) ∧ (∃ n₁ n₂ : ℕ, 0 < n₁ ∧ n₁ * d₁ = n₂ * d₂ ∧ Module.finrank i₁.fieldRange Ω₃ = n₁ ∧ Module.finrank i₂.fieldRange Ω₃ = n₂) ∧ ∀ s (c : Fin (r s) → E) (m₁ : Matrix (Fin (r s)) (Fin (r s)) Ω₁) (m₂ : Matrix (Fin (r s)) (Fin (r s)) Ω₂), LinearIndependent Ω c → Submodule.span Ω (Set.range c) = V s → (∀ k, b₁ s k = ∑ l, m₁ l k • j₁ (c l)) → (∀ k, b₂ s k = ∑ l, m₂ l k • j₂ (c l)) → ∀ i, flagStep Ω₃ (fun k l => i₁ (m₁ l k) : Fin (r s) → Fin (r s) → Ω₃) i = flagStep Ω₃ (fun k l => i₂ (m₂ l k) : Fin (r s) → Fin (r s) → Ω₃) i := by
  intro Ω Ω₁ Ω₂ _ _ _ _ _ E E₁ E₂ _ _ _ _ _ _ j₁ j₂ S _ r V b₁ b₂ d₁ d₂ hG1 hG2
  unfold IsGenericFlag at hG1 hG2
  obtain ⟨c1, u1, hc1, hj1, hjc1, -, hd1, hup1, hfl1, hai1, hdpos1, hrk1⟩ := hG1
  obtain ⟨c2, u2, hc2, hj2, hjc2, -, hd2, hup2, hfl2, hai2, hdpos2, hrk2⟩ := hG2
  have hU1 : ∀ σ, GF.Uni (u1 σ) := fun σ => ⟨hd1 σ, hup1 σ⟩
  have hU2 : ∀ σ, GF.Uni (u2 σ) := fun σ => ⟨hd2 σ, hup2 σ⟩
  rw [GF.adjoin_all u1 hU1] at hrk1
  rw [GF.adjoin_all u2 hU2] at hrk2
  have hfd1 : FiniteDimensional (IntermediateField.adjoin Ω (Set.range (GF.ent u1))) Ω₁ :=
    Module.finite_of_finrank_pos (by rw [hrk1]; exact hdpos1)
  have hfd2 : FiniteDimensional (IntermediateField.adjoin Ω (Set.range (GF.ent u2))) Ω₂ :=
    Module.finite_of_finrank_pos (by rw [hrk2]; exact hdpos2)
  have hA : ∀ σ, ∃ A : Matrix (Fin (r σ)) (Fin (r σ)) Ω,
      (∀ k, c2 σ k = ∑ l, A l k • c1 σ l) ∧ A.det ≠ 0 := by
    intro σ
    obtain ⟨A, hA⟩ := l_genflag_lemma (c2 σ) (c1 σ)
      (fun k => by rw [(hc1 σ).2, ← (hc2 σ).2]; exact Submodule.subset_span ⟨k, rfl⟩)
    obtain ⟨B, hB⟩ := l_genflag_lemma (c1 σ) (c2 σ)
      (fun k => by rw [(hc2 σ).2, ← (hc1 σ).2]; exact Submodule.subset_span ⟨k, rfl⟩)
    refine ⟨A, hA, fun h0 => ?_⟩
    have hBA := congrArg Matrix.det (l_genflag_lemma_2 (c2 σ) (c1 σ) (hc2 σ).1 hA hB)
    rw [Matrix.det_mul, Matrix.det_one, h0, mul_zero] at hBA
    exact zero_ne_one hBA
  choose A hAc hAdet using hA
  obtain ⟨u2', hU2', hai2', hadj, hfl2'⟩ := GF.change u2 hU2 hai2 hfd2 A hAdet
  have hfd2' : FiniteDimensional (IntermediateField.adjoin Ω (Set.range (GF.ent u2'))) Ω₂ := by
    rw [hadj]; exact hfd2
  have hrk2' : Module.finrank (IntermediateField.adjoin Ω (Set.range (GF.ent u2'))) Ω₂ = d₂ := by
    rw [hadj]; exact hrk2
  obtain ⟨Ω₃, hF3, i₁, i₂, hα, hq, n₁, n₂, hn, hdeg, hr1, hr2⟩ :=
    GF.compositum' (GF.ent u1) (GF.ent u2') hai1 hai2' hfd1 hfd2'
  have hU : ∀ σ, (u1 σ).map i₁ = (u2' σ).map i₂ := by
    intro σ
    ext l k
    simp only [Matrix.map_apply]
    rcases lt_trichotomy k l with hkl | rfl | hlk
    · exact hq ⟨σ, ⟨(l, k), hkl⟩⟩
    · rw [(hU1 σ).1 k, (hU2' σ).1 k, map_one, map_one]
    · rw [(hU1 σ).2 l k hlk, (hU2' σ).2 l k hlk, map_zero, map_zero]
  refine ⟨Ω₃, hF3, i₁, i₂, RingHom.ext hα, ⟨n₁, n₂, hn, ?_, hr1, hr2⟩, ?_⟩
  · rw [← hrk1, ← hrk2', hdeg]
  intro s c m₁ m₂ hc hspan hb1 hb2 i
  obtain ⟨h1, hh1⟩ := l_genflag_lemma c (c1 s)
    (fun k => by rw [(hc1 s).2, ← hspan]; exact Submodule.subset_span ⟨k, rfl⟩)
  obtain ⟨P1, hP1⟩ := l_genflag_lemma (c1 s) c
    (fun k => by rw [hspan, ← (hc1 s).2]; exact Submodule.subset_span ⟨k, rfl⟩)
  have hP2 : ∀ k, c2 s k = ∑ p, (P1 * A s) p k • c p := l_genflag_lemma_0 (c2 s) (c1 s) c (hAc s) hP1
  obtain ⟨h2, hh2⟩ := l_genflag_lemma c (c2 s)
    (fun k => by rw [(hc2 s).2, ← hspan]; exact Submodule.subset_span ⟨k, rfl⟩)
  have e1 : P1 * h1 = 1 := l_genflag_lemma_2 c (c1 s) hc hh1 hP1
  have e2 : (P1 * A s) * h2 = 1 := l_genflag_lemma_2 c (c2 s) hc hh2 hP2
  have f1 := GF.fl_coord j₁ hj1 (hjc1 s) hh1 hb1 (hfl1 s i)
  have f2 := GF.fl_coord j₂ hj2 (hjc2 s) hh2 hb2 (hfl2 s i)
  have g1 : GF.fl m₁ i = GF.fl (P1.map (algebraMap Ω Ω₁) * u1 s) i := by
    have := l_genflag_lemma_5 (P1.map (algebraMap Ω Ω₁)) f1
    rwa [← mul_assoc, ← Matrix.map_mul, e1, Matrix.map_one _ (map_zero _) (map_one _), one_mul] at this
  have g2 : GF.fl m₂ i = GF.fl ((P1 * A s).map (algebraMap Ω Ω₂) * u2 s) i := by
    have := l_genflag_lemma_5 ((P1 * A s).map (algebraMap Ω Ω₂)) f2
    rwa [← mul_assoc, ← Matrix.map_mul, e2, Matrix.map_one _ (map_zero _) (map_one _), one_mul] at this
  change GF.fl (m₁.map i₁) i = GF.fl (m₂.map i₂) i
  rw [l_genflag_lemma_4 i₁ g1, l_genflag_lemma_4 i₂ g2]
  have hPβ : (P1.map (algebraMap Ω Ω₁)).map i₁ = (P1.map (algebraMap Ω Ω₂)).map i₂ := by
    ext l k
    exact hα (P1 l k)
  have L : (P1.map (algebraMap Ω Ω₁) * u1 s).map i₁ =
      (P1.map (algebraMap Ω Ω₂)).map i₂ * (u2' s).map i₂ := by
    rw [Matrix.map_mul, hPβ, hU s]
  have R : ((P1 * A s).map (algebraMap Ω Ω₂) * u2 s).map i₂ =
      (P1.map (algebraMap Ω Ω₂)).map i₂ * (((A s).map (algebraMap Ω Ω₂) * u2 s).map i₂) := by
    simp only [Matrix.map_mul, mul_assoc]
  rw [L, R]
  exact l_genflag_lemma_5 _ (l_genflag_lemma_4 i₂ (hfl2' s i))

end PositivityTheory.UnitarySelfGeneration
