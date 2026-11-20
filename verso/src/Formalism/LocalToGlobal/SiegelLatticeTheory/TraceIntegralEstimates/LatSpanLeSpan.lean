import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.FrameTop
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SplitRow
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdentityCellTrace.TraceOneHolds
import Formalism.SharpRestriction.CuspSpanNormBounds.CntPartners

noncomputable section

open scoped Classical

namespace Formalism.L2.S.Pv.ClassCounting

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef PI.TermsAtPtFiniteW
  PI.TermsAtPtFiniteW.HeisW PI.TermsAtPtFiniteW.LeviW Formalism.L2.SG.Saturated

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

/- English proof (translation)
Introduce `x hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨a, rfl⟩` from `hz`. Conclude with `h a`.

Consider the case `zero => simp`. Consider the case `add x x' _ _ hx hx' => simp [hx, hx']`. Consider the case `smul c x _ hx => simp [hx]`.
-/
theorem orth_span (v : Fin r → S.V) {y : S.V} (h : ∀ a, S.hT (v a) y = 0) :
    ∀ x ∈ Submodule.span E (Set.range v), S.hT x y = 0 := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨a, rfl⟩ := hz
    exact h a
  | zero => simp
  | add x x' _ _ hx hx' => simp [hx, hx']
  | smul c x _ hx => simp [hx]

/- English proof (translation)
Unfold `latSpan`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `y ⟨a, x, -, rfl⟩`. Conclude with `Submodule.smul_mem _ x (Submodule.subset_span ⟨a, rfl⟩)`.
-/
theorem latSpan_le_span (aa : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (v : Fin r → S.V) :
    latSpan aa v ≤ (Submodule.span E (Set.range v)).restrictScalars (𝓞 E) := by
  unfold latSpan
  rw [Submodule.span_le]
  rintro y ⟨a, x, -, rfl⟩
  exact Submodule.smul_mem _ x (Submodule.subset_span ⟨a, rfl⟩)

/- English proof (translation)
Take `⟨c, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun E).mp hx`. Use `Finset.sum_congr rfl (fun a _ => ?_)` and prove the remaining obligations. Use `congr 1`. Rewrite using `[map_sum]`. Simplify using `[hfe]`.
-/
theorem coef_of_span (e f : Fin r → S.V) (hfe : ∀ a b, S.hT (f a) (e b) = if a = b then 1 else 0) {x : S.V}
    (hx : x ∈ Submodule.span E (Set.range e)) : x = ∑ a, S.hT (f a) x • e a := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).mp hx
  refine Finset.sum_congr rfl (fun a _ => ?_)
  congr 1
  rw [map_sum]
  simp [hfe]

variable (Λ : Submodule (𝓞 E) S.V) (aa : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (e f : Fin r → S.V)
  (L : Submodule (𝓞 E) S.V)

/- English proof (translation)
Establish `horth2 : ∀ (u : S.V) (w : Fin r → S.V), (∀ b, S.hT u (w b) = 0) → ∀ y ∈ Submodule.span E (Set.range w), S.hT u y = 0`. Introduce `u w hw y hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨b, rfl⟩` from `hz`.

Conclude with `hw b`. Consider the case `zero => simp`. Consider the case `add x x' _ _ hx hx' => simp [hx, hx']`. Consider the case `smul c x _ hx => simp [hx]`. Establish `hfe : ∀ a b, S.hT (f a) (e b) = if a = b then 1 else 0`.

Introduce `a b`. Rewrite using `[← S.herm.eq (e b) (f a), hef b a]`. Distinguish the cases in `h : a = b`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[h, Ne.symm h]`. Establish `hxd : x ∈ Formalism.HermitianLatticesTheory.dual S.hT Λ`. Unfold `Formalism.HermitianLatticesTheory.dual Formalism.E.hdual`. Simplify using `only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply, Submodule.mem_one]`. Introduce `y hy`.

Rewrite `hy` using `[hΛ]`. Take `⟨y12, hy12, y2, hy2, rfl⟩` from `Submodule.mem_sup.mp hy`. Take `⟨y1, hy1, yL, hyL, rfl⟩` from `Submodule.mem_sup.mp hy12`. Establish `h1 : S.hT y1 x = 0` using `orth_span e hxe y1 (latSpan_le_span aa e hy1)`. Establish `h2 : S.hT y2 x = 0` using `orth_span f hxf y2 (latSpan_le_span _ f hy2)`.

Take `⟨o, ho⟩` from `hxL yL hyL`. Use `⟨o, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, h1, h2, ← ho]`. Simplify using the standard rewrite rules. Establish `hxΛ : x ∈ Λ`.

Unfold `Formalism.HermitianLatticesTheory.IsUnimodular at hU`. Rewrite `hxd` using `[hU]`. Conclude with `hxd`. Rewrite `hxΛ` using `[hΛ]`. Take `⟨x12, hx12, x2, hx2, hxeq⟩` from `Submodule.mem_sup.mp hxΛ`.

Take `⟨x1, hx1, xL, hxL', rfl⟩` from `Submodule.mem_sup.mp hx12`. Establish `hx1' : x1 ∈ Submodule.span E (Set.range e)` using `latSpan_le_span aa e hx1`. Establish `hx2' : x2 ∈ Submodule.span E (Set.range f)` using `latSpan_le_span _ f hx2`. Establish `hf1 : ∀ a, S.hT (f a) x1 = 0`. Introduce `a`.

Establish `h` using `hxf a`. Rewrite `h` using `[← hxeq, map_add, map_add, (hL xL hxL' a).2, horth2 (f a) f (hff a) x2 hx2']`. Simplify using `using h`. Establish `he2 : ∀ a, S.hT (e a) x2 = 0`. Introduce `a`.

Establish `h` using `hxe a`. Rewrite `h` using `[← hxeq, map_add, map_add, (hL xL hxL' a).1, horth2 (e a) e (hee a) x1 hx1']`. Simplify using `using h`. Establish `h10 : x1 = 0`. Rewrite using `[coef_of_span e f hfe hx1']`.

Simplify using `[hf1]`. Establish `h20 : x2 = 0`. Rewrite using `[coef_of_span f e hef hx2']`. Simplify using `[he2]`. Rewrite using `[← hxeq, h10, h20, zero_add, add_zero]`.

Conclude with `hxL'`.
-/
theorem mem_L_of_dual (hU : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ)
    (hΛ : Λ = latSpan aa e ⊔ L ⊔ latSpan (fun a => (aa a)⁻¹) f)
    (hee : ∀ a b, S.hT (e a) (e b) = 0) (hff : ∀ a b, S.hT (f a) (f b) = 0)
    (hef : ∀ a b, S.hT (e a) (f b) = if a = b then 1 else 0)
    (hL : ∀ x ∈ L, ∀ a, S.hT (e a) x = 0 ∧ S.hT (f a) x = 0)
    {x : S.V} (hxe : ∀ a, S.hT (e a) x = 0) (hxf : ∀ a, S.hT (f a) x = 0)
    (hxL : ∀ y ∈ L, ∃ o : 𝓞 E, (o : E) = S.hT y x) : x ∈ L := by
  have horth2 : ∀ (u : S.V) (w : Fin r → S.V), (∀ b, S.hT u (w b) = 0) →
      ∀ y ∈ Submodule.span E (Set.range w), S.hT u y = 0 := by
    intro u w hw y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨b, rfl⟩ := hz
      exact hw b
    | zero => simp
    | add x x' _ _ hx hx' => simp [hx, hx']
    | smul c x _ hx => simp [hx]
  have hfe : ∀ a b, S.hT (f a) (e b) = if a = b then 1 else 0 := by
    intro a b
    rw [← S.herm.eq (e b) (f a), hef b a]
    by_cases h : a = b
    · subst h; simp
    · simp [h, Ne.symm h]
  have hxd : x ∈ Formalism.HermitianLatticesTheory.dual S.hT Λ := by
    unfold Formalism.HermitianLatticesTheory.dual Formalism.E.hdual
    simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply, Submodule.mem_one]
    intro y hy
    rw [hΛ] at hy
    obtain ⟨y12, hy12, y2, hy2, rfl⟩ := Submodule.mem_sup.mp hy
    obtain ⟨y1, hy1, yL, hyL, rfl⟩ := Submodule.mem_sup.mp hy12
    have h1 : S.hT y1 x = 0 := orth_span e hxe y1 (latSpan_le_span aa e hy1)
    have h2 : S.hT y2 x = 0 := orth_span f hxf y2 (latSpan_le_span _ f hy2)
    obtain ⟨o, ho⟩ := hxL yL hyL
    refine ⟨o, ?_⟩
    rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, h1, h2, ← ho]
    simp
  have hxΛ : x ∈ Λ := by
    unfold Formalism.HermitianLatticesTheory.IsUnimodular at hU
    rw [hU] at hxd
    exact hxd
  rw [hΛ] at hxΛ
  obtain ⟨x12, hx12, x2, hx2, hxeq⟩ := Submodule.mem_sup.mp hxΛ
  obtain ⟨x1, hx1, xL, hxL', rfl⟩ := Submodule.mem_sup.mp hx12
  have hx1' : x1 ∈ Submodule.span E (Set.range e) := latSpan_le_span aa e hx1
  have hx2' : x2 ∈ Submodule.span E (Set.range f) := latSpan_le_span _ f hx2
  have hf1 : ∀ a, S.hT (f a) x1 = 0 := by
    intro a
    have h := hxf a
    rw [← hxeq, map_add, map_add, (hL xL hxL' a).2, horth2 (f a) f (hff a) x2 hx2'] at h
    simpa using h
  have he2 : ∀ a, S.hT (e a) x2 = 0 := by
    intro a
    have h := hxe a
    rw [← hxeq, map_add, map_add, (hL xL hxL' a).1, horth2 (e a) e (hee a) x1 hx1'] at h
    simpa using h
  have h10 : x1 = 0 := by
    rw [coef_of_span e f hfe hx1']
    simp [hf1]
  have h20 : x2 = 0 := by
    rw [coef_of_span f e hef hx2']
    simp [he2]
  rw [← hxeq, h10, h20, zero_add, add_zero]
  exact hxL'

/- English proof (translation)
Establish `hstar : ∀ o : 𝓞 E, ∃ o' : 𝓞 E, (o' : E) = star (o : E)`. Introduce `o`. Conclude with `⟨⟨star (o : E), (o.2).map (starRingEnd E).toIntAlgHom⟩, rfl⟩`. Establish `hsmul : ∀ (c : 𝓞 E) (y : S.V), c • y = (c : E) • y` using `fun c y => (algebraMap_smul E c y).symm`. Set `J : Ideal (𝓞 E)` to `{ carrier := {o | ∃ σ ∈ L, (o : E) = S.hT σ z} add_mem' := by`.

Introduce and unpack `a b ⟨σ, hσ, ha⟩ ⟨τ, hτ, hb⟩`. Conclude with `⟨σ + τ, L.add_mem hσ hτ, by simp [ha, hb]⟩`. Use the proof step `zero_mem' := ⟨0, L.zero_mem, by simp⟩`. Use the proof step `smul_mem' := by`. Introduce and unpack `c a ⟨σ, hσ, ha⟩`.

Take `⟨c', hc'⟩` from `hstar c`. Use `⟨c' • σ, L.smul_mem c' hσ, ?_⟩` and prove the remaining obligations. Rewrite using `[hsmul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, ← ha, hc']`. Simplify using `[starRingEnd_apply] }`. Take `⟨o0, ho0⟩` from `hint z hzL z hzL`.

Establish `hJ : J ≠ ⊥`. Introduce `h`. Establish `hmem : o0 ∈ J` using `⟨z, hzL, ho0⟩`. Rewrite `hmem` using `[h, Ideal.mem_bot]`. Rewrite `ho0` using `[hmem]`.

Conclude with `hzz (by simpa using ho0.symm)`. Establish `hI : (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≠ 0` using `FractionalIdeal.coeIdeal_ne_zero.mpr hJ`. Establish `hinv : (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)⁻¹ ≤ 1`. Introduce `x hx`. Rewrite `hx` using `[FractionalIdeal.mem_inv_iff hI]`.

Establish `hxz : x • z ∈ L`. Apply `hdual` to reduce the goal to its premises. Introduce `y hy`. Take `⟨o, ho⟩` from `hint y hy z hzL`. Establish `hoJ : (o : E) ∈ (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)` using `(FractionalIdeal.mem_coeIdeal _).mpr ⟨o, ⟨y, hy, ho⟩, rfl⟩`.

Take `⟨o', ho'⟩` from `(FractionalIdeal.mem_one_iff _).mp (hx _ hoJ)`. Conclude with `⟨o', by rw [map_smul, smul_eq_mul, ← ho, ← ho']⟩`. Take `⟨o, ho⟩` from `hprim x hxz`. Conclude with `(FractionalIdeal.mem_one_iff _).mpr ⟨o, ho⟩`. Establish `h1 : (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≤ J`.

Combine the equalities or inequalities in the displayed calculation. Establish `h1J : (1 : E) ∈ (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)` using `h1 (FractionalIdeal.one_mem_one _)`. Take `⟨j, ⟨σ, hσ, hj⟩, hj1⟩` from `(FractionalIdeal.mem_coeIdeal _).mp h1J`. Use `⟨σ, hσ, ?_⟩` and prove the remaining obligations. Rewrite using `[← hj]`.

Conclude with `hj1`.
-/
theorem exists_partner (z : S.V) (hzL : z ∈ L) (hzz : S.hT z z ≠ 0)
    (hint : ∀ x ∈ L, ∀ y ∈ L, ∃ o : 𝓞 E, (o : E) = S.hT x y)
    (hdual : ∀ c : E, (∀ y ∈ L, ∃ o : 𝓞 E, (o : E) = S.hT y (c • z)) → c • z ∈ L)
    (hprim : ∀ c : E, c • z ∈ L → ∃ o : 𝓞 E, (o : E) = c) :
    ∃ σ ∈ L, S.hT σ z = 1 := by
  classical
  have hstar : ∀ o : 𝓞 E, ∃ o' : 𝓞 E, (o' : E) = star (o : E) := by
    intro o
    exact ⟨⟨star (o : E), (o.2).map (starRingEnd E).toIntAlgHom⟩, rfl⟩
  have hsmul : ∀ (c : 𝓞 E) (y : S.V), c • y = (c : E) • y := fun c y => (algebraMap_smul E c y).symm
  let J : Ideal (𝓞 E) :=
    { carrier := {o | ∃ σ ∈ L, (o : E) = S.hT σ z}
      add_mem' := by
        rintro a b ⟨σ, hσ, ha⟩ ⟨τ, hτ, hb⟩
        exact ⟨σ + τ, L.add_mem hσ hτ, by simp [ha, hb]⟩
      zero_mem' := ⟨0, L.zero_mem, by simp⟩
      smul_mem' := by
        rintro c a ⟨σ, hσ, ha⟩
        obtain ⟨c', hc'⟩ := hstar c
        refine ⟨c' • σ, L.smul_mem c' hσ, ?_⟩
        rw [hsmul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, ← ha, hc']
        simp [starRingEnd_apply] }
  obtain ⟨o0, ho0⟩ := hint z hzL z hzL
  have hJ : J ≠ ⊥ := by
    intro h
    have hmem : o0 ∈ J := ⟨z, hzL, ho0⟩
    rw [h, Ideal.mem_bot] at hmem
    rw [hmem] at ho0
    exact hzz (by simpa using ho0.symm)
  have hI : (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr hJ
  have hinv : (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)⁻¹ ≤ 1 := by
    intro x hx
    rw [FractionalIdeal.mem_inv_iff hI] at hx
    have hxz : x • z ∈ L := by
      apply hdual
      intro y hy
      obtain ⟨o, ho⟩ := hint y hy z hzL
      have hoJ : (o : E) ∈ (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) :=
        (FractionalIdeal.mem_coeIdeal _).mpr ⟨o, ⟨y, hy, ho⟩, rfl⟩
      obtain ⟨o', ho'⟩ := (FractionalIdeal.mem_one_iff _).mp (hx _ hoJ)
      exact ⟨o', by rw [map_smul, smul_eq_mul, ← ho, ← ho']⟩
    obtain ⟨o, ho⟩ := hprim x hxz
    exact (FractionalIdeal.mem_one_iff _).mpr ⟨o, ho⟩
  have h1 : (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≤ J := by
    calc (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) = J * (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)⁻¹ :=
          (mul_inv_cancel₀ hI).symm
      _ ≤ J * 1 := by gcongr
      _ = J := mul_one _
  have h1J : (1 : E) ∈ (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) := h1 (FractionalIdeal.one_mem_one _)
  obtain ⟨j, ⟨σ, hσ, hj⟩, hj1⟩ := (FractionalIdeal.mem_coeIdeal _).mp h1J
  refine ⟨σ, hσ, ?_⟩
  rw [← hj]
  exact hj1

end Gen

end Formalism.L2.S.Pv.ClassCounting

end
