import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.GenericAdmissibleFamilyOfSteps
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.FibreCountOfFirstSteps

noncomputable section

open scoped Classical

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.LatticeGluingRadicals
open scoped ENNReal

section GenG

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {r : ℕ}
  {Λ : Submodule (𝓞 E) S.V} {g : ℕ} {T T' : E} {F : LFlag S r T} {F' : LFlag S r T'}

/- English proof (translation)
Use `P.isPrime` as an intermediate fact. Proceed by induction on `b using Fin.lastCases with`. Consider the case `last => rw [a_frame_last]`. Conclude with `c3eqv_le_loc _ hzm`. Consider the case `cast b`.

Rewrite using `[a_frame_castSucc]`. Take `⟨c, -, hc1, heq⟩` from `hc.1 P`. Establish `h1 : F₁.fl.e b ∈ Submodule.span (𝓞 E) (Set.range fun a => c a • F₁.fl.e a)` using `Submodule.subset_span ⟨b, by simp [hc1 hP b]⟩`. Establish `h2 : F₁.fl.e b ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XLam Λ F₁)`. Rewrite using `[heq]`.

Conclude with `c3eqv_le_loc _ h1`. Conclude with `c3eqv_loc_mono hX h2`.
-/
theorem frame_mem_localization (F₁ : LFlag S r T) (UUm : Submodule (𝓞 E) S.V) (hX : XLam Λ F₁ ≤ UUm) (hzm : F₁.fl.z ∈ UUm)
    (hc : IsFixedConv Λ g F₁) (P : HeightOneSpectrum (𝓞 E)) (hP : (g : 𝓞 E) ∈ P.asIdeal) (b : Fin (r + 1)) :
    frame F₁ b ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal UUm) := by
  have := P.isPrime
  induction b using Fin.lastCases with
  | last => rw [a_frame_last]; exact c3eqv_le_loc _ hzm
  | cast b =>
    rw [a_frame_castSucc]
    obtain ⟨c, -, hc1, heq⟩ := hc.1 P
    have h1 : F₁.fl.e b ∈ Submodule.span (𝓞 E) (Set.range fun a => c a • F₁.fl.e a) :=
      Submodule.subset_span ⟨b, by simp [hc1 hP b]⟩
    have h2 : F₁.fl.e b ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XLam Λ F₁) := by
      rw [heq]; exact c3eqv_le_loc _ h1
    exact c3eqv_loc_mono hX h2

end GenG

section GenG2

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {r : ℕ}
  {Λ : Submodule (𝓞 E) S.V} {g : ℕ} {T T' : E} {F : LFlag S r T} {F' : LFlag S r T'}

/- English proof (translation)
Introduce `w hw`. Apply `BridgeLemma.lframe_local_global` to reduce the goal to its premises. Introduce `P`. Use `P.isPrime` as an intermediate fact. Take `⟨ξ, hξ, hloc⟩` from `hgen`.

Establish `hA : XLam Λ F ≤ UU Λ F F'` using `le_sup_of_le_left (le_sup_of_le_left le_sup_left)`. Establish `hB : F.fl.z ∈ UU Λ F F'`. Rewrite using `[← hz.2]`. Conclude with `(le_sup_of_le_left (le_sup_of_le_left le_sup_right) : Submodule.span (𝓞 E) {F.zt} ≤ UU Λ F F') (Submodule.mem_span_singleton_self _)`. Establish `hC : XLam Λ F' ≤ UU Λ F F'` using `le_sup_of_le_left le_sup_right`.

Establish `hD : F'.fl.z ∈ UU Λ F F'`. Rewrite using `[← hz'.2]`. Conclude with `(le_sup_right : Submodule.span (𝓞 E) {F'.zt} ≤ UU Λ F F') (Submodule.mem_span_singleton_self _)`. Distinguish the cases in `hP : (g : 𝓞 E) ∈ P.asIdeal`. Establish `h1 : w ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Mplus Λ g F F' ξ)`.

Rewrite using `[← (hloc P).1 hP]`. Conclude with `c3eqv_le_loc _ hw`. Take `⟨s, hs, hsw⟩` from `BridgeLemma.lframe_mem_locP.1 h1`. Establish `hle : Mplus Λ g F F' ξ ≤ (Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (UU Λ F F')).comap (LinearMap.lsmul (𝓞 E) S.V (g : 𝓞 E))`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations.

Introduce and unpack `x ((hx | hx) | ⟨b, rfl⟩)`. Conclude with `c3eqv_le_loc _ (Submodule.smul_mem _ _ (hA hx))`. Establish `hx' : x = F.zt` using `hx`. Rewrite using `[hx', hz.2]`. Conclude with `c3eqv_le_loc _ (Submodule.smul_mem _ _ hB)`.

Use `show (g : 𝓞 E) • ((g : E)⁻¹ • (frame F' b - frameAct (frame F) ξ b)) ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (UU Λ F F')`. Establish `hgE : (g : E) ≠ 0` using `by exact_mod_cast hg`. Establish `e : (g : 𝓞 E) • ((g : E)⁻¹ • (frame F' b - frameAct (frame F) ξ b)) = frame F' b - frameAct (frame F) ξ b`. Rewrite using `[← algebraMap_smul E (g : 𝓞 E), map_natCast, smul_smul, mul_inv_cancel₀ hgE, one_smul]`. Rewrite using `[e]`.

Use `Submodule.sub_mem _ (frame_mem_localization F' _ hC hD hc' P hP b) ?_` and prove the remaining obligations. Simplify using `only [frameAct]`. Use `Submodule.sum_mem _ fun a _ => ?_` and prove the remaining obligations. Use `Submodule.smul_mem _ (ξ a b) (frame_mem_localization F _ hA hB hc P hP a)` as an intermediate fact. Rewrite `this` using `[← algebraMap_smul E (ξ a b)]`.

Conclude with `this`. Establish `h2 : (g : 𝓞 E) • (s • w) ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (UU Λ F F')` using `hle hsw`. Take `⟨t, ht, htx⟩` from `BridgeLemma.lframe_mem_locP.1 h2`. Use `⟨t * s, fun h => ?_, ?_⟩` and prove the remaining obligations. Break down `P.isPrime.mem_or_mem h with h | h` into its components or cases.

Conclude with `ht h`. Conclude with `hs h`. Rewrite using `[mul_smul, smul_comm s (g : 𝓞 E) w]`. Conclude with `htx`. Establish `h1 : w ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (UU Λ F F')`.

Rewrite using `[← (hloc P).2 hP]`. Conclude with `c3eqv_le_loc _ hw`. Take `⟨s, hs, hsw⟩` from `BridgeLemma.lframe_mem_locP.1 h1`. Conclude with `⟨s, hs, by rw [smul_comm]; exact Submodule.smul_mem _ _ hsw⟩`.
-/
theorem generic_kills_B (hg : g ≠ 0) (hz : IsLift Λ F) (hz' : IsLift Λ F') (hc : IsFixedConv Λ g F) (hc' : IsFixedConv Λ g F')
    (hgen : IsGeneric Λ g F F') : ∀ w ∈ BLat Λ F F', (g : 𝓞 E) • w ∈ UU Λ F F' := by
  intro w hw
  apply BridgeLemma.lframe_local_global
  intro P
  have := P.isPrime
  obtain ⟨ξ, hξ, hloc⟩ := hgen
  have hA : XLam Λ F ≤ UU Λ F F' := le_sup_of_le_left (le_sup_of_le_left le_sup_left)
  have hB : F.fl.z ∈ UU Λ F F' := by
    rw [← hz.2]
    exact (le_sup_of_le_left (le_sup_of_le_left le_sup_right) : Submodule.span (𝓞 E) {F.zt} ≤ UU Λ F F')
      (Submodule.mem_span_singleton_self _)
  have hC : XLam Λ F' ≤ UU Λ F F' := le_sup_of_le_left le_sup_right
  have hD : F'.fl.z ∈ UU Λ F F' := by
    rw [← hz'.2]
    exact (le_sup_right : Submodule.span (𝓞 E) {F'.zt} ≤ UU Λ F F') (Submodule.mem_span_singleton_self _)
  by_cases hP : (g : 𝓞 E) ∈ P.asIdeal
  · have h1 : w ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Mplus Λ g F F' ξ) := by
      rw [← (hloc P).1 hP]; exact c3eqv_le_loc _ hw
    obtain ⟨s, hs, hsw⟩ := BridgeLemma.lframe_mem_locP.1 h1
    have hle : Mplus Λ g F F' ξ ≤
        (Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (UU Λ F F')).comap (LinearMap.lsmul (𝓞 E) S.V (g : 𝓞 E)) := by
      refine Submodule.span_le.2 ?_
      rintro x ((hx | hx) | ⟨b, rfl⟩)
      · exact c3eqv_le_loc _ (Submodule.smul_mem _ _ (hA hx))
      · have hx' : x = F.zt := hx
        rw [hx', hz.2]
        exact c3eqv_le_loc _ (Submodule.smul_mem _ _ hB)
      · show (g : 𝓞 E) • ((g : E)⁻¹ • (frame F' b - frameAct (frame F) ξ b)) ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (UU Λ F F')
        have hgE : (g : E) ≠ 0 := by exact_mod_cast hg
        have e : (g : 𝓞 E) • ((g : E)⁻¹ • (frame F' b - frameAct (frame F) ξ b)) =
            frame F' b - frameAct (frame F) ξ b := by
          rw [← algebraMap_smul E (g : 𝓞 E), map_natCast, smul_smul, mul_inv_cancel₀ hgE, one_smul]
        rw [e]
        refine Submodule.sub_mem _ (frame_mem_localization F' _ hC hD hc' P hP b) ?_
        simp only [frameAct]
        refine Submodule.sum_mem _ fun a _ => ?_
        have := Submodule.smul_mem _ (ξ a b) (frame_mem_localization F _ hA hB hc P hP a)
        rw [← algebraMap_smul E (ξ a b)] at this
        exact this
    have h2 : (g : 𝓞 E) • (s • w) ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (UU Λ F F') := hle hsw
    obtain ⟨t, ht, htx⟩ := BridgeLemma.lframe_mem_locP.1 h2
    refine ⟨t * s, fun h => ?_, ?_⟩
    · rcases P.isPrime.mem_or_mem h with h | h
      · exact ht h
      · exact hs h
    · rw [mul_smul, smul_comm s (g : 𝓞 E) w]; exact htx
  · have h1 : w ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (UU Λ F F') := by
      rw [← (hloc P).2 hP]; exact c3eqv_le_loc _ hw
    obtain ⟨s, hs, hsw⟩ := BridgeLemma.lframe_mem_locP.1 h1
    exact ⟨s, hs, by rw [smul_comm]; exact Submodule.smul_mem _ _ hsw⟩

/- English proof (translation)
Unfold `gB`. Rewrite using `[eq_bot_iff, Submodule.smul_le]`. Introduce `a ha q _`. Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.1 ha`. Take `⟨w, rfl⟩` from `Submodule.Quotient.mk_surjective _ q`.

Rewrite using `[Submodule.mem_bot, mul_smul, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Conclude with `Submodule.smul_mem _ c (generic_kills_B hg hz hz' hc hc' hgen w.1 w.2)`.
-/
theorem generic_B_eq_bot (hg : g ≠ 0) (hz : IsLift Λ F) (hz' : IsLift Λ F') (hc : IsFixedConv Λ g F)
    (hc' : IsFixedConv Λ g F') (hgen : IsGeneric Λ g F F') : gB Λ g F F' = ⊥ := by
  unfold gB
  rw [eq_bot_iff, Submodule.smul_le]
  intro a ha q _
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [Submodule.mem_bot, mul_smul, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul,
    Submodule.Quotient.mk_eq_zero]
  exact Submodule.smul_mem _ c (generic_kills_B hg hz hz' hc hc' hgen w.1 w.2)

end GenG2

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word)

def GenericIndexOne (C' Cl Cg cb Cu cT CT C0 A : ℝ) : Prop :=
  Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A →
  ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u →
  ∀ Λ : LatV D, IsRowLat D F0 Λ →
  ∀ F' : FlagU D u', IsTermF D Λ (lf D F0) F' → IsGeneric Λ (gS D) (lf D F0) F' →
    La Λ (gS D) (lf D F0) F' ≤ Thp Λ (lf D F0) F'

/- English proof (translation)
Introduce `hH F0 _ _ Λ hΛr F' hT' hgen x hx`. Establish `hSt : Cnt.Stand D u u'` using `hH.2.1`. Establish `hPr` using `Formalism.MainNotions.VanishingOnXAndXPlus.primeHyp_of_stand D u u' hSt`. Establish `hF : FixedHyp D Λ (lf D F0)` using `hΛr.2.1`. Establish `hg : gS D ≠ 0`.

Unfold `gS`. Conclude with `Nat.mul_ne_zero hSt.2.2.2.2.2.2.2.1.ne_zero hSt.2.2.2.2.2.2.2.2.1.ne_zero`. Take `⟨_, _, _, _, φ, hφ, _⟩` from `lemma_one_section D u (Tu D u') Λ (lf D F0) F' hF hPr hT'.1`. Establish `hbot` using `generic_B_eq_bot hg hF.2.2.1 hT'.1.1 hF.2.2.2 hT'.2.1 hgen`. Establish `h0 : φ (Submodule.Quotient.mk ⟨x, hx⟩) = φ 0`.

Apply `Subtype.ext` to reduce the goal to its premises. Establish `hall : ∀ y : gB Λ (gS D) (lf D F0) F', (y : BQ Λ (lf D F0) F') = 0` using `fun y => (Submodule.mem_bot (𝓞 D.host.E)).1 (hbot.le y.2)`. Rewrite using `[hall, hall]`. Establish `h3` using `hφ h0`. Rewrite `h3` using `[Submodule.Quotient.mk_eq_zero]`.

Conclude with `h3`.
-/
theorem generic_index_one (C' Cl Cg cb Cu cT CT C0 A : ℝ) : GenericIndexOne D large₂ u u' C' Cl Cg cb Cu cT CT C0 A := by
  intro hH F0 _ _ Λ hΛr F' hT' hgen x hx
  have hSt : Cnt.Stand D u u' := hH.2.1
  have hPr := Formalism.MainNotions.VanishingOnXAndXPlus.primeHyp_of_stand D u u' hSt
  have hF : FixedHyp D Λ (lf D F0) := hΛr.2.1
  have hg : gS D ≠ 0 := by
    unfold gS
    exact Nat.mul_ne_zero hSt.2.2.2.2.2.2.2.1.ne_zero hSt.2.2.2.2.2.2.2.2.1.ne_zero
  obtain ⟨_, _, _, _, φ, hφ, _⟩ := lemma_one_section D u (Tu D u') Λ (lf D F0) F' hF hPr hT'.1
  have hbot := generic_B_eq_bot hg hF.2.2.1 hT'.1.1 hF.2.2.2 hT'.2.1 hgen
  have h0 : φ (Submodule.Quotient.mk ⟨x, hx⟩) = φ 0 := by
    apply Subtype.ext
    have hall : ∀ y : gB Λ (gS D) (lf D F0) F', (y : BQ Λ (lf D F0) F') = 0 := fun y =>
      (Submodule.mem_bot (𝓞 D.host.E)).1 (hbot.le y.2)
    rw [hall, hall]
  have h3 := hφ h0
  rw [Submodule.Quotient.mk_eq_zero] at h3
  exact h3

end Gen

end Formalism.MainNotions.BridgeLemma₂

end
