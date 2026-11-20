import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh

namespace GlobalTheory.NefGrowth

section SlopeTestRemainingChoices

variable {k : Type} [Field k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)]

/- English proof (translation)
Take `⟨N, ι, _, h⟩` from `hp`. Establish `: LocallyOfFiniteType (strHom k X)` using `h ▸ inferInstance`. Conclude with `LocallyOfFiniteType.isLocallyNoetherian (strHom k X)`.
-/
theorem isLocallyNoetherian_of_isProjOver (hp : IsProjOver (strHom k X)) :
    IsLocallyNoetherian X := by
  obtain ⟨N, ι, _, h⟩ := hp
  have : LocallyOfFiniteType (strHom k X) := h ▸ inferInstance
  exact LocallyOfFiniteType.isLocallyNoetherian (strHom k X)

/- English proof (translation)
Establish `: Subsingleton (coh (twist (structureModule X) L) 0)`. Use `⟨fun x y => ?_⟩` and prove the remaining obligations. Establish `h : ∀ z : coh (twist (structureModule X) L) 0, z = 0` using `fun z => by`. Rewrite using `[← one_smul Γ(X, ⊤) z, Subsingleton.elim (1 : Γ(X, ⊤)) 0, zero_smul]`. Rewrite using `[h x, h y]`.

Conclude with `hdim_eq_zero_of_subsingleton k 0`.
-/
theorem lineBundleGlobalSectionsDim_eq_zero_of_isEmpty [IsEmpty X] (L : LB X) : lbH0 k L = 0 := by
  have : Subsingleton (coh (twist (structureModule X) L) 0) := by
    refine ⟨fun x y => ?_⟩
    have h : ∀ z : coh (twist (structureModule X) L) 0, z = 0 := fun z => by
      rw [← one_smul Γ(X, ⊤) z, Subsingleton.elim (1 : Γ(X, ⊤)) 0, zero_smul]
    rw [h x, h y]
  exact hdim_eq_zero_of_subsingleton k 0

/- English proof (translation)
Take `⟨i⟩` from `nonempty_twist_twist_iso_of_cls_eq (structureModule X) hA hB hN e`. Use `Twist.isQuasicoherent_twist (F := structureModule X) hA` as an intermediate fact. Establish `: Mono (Twist.secHom (twist (structureModule X) A) s)`. Rewrite using `[mono_secHom_iff _ hB, Twist.assPoints_twist hA, ← mono_cutHom_iff _ hB]`. Conclude with `hs`.

Conclude with `LinearMap.finrank_le_finrank_of_injective (cohOn.map_zero_injective_of_mono k ⊤ (Twist.secHom (twist (structureModule X) A) s ≫ i.hom))`.
-/
theorem lineBundleGlobalSectionsDim_le_of_injective_section_mul [IsLocallyNoetherian X] {N A B : LB X} (hN : N.IsLB)
    (hA : A.IsLB) (hB : B.IsLB) (e : cls N hN = cls A hA + cls B hB) (s : B.Sec)
    (hs : Mono (cutHom (structureModule X) hB s))
    (hfin : Module.Finite k (coh (twist (structureModule X) N) 0)) : lbH0 k A ≤ lbH0 k N := by
  obtain ⟨i⟩ := nonempty_twist_twist_iso_of_cls_eq (structureModule X) hA hB hN e
  have := Twist.isQuasicoherent_twist (F := structureModule X) hA
  have : Mono (Twist.secHom (twist (structureModule X) A) s) := by
    rw [mono_secHom_iff _ hB, Twist.assPoints_twist hA, ← mono_cutHom_iff _ hB]
    exact hs
  exact LinearMap.finrank_le_finrank_of_injective
    (cohOn.map_zero_injective_of_mono k ⊤ (Twist.secHom (twist (structureModule X) A) s ≫ i.hom))

end SlopeTestRemainingChoices

open GlobalTheory.Published

/- English proof (translation)
Introduce `hNum F _ Z _ d hp hd L A hL hA`. Break down `isEmpty_or_nonempty Z with hZ | hZ` into its components or cases. Conclude with `⟨0, .of_forall fun m => by rw [lineBundleGlobalSectionsDim_eq_zero_of_isEmpty]; simp⟩`. Use `isLocallyNoetherian_of_isProjOver hp` as an intermediate fact. Choose the witnesses or unpack the hypotheses as in `⟨e, he⟩ : ∃ e : ℕ, topologicalKrullDim Z = e := by`.

Establish `h0 : topologicalKrullDim Z ≠ ⊥` using `topologicalKrullDim_eq_bot_iff.not.2 (not_isEmpty_of_nonempty Z)`. Use `revert h0 hd`. Generalize the expression as in `topologicalKrullDim Z = D`. Introduce `hd h0`. Proceed by induction on `D using WithBot.recBotCoe with`.

Consider the case `bot => exact absurd rfl h0`. Consider the case `coe D`. Proceed by induction on `D using ENat.recTopCoe with`. Consider the case `top`. Establish `h' : (⊤ : ℕ∞) ≤ (d : ℕ∞)` using `by exact_mod_cast hd`.

Conclude with `absurd (top_le_iff.1 h') (ENat.coe_ne_top d)`. Consider the case `coe n => exact ⟨n, rfl⟩`. Establish `hed : e ≤ d`. Rewrite `hd` using `[he]`. Conclude with `hd` after adjusting the coercions.

Establish `hLA : IsNef F (tens L A)` using `hL.tens hA.isNef hA`. Establish `ht` using `hNum.2.2.tendsto hp he hLA`. Use `set c : ℝ := (topSelfIntersection F (tens L A) e : ℝ) / e.factorial`. Establish `hb` using `ht.eventually (gt_mem_nhds (lt_add_one c))`. Establish `hcut : ∀ᶠ m : ℕ in atTop, ∃ t : (lbPow A (m - 1)).Sec, Mono (cutHom (structureModule Z) (isLB_lbPow hA.isLB (m - 1)) t)` using `(tendsto_sub_atTop_nat 1).eventually (hA.eventually_exists_mono_cutHom_pow (structureModule Z))`.

Use `⟨|c| + 1, ?_⟩` and prove the remaining obligations. Use `filter_upwards [hcut, hb, eventually_ge_atTop 1] with m ⟨t, hts⟩ hm hm1`. Establish `hcls : cls _ (isLB_lbPow (isLB_tens hL.isLB hA.isLB) m) = cls _ (isLB_tens (isLB_lbPow hL.isLB m) hA.isLB) + cls _ (isLB_lbPow hA.isLB (m - 1))`. Rewrite using `[cls_lbPow (isLB_tens hL.isLB hA.isLB), cls_tens hL.isLB hA.isLB, cls_tens (isLB_lbPow hL.isLB m) hA.isLB, cls_lbPow hL.isLB, cls_lbPow hA.isLB]`. Take `⟨n, rfl⟩ : ∃ n, m = n + 1` from `⟨m - 1, by omega⟩`.

Simplify using `only [Nat.add_sub_cancel, add_smul, one_smul, smul_add]`. Normalize the expressions using the abelian group laws. Establish `h1` using `lineBundleGlobalSectionsDim_le_of_injective_section_mul (k := F) (isLB_lbPow (isLB_tens hL.isLB hA.isLB) m) (isLB_tens (isLB_lbPow hL.isLB m) hA.isLB) (isLB_lbPow hA.isLB (m - 1)) hcls t hts (finite_coh_zero_twist_of_isProjOver (algebraMap_eq_strHom F Z) hp (isLB_lbPow (isLB_tens …`. Establish `hmpos : (0 : ℝ) < (m : ℝ) ^ e` using `by positivity`. Establish `h2 : (lbH0 F (lbPow (tens L A) m) : ℝ) ≤ (c + 1) * (m : ℝ) ^ e` using `((div_lt_iff₀ hmpos).1 hm).le`.

Establish `h3 : (m : ℝ) ^ e ≤ (m : ℝ) ^ d` using `pow_le_pow_right₀ (by exact_mod_cast hm1) hed`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem lineBundleGlobalSectionsDim_nefPow_tensor_ample_isBigO : GlobalTheory.Published.NefNumerics → ∀ (F : Type) [Field F] (Z : Scheme.{0})
    [Algebra F Γ(Z, ⊤)] (d : ℕ), IsProjOver (strHom F Z) → topologicalKrullDim Z ≤ d →
    ∀ L A : LB Z, IsNef F L → IsAmpleLB A → ∃ C : ℝ, ∀ᶠ m : ℕ in atTop,
      (lbH0 F (tens (lbPow L m) A) : ℝ) ≤ C * (m : ℝ) ^ d := by
  intro hNum F _ Z _ d hp hd L A hL hA
  rcases isEmpty_or_nonempty Z with hZ | hZ
  · exact ⟨0, .of_forall fun m => by rw [lineBundleGlobalSectionsDim_eq_zero_of_isEmpty]; simp⟩
  have := isLocallyNoetherian_of_isProjOver hp
  obtain ⟨e, he⟩ : ∃ e : ℕ, topologicalKrullDim Z = e := by
    have h0 : topologicalKrullDim Z ≠ ⊥ := topologicalKrullDim_eq_bot_iff.not.2 (not_isEmpty_of_nonempty Z)
    revert h0 hd
    generalize topologicalKrullDim Z = D
    intro hd h0
    induction D using WithBot.recBotCoe with
    | bot => exact absurd rfl h0
    | coe D =>
      induction D using ENat.recTopCoe with
      | top =>
        have h' : (⊤ : ℕ∞) ≤ (d : ℕ∞) := by exact_mod_cast hd
        exact absurd (top_le_iff.1 h') (ENat.coe_ne_top d)
      | coe n => exact ⟨n, rfl⟩
  have hed : e ≤ d := by
    rw [he] at hd
    exact_mod_cast hd
  have hLA : IsNef F (tens L A) := hL.tens hA.isNef hA
  have ht := hNum.2.2.tendsto hp he hLA
  set c : ℝ := (topSelfIntersection F (tens L A) e : ℝ) / e.factorial
  have hb := ht.eventually (gt_mem_nhds (lt_add_one c))
  have hcut : ∀ᶠ m : ℕ in atTop,
      ∃ t : (lbPow A (m - 1)).Sec, Mono (cutHom (structureModule Z) (isLB_lbPow hA.isLB (m - 1)) t) :=
    (tendsto_sub_atTop_nat 1).eventually (hA.eventually_exists_mono_cutHom_pow (structureModule Z))
  refine ⟨|c| + 1, ?_⟩
  filter_upwards [hcut, hb, eventually_ge_atTop 1] with m ⟨t, hts⟩ hm hm1
  have hcls : cls _ (isLB_lbPow (isLB_tens hL.isLB hA.isLB) m) =
      cls _ (isLB_tens (isLB_lbPow hL.isLB m) hA.isLB) + cls _ (isLB_lbPow hA.isLB (m - 1)) := by
    rw [cls_lbPow (isLB_tens hL.isLB hA.isLB), cls_tens hL.isLB hA.isLB,
      cls_tens (isLB_lbPow hL.isLB m) hA.isLB, cls_lbPow hL.isLB, cls_lbPow hA.isLB]
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    simp only [Nat.add_sub_cancel, add_smul, one_smul, smul_add]
    abel
  have h1 := lineBundleGlobalSectionsDim_le_of_injective_section_mul (k := F) (isLB_lbPow (isLB_tens hL.isLB hA.isLB) m)
    (isLB_tens (isLB_lbPow hL.isLB m) hA.isLB) (isLB_lbPow hA.isLB (m - 1)) hcls t hts
    (finite_coh_zero_twist_of_isProjOver (algebraMap_eq_strHom F Z) hp
      (isLB_lbPow (isLB_tens hL.isLB hA.isLB) m))
  have hmpos : (0 : ℝ) < (m : ℝ) ^ e := by positivity
  have h2 : (lbH0 F (lbPow (tens L A) m) : ℝ) ≤ (c + 1) * (m : ℝ) ^ e :=
    ((div_lt_iff₀ hmpos).1 hm).le
  have h3 : (m : ℝ) ^ e ≤ (m : ℝ) ^ d := pow_le_pow_right₀ (by exact_mod_cast hm1) hed
  calc (lbH0 F (tens (lbPow L m) A) : ℝ) ≤ lbH0 F (lbPow (tens L A) m) := by exact_mod_cast h1
    _ ≤ (c + 1) * (m : ℝ) ^ e := h2
    _ ≤ (|c| + 1) * (m : ℝ) ^ e := by gcongr; exact le_abs_self c
    _ ≤ (|c| + 1) * (m : ℝ) ^ d := by gcongr

end GlobalTheory.NefGrowth
