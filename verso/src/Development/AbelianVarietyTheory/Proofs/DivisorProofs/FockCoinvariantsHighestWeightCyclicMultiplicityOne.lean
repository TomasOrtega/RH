import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ActAtApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNontrivialLiftModule
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsJointShapeGenerated
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoinvTopOrRat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockOperatorsLieRepresentationCommute
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPolynomialsLocallyFiniteRationalWeights
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHighestWeightLiftModStableSubspaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActionIsLocallyBlockUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightLeSpanSupFockCoinvariantsStatement

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

noncomputable section

namespace GlobalTheory.HoweR.Cyc

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coinv_eq_rel (P Q R S : ℕ) (x : ℚ) : coinv P Q R S (x : ℂ) = GlobalTheory.FockQuot.rel P Q R S x := rfl

/- English proof (translation)
Assemble the required witnesses or components as `⟨(fock_lie_and_commute P Q R S).2.2.1, fun v => ((GlobalTheory.FockPolGK.pol_locFin_weights P Q R S).2 v).2, GlobalTheory.T.fockAction_isLocallyBlockUnitary P Q R S⟩`.
-/
theorem fockAct2_good (P Q R S : ℕ) : Good (fockAct2 P Q R S) :=
  ⟨(fock_lie_and_commute P Q R S).2.2.1, fun v => ((GlobalTheory.FockPolGK.pol_locFin_weights P Q R S).2 v).2,
    GlobalTheory.T.fockAction_isLocallyBlockUnitary P Q R S⟩

/- English proof (translation)
Establish `h` using `GlobalTheory.FockQuot.fockTraceCharacterRelations_le_comap_secondAction P Q R S x 0 Y hy`. Rewrite `h` using `[Submodule.mem_comap, GlobalTheory.FockQuot.fockSecondActionTraceShift_apply]`. Simplify using `using h`.
-/
theorem rel_stab (P Q R S : ℕ) (x : ℚ) (Y : Mat R S) (y : Pol P Q R S) (hy : y ∈ GlobalTheory.FockQuot.rel P Q R S x) :
    fockAct2 P Q R S Y y ∈ GlobalTheory.FockQuot.rel P Q R S x := by
  have h := GlobalTheory.FockQuot.fockTraceCharacterRelations_le_comap_secondAction P Q R S x 0 Y hy
  rw [Submodule.mem_comap, GlobalTheory.FockQuot.fockSecondActionTraceShift_apply] at h
  simpa using h

/- English proof (translation)
Rewrite using `[GlobalTheory.FockQuot.actQ_mk, GlobalTheory.FockQuot.fockSecondActionTraceShift_apply]`. Simplify using the standard rewrite rules.
-/
theorem actQ_zero_mk (P Q R S : ℕ) (x : ℚ) (Y : Mat R S) (f : Pol P Q R S) :
    GlobalTheory.FockQuot.actQ P Q R S x 0 Y (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (fockAct2 P Q R S Y f) := by
  rw [GlobalTheory.FockQuot.actQ_mk, GlobalTheory.FockQuot.fockSecondActionTraceShift_apply]; simp

/- English proof (translation)
Unfold `genSub at hy ⊢`. Rewrite `hy`, the goal using `[Submodule.mem_sInf]`. Introduce `N hN`. Conclude with `hN.2 Z y (hy N hN)`.
-/
theorem genSub_stable {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V)
    (T : Set V) (Z : Mat p q) (y : V) (hy : y ∈ genSub act T) : act Z y ∈ genSub act T := by
  unfold genSub at hy ⊢
  rw [Submodule.mem_sInf] at hy ⊢
  intro N hN
  exact hN.2 Z y (hy N hN)

/- English proof (translation)
Unfold `genSub`. Rewrite using `[Submodule.mem_sInf]`. Introduce `N hN`. Conclude with `hN.1 rfl`.
-/
theorem mem_genSub_self {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V)
    (v : V) : v ∈ genSub act {v} := by
  unfold genSub
  rw [Submodule.mem_sInf]
  intro N hN
  exact hN.1 rfl

/- English proof (translation)
Use `set C := GlobalTheory.FockQuot.rel P Q R S x with hC`. Establish `hnt : Nontrivial (GlobalTheory.FockQuot.gkQ P Q R S x 0).V` using `by show Nontrivial (Pol P Q R S ⧸ C)`. Conclude with `Submodule.Quotient.nontrivial_iff.2 hne`. Establish `hlift : IsLift x 0 (GlobalTheory.FockQuot.gkQ P Q R S x 0) C.mkQ`. Use `⟨Submodule.mkQ_surjective _, fun X f => GlobalTheory.FockQuot.mk_fockFirstAction_eq_trace_smul P Q R S x X f, fun Y f => ?_⟩` and prove the remaining obligations.

Use `show GlobalTheory.FockQuot.actQ P Q R S x 0 Y (Submodule.Quotient.mk f) = _`. Rewrite using `[GlobalTheory.FockQuot.actQ_mk, GlobalTheory.FockQuot.fockSecondActionTraceShift_apply]`. Both sides reduce to the same expression. Take `⟨μ', hJ, w, ⟨hw0, hwhw⟩, hgen⟩` from `GlobalTheory.RealLift.GenLift.genBy_of_isLift P Q R S x 0 _ _ hlift hnt`. Express the relevant statement in the definitionally equal form `w ∈ hwSub (GlobalTheory.FockQuot.actQ P Q R S x 0) _ at hwhw`.

Express the relevant statement in the definitionally equal form `genSub (GlobalTheory.FockQuot.actQ P Q R S x 0) {w} = ⊤ at hgen`. Take `⟨f₁, rfl⟩` from `Submodule.Quotient.mk_surjective C w`. Express the relevant statement in the definitionally equal form `(Submodule.Quotient.mk f₁ : Pol P Q R S ⧸ C) ≠ 0 at hw0`. Establish `hwhw' : (Submodule.Quotient.mk f₁ : Pol P Q R S ⧸ C) ∈ hwSub (GlobalTheory.FockQuot.actQ P Q R S x 0) (fun c => μ' c + 0)` using `hwhw`. Take `⟨hwt0, hpos0⟩` from `Submodule.mem_inf.1 hwhw'`.

Establish `hwt : ∀ c, GlobalTheory.FockQuot.actQ P Q R S x 0 (Eab c c) (Submodule.Quotient.mk f₁ : Pol P Q R S ⧸ C) = (((μ' c + 0 : ℚ)) : ℂ) • (Submodule.Quotient.mk f₁ : Pol P Q R S ⧸ C)` using `fun c => by`. Unfold `wtSub at hwt0`. Establish `h` using `(Submodule.mem_iInf _).1 hwt0 c`. Rewrite `h` using `[LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]`. Simplify using `using h`.

Establish `hpos : ∀ c d, posC c d → GlobalTheory.FockQuot.actQ P Q R S x 0 (Eab c d) (Submodule.Quotient.mk f₁ : Pol P Q R S ⧸ C) = 0` using `fun c d hcd => by`. Establish `h` using `(Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hpos0 c) d) hcd`. Conclude with `h`. Establish `hKC : KStable (fockAct2 P Q R S) C` using `fun X _ y hy => rel_stab P Q R S x X y hy`. Establish `hKT : KStable (fockAct2 P Q R S) (⊤ : Submodule ℂ (Pol P Q R S))` using `fun _ _ _ _ => Submodule.mem_top`.

Establish `h1 : ∀ c, fockAct2 P Q R S (Eab c c) f₁ - ((μ' c : ℚ) : ℂ) • f₁ ∈ C`. Introduce `c`. Rewrite using `[← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul, ← actQ_zero_mk, hwt c]`. Simplify using the standard rewrite rules. Establish `h2 : ∀ c d, posC c d → fockAct2 P Q R S (Eab c d) f₁ ∈ C`.

Introduce `c d hcd`. Rewrite using `[← Submodule.Quotient.mk_eq_zero, ← actQ_zero_mk]`. Conclude with `hpos c d hcd`. Take `⟨v, -, hv, hfv⟩` from `GlobalTheory.T.exists_highestWeight_lift_mod_stable_subspace R S (Pol P Q R S) (fockAct2 P Q R S) (fockAct2_good P Q R S) C ⊤ hKC hKT μ' f₁ Submodule.mem_top h1 h2`. Establish `hmk : (Submodule.Quotient.mk v : Pol P Q R S ⧸ C) = Submodule.Quotient.mk f₁` using `((Submodule.Quotient.eq C).2 hfv).symm`.

Use `⟨μ', v, hv, ?_, ?_⟩` and prove the remaining obligations. Use `set N := genSub (fockAct2 P Q R S) {v} ⊔ C with hN`. Establish `hNst : ∀ Z, ∀ y ∈ N, fockAct2 P Q R S Z y ∈ N`. Introduce `Z y hy`. Take `⟨a, ha, b, hb, rfl⟩` from `Submodule.mem_sup.1 hy`.

Rewrite using `[map_add]`. Conclude with `N.add_mem (Submodule.mem_sup_left (genSub_stable _ _ Z a ha)) (Submodule.mem_sup_right (rel_stab P Q R S x Z b hb))`. Establish `hle : genSub (GlobalTheory.FockQuot.actQ P Q R S x 0) {Submodule.Quotient.mk f₁} ≤ N.map C.mkQ`. Use `sInf_le ⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Set.singleton_subset_iff, ← hmk]`.

Conclude with `⟨v, Submodule.mem_sup_left (mem_genSub_self _ v), rfl⟩`. Introduce and unpack `Z _ ⟨n, hn, rfl⟩`. Use `⟨fockAct2 P Q R S Z n, hNst Z n hn, ?_⟩` and prove the remaining obligations. Simplify using `only [Submodule.mkQ_apply]`. Rewrite using `[actQ_zero_mk]`.

Establish `hle2 : N.map C.mkQ = ⊤` using `top_le_iff.1 (le_trans (le_of_eq hgen.symm) hle)`. Rewrite using `[eq_top_iff]`. Introduce `f _`. Establish `hf : Submodule.Quotient.mk f ∈ N.map C.mkQ` using `by rw [hle2]; exact Submodule.mem_top`. Take `⟨n, hn, hnf⟩` from `hf`.

Establish `hd : n - f ∈ C` using `(Submodule.Quotient.eq C).1 hnf`. Establish `: f = n - (n - f)` using `by abel`. Rewrite using `[this]`. Conclude with `N.sub_mem hn (Submodule.mem_sup_right hd)`. Take `⟨f₀, hf₀⟩` from `GlobalTheory.T.highestWeight_le_span_sup_fockCoinvariants P Q R S x μ' hJ`.

Rewrite `hf₀` using `[coinv_eq_rel]`. Take `⟨y, hy, c, hc, hyc⟩` from `Submodule.mem_sup.1 (hf₀ hv)`. Take `⟨z, rfl⟩` from `Submodule.mem_span_singleton.1 hy`. Establish `hz : z ≠ 0`. Introduce and unpack `rfl`.

Apply `hw0` to reduce the goal to its premises. Rewrite using `[← hmk, Submodule.Quotient.mk_eq_zero, ← hyc]`. Simplify using `using hc`. Establish `hf₀mem : f₀ ∈ Submodule.span ℂ {v} ⊔ C`. Establish `: f₀ = z⁻¹ • v - z⁻¹ • c`.

Rewrite using `[← hyc, smul_add, smul_smul, inv_mul_cancel₀ hz, one_smul, add_sub_cancel_right]`. Rewrite using `[this]`. Conclude with `Submodule.sub_mem _ (Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v))) (Submodule.mem_sup_right (C.smul_mem _ hc))`. Use `hf₀.trans (sup_le ?_ le_sup_right)` and prove the remaining obligations. Rewrite using `[Submodule.span_le, Set.singleton_subset_iff]`.

Conclude with `hf₀mem`.
-/
theorem cycMod_rel (P Q R S : ℕ) (x : ℚ) (hne : GlobalTheory.FockQuot.rel P Q R S x ≠ ⊤) :
    CycMod (fockAct2 P Q R S) (GlobalTheory.FockQuot.rel P Q R S x) := by
  set C := GlobalTheory.FockQuot.rel P Q R S x with hC
  have hnt : Nontrivial (GlobalTheory.FockQuot.gkQ P Q R S x 0).V := by
    show Nontrivial (Pol P Q R S ⧸ C)
    exact Submodule.Quotient.nontrivial_iff.2 hne
  have hlift : IsLift x 0 (GlobalTheory.FockQuot.gkQ P Q R S x 0) C.mkQ := by
    refine ⟨Submodule.mkQ_surjective _, fun X f => GlobalTheory.FockQuot.mk_fockFirstAction_eq_trace_smul P Q R S x X f, fun Y f => ?_⟩
    show GlobalTheory.FockQuot.actQ P Q R S x 0 Y (Submodule.Quotient.mk f) = _
    rw [GlobalTheory.FockQuot.actQ_mk, GlobalTheory.FockQuot.fockSecondActionTraceShift_apply]; rfl
  obtain ⟨μ', hJ, w, ⟨hw0, hwhw⟩, hgen⟩ :=
    GlobalTheory.RealLift.GenLift.genBy_of_isLift P Q R S x 0 _ _ hlift hnt
  change w ∈ hwSub (GlobalTheory.FockQuot.actQ P Q R S x 0) _ at hwhw
  change genSub (GlobalTheory.FockQuot.actQ P Q R S x 0) {w} = ⊤ at hgen
  obtain ⟨f₁, rfl⟩ := Submodule.Quotient.mk_surjective C w
  change (Submodule.Quotient.mk f₁ : Pol P Q R S ⧸ C) ≠ 0 at hw0
  have hwhw' : (Submodule.Quotient.mk f₁ : Pol P Q R S ⧸ C) ∈
      hwSub (GlobalTheory.FockQuot.actQ P Q R S x 0) (fun c => μ' c + 0) := hwhw
  obtain ⟨hwt0, hpos0⟩ := Submodule.mem_inf.1 hwhw'
  have hwt : ∀ c, GlobalTheory.FockQuot.actQ P Q R S x 0 (Eab c c) (Submodule.Quotient.mk f₁ : Pol P Q R S ⧸ C) =
      (((μ' c + 0 : ℚ)) : ℂ) • (Submodule.Quotient.mk f₁ : Pol P Q R S ⧸ C) := fun c => by
    unfold wtSub at hwt0
    have h := (Submodule.mem_iInf _).1 hwt0 c
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at h
    simpa using h
  have hpos : ∀ c d, posC c d →
      GlobalTheory.FockQuot.actQ P Q R S x 0 (Eab c d) (Submodule.Quotient.mk f₁ : Pol P Q R S ⧸ C) = 0 := fun c d hcd => by
    have h := (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hpos0 c) d) hcd
    exact h
  have hKC : KStable (fockAct2 P Q R S) C := fun X _ y hy => rel_stab P Q R S x X y hy
  have hKT : KStable (fockAct2 P Q R S) (⊤ : Submodule ℂ (Pol P Q R S)) := fun _ _ _ _ => Submodule.mem_top
  have h1 : ∀ c, fockAct2 P Q R S (Eab c c) f₁ - ((μ' c : ℚ) : ℂ) • f₁ ∈ C := by
    intro c
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul,
      ← actQ_zero_mk, hwt c]
    simp
  have h2 : ∀ c d, posC c d → fockAct2 P Q R S (Eab c d) f₁ ∈ C := by
    intro c d hcd
    rw [← Submodule.Quotient.mk_eq_zero, ← actQ_zero_mk]
    exact hpos c d hcd
  obtain ⟨v, -, hv, hfv⟩ :=
    GlobalTheory.T.exists_highestWeight_lift_mod_stable_subspace R S (Pol P Q R S) (fockAct2 P Q R S) (fockAct2_good P Q R S) C ⊤ hKC hKT μ' f₁
      Submodule.mem_top h1 h2
  have hmk : (Submodule.Quotient.mk v : Pol P Q R S ⧸ C) = Submodule.Quotient.mk f₁ :=
    ((Submodule.Quotient.eq C).2 hfv).symm
  refine ⟨μ', v, hv, ?_, ?_⟩
  ·
    set N := genSub (fockAct2 P Q R S) {v} ⊔ C with hN
    have hNst : ∀ Z, ∀ y ∈ N, fockAct2 P Q R S Z y ∈ N := by
      intro Z y hy
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hy
      rw [map_add]
      exact N.add_mem (Submodule.mem_sup_left (genSub_stable _ _ Z a ha))
        (Submodule.mem_sup_right (rel_stab P Q R S x Z b hb))
    have hle : genSub (GlobalTheory.FockQuot.actQ P Q R S x 0) {Submodule.Quotient.mk f₁} ≤ N.map C.mkQ := by
      refine sInf_le ⟨?_, ?_⟩
      · rw [Set.singleton_subset_iff, ← hmk]
        exact ⟨v, Submodule.mem_sup_left (mem_genSub_self _ v), rfl⟩
      · rintro Z _ ⟨n, hn, rfl⟩
        refine ⟨fockAct2 P Q R S Z n, hNst Z n hn, ?_⟩
        simp only [Submodule.mkQ_apply]
        rw [actQ_zero_mk]
    have hle2 : N.map C.mkQ = ⊤ := top_le_iff.1 (le_trans (le_of_eq hgen.symm) hle)
    rw [eq_top_iff]
    intro f _
    have hf : Submodule.Quotient.mk f ∈ N.map C.mkQ := by rw [hle2]; exact Submodule.mem_top
    obtain ⟨n, hn, hnf⟩ := hf
    have hd : n - f ∈ C := (Submodule.Quotient.eq C).1 hnf
    have : f = n - (n - f) := by abel
    rw [this]
    exact N.sub_mem hn (Submodule.mem_sup_right hd)
  ·
    obtain ⟨f₀, hf₀⟩ := GlobalTheory.T.highestWeight_le_span_sup_fockCoinvariants P Q R S x μ' hJ
    rw [coinv_eq_rel] at hf₀
    obtain ⟨y, hy, c, hc, hyc⟩ := Submodule.mem_sup.1 (hf₀ hv)
    obtain ⟨z, rfl⟩ := Submodule.mem_span_singleton.1 hy
    have hz : z ≠ 0 := by
      rintro rfl
      apply hw0
      rw [← hmk, Submodule.Quotient.mk_eq_zero, ← hyc]
      simpa using hc
    have hf₀mem : f₀ ∈ Submodule.span ℂ {v} ⊔ C := by
      have : f₀ = z⁻¹ • v - z⁻¹ • c := by
        rw [← hyc, smul_add, smul_smul, inv_mul_cancel₀ hz, one_smul, add_sub_cancel_right]
      rw [this]
      exact Submodule.sub_mem _ (Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)))
        (Submodule.mem_sup_right (C.smul_mem _ hc))
    refine hf₀.trans (sup_le ?_ le_sup_right)
    rw [Submodule.span_le, Set.singleton_subset_iff]
    exact hf₀mem

end GlobalTheory.HoweR.Cyc

/- English proof (translation)
Introduce `P Q R S x`. Break down `GlobalTheory.HoweR.coinv_top_or_rat P Q R S x with h | ⟨x', h⟩` into its components or cases. Rewrite using `[h]`. Use `⟨0, 0, Submodule.zero_mem _, by simp, by simp⟩` and prove the remaining obligations. Rewrite `*` using `[h, GlobalTheory.HoweR.Cyc.coinv_eq_rel]`.

Distinguish the cases in `hne : GlobalTheory.FockQuot.rel P Q R S x' = ⊤`. Rewrite using `[hne]`. Conclude with `⟨0, 0, Submodule.zero_mem _, by simp, by simp⟩`. Conclude with `GlobalTheory.HoweR.Cyc.cycMod_rel P Q R S x' hne`.
-/
theorem GlobalTheory.HoweR.coinv_cycMod : ∀ (P Q R S : ℕ) (x : ℂ), CycMod (fockAct2 P Q R S) (coinv P Q R S x) := by
  intro P Q R S x
  rcases GlobalTheory.HoweR.coinv_top_or_rat P Q R S x with h | ⟨x', h⟩
  · rw [h]
    refine ⟨0, 0, Submodule.zero_mem _, by simp, by simp⟩
  · rw [h, GlobalTheory.HoweR.Cyc.coinv_eq_rel] at *
    by_cases hne : GlobalTheory.FockQuot.rel P Q R S x' = ⊤
    · rw [hne]
      exact ⟨0, 0, Submodule.zero_mem _, by simp, by simp⟩
    · exact GlobalTheory.HoweR.Cyc.cycMod_rel P Q R S x' hne
