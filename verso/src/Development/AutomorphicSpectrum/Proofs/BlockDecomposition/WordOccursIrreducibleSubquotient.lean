import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InSupportOfIsSubquotient
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchurAdmissibleAlt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionTensorProductHasFiniteLength

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

namespace GlobalTheory.CompanionTheory.WordIrr

/- English proof (translation)
Establish `hint : ∀ (g : G) (u : V), f.toLinearMap (σ g u) = τ g (f.toLinearMap u)` using `fun g u => LinearMap.congr_fun (f.isIntertwining' g) u`. Establish `hfL : ∀ x, f x = f.toLinearMap x` using `fun _ => rfl`. Establish `hy' : y ∈ Submodule.span ℂ {w | ∃ (n : H) (v : W), w = τ ↑n v - ↑((1 : H →* ℂˣ) n) • v}` using `hy`. Use `clear hy`. Proceed by induction on `hy' using Submodule.span_induction with`.

Consider the case `mem w hw`. Take `⟨n, v, rfl⟩` from `hw`. Take `⟨u, rfl⟩` from `hf v`. Use `⟨σ ↑n u - ↑((1 : H →* ℂˣ) n) • u, Submodule.subset_span ⟨n, u, rfl⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [hfL, map_sub, Units.smul_def, map_smul, hint]`.

Consider the case `zero`. Use `⟨0, Submodule.zero_mem _, ?_⟩` and prove the remaining obligations. Rewrite using `[hfL]`. Conclude with `map_zero _`. Consider the case `add a b _ _ ha hb`.

Take `⟨x1, hx1, rfl⟩` from `ha`. Take `⟨x2, hx2, rfl⟩` from `hb`. Use `⟨x1 + x2, add_mem hx1 hx2, ?_⟩` and prove the remaining obligations. Simplify using `only [hfL, map_add]`. Consider the case `smul c a _ ha`.

Take `⟨x1, hx1, rfl⟩` from `ha`. Use `⟨c • x1, Submodule.smul_mem _ c hx1, ?_⟩` and prove the remaining obligations. Simplify using `only [hfL, map_smul]`.
-/
theorem exists_lift_twKer {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ G V} {τ : Representation ℂ G W} (f : σ.IntertwiningMap τ)
    (hf : Function.Surjective f) {H : Subgroup G} {y : W} (hy : y ∈ twKer τ H 1) :
    ∃ x ∈ twKer σ H 1, f x = y := by
  have hint : ∀ (g : G) (u : V), f.toLinearMap (σ g u) = τ g (f.toLinearMap u) :=
    fun g u => LinearMap.congr_fun (f.isIntertwining' g) u
  have hfL : ∀ x, f x = f.toLinearMap x := fun _ => rfl
  have hy' : y ∈ Submodule.span ℂ {w | ∃ (n : H) (v : W), w = τ ↑n v - ↑((1 : H →* ℂˣ) n) • v} := hy
  clear hy
  induction hy' using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨n, v, rfl⟩ := hw
    obtain ⟨u, rfl⟩ := hf v
    refine ⟨σ ↑n u - ↑((1 : H →* ℂˣ) n) • u, Submodule.subset_span ⟨n, u, rfl⟩, ?_⟩
    simp only [hfL, map_sub, Units.smul_def, map_smul, hint]
  | zero =>
    refine ⟨0, Submodule.zero_mem _, ?_⟩
    rw [hfL]
    exact map_zero _
  | add a b _ _ ha hb =>
    obtain ⟨x1, hx1, rfl⟩ := ha
    obtain ⟨x2, hx2, rfl⟩ := hb
    refine ⟨x1 + x2, add_mem hx1 hx2, ?_⟩
    simp only [hfL, map_add]
  | smul c a _ ha =>
    obtain ⟨x1, hx1, rfl⟩ := ha
    refine ⟨c • x1, Submodule.smul_mem _ c hx1, ?_⟩
    simp only [hfL, map_smul]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {N s : ℕ} {d : Fin s → ℕ} {V U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]

/- English proof (translation)
Set `j : S.toRepresentation.IntertwiningMap π` to `⟨S.toSubmodule.subtype, fun _ => rfl⟩`. Establish `hS : IsSmooth S.toRepresentation` using `(IsSubquotient.of_injective j Subtype.val_injective).isSmooth hπ`. Set `ι : T.toRepresentation.IntertwiningMap S.toRepresentation` to `⟨Submodule.inclusion h, fun _ => rfl⟩`. Set `p : S.toRepresentation.IntertwiningMap (subQuot S T)` to `⟨Submodule.mkQ _, fun _ => rfl⟩`. Establish `hp : ∀ v, p v = 0 ↔ v.1 ∈ T.toSubmodule` using `fun v => Submodule.Quotient.mk_eq_zero _`.

Establish `hps : Function.Surjective p` using `Submodule.Quotient.mk_surjective _`. Use `jhMult_exact (jacMap e ι) (jacMap e p) hσ (GlobalTheory.JacquetExact.jacMap_injective e hS ι (Submodule.inclusion_injective h)) (GlobalTheory.JacquetExact.jacMap_surjective e p hps) (fun u => ?_) (fun v hv => ?_)` and prove the remaining obligations. Take `⟨t, rfl⟩` from `Submodule.Quotient.mk_surjective _ u`. Establish `h0 : p (ι t) = 0` using `(hp _).2 t.2`. Use `show Submodule.Quotient.mk (p (ι t)) = 0`.

Rewrite using `[h0]`. Both sides reduce to the same expression. Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective _ v`. Establish `h1 : p x ∈ twKer (subQuot S T) (unipRad k e) 1` using `(Submodule.Quotient.mk_eq_zero _).1 hv`. Take `⟨y, hy, hxy⟩` from `exists_lift_twKer p hps h1`.

Establish `h2 : (x - y).1 ∈ T.toSubmodule` using `(hp _).1 (by rw [map_sub, hxy, sub_self])`. Use `⟨Submodule.Quotient.mk ⟨(x - y).1, h2⟩, ?_⟩` and prove the remaining obligations. Use `show Submodule.Quotient.mk (x - y) = Submodule.Quotient.mk x`. Use `(Submodule.Quotient.eq _).2 ?_` and prove the remaining obligations. Rewrite using `[sub_sub_cancel_left]`.

Conclude with `neg_mem hy`.
-/
theorem jhMult_jac_of_le (e : (Σ a, Fin (d a)) ≃ Fin N)
    {σ : Representation ℂ (Levi k fun a => Fin (d a)) U} (hσ : σ.IsIrreducible)
    {π : Representation ℂ (GL (Fin N) k) V} (hπ : IsSmooth π) {S T : Subrepresentation π} (h : T ≤ S) :
    jhMult σ (jac e S.toRepresentation) =
      jhMult σ (jac e T.toRepresentation) + jhMult σ (jac e (subQuot S T)) := by
  let j : S.toRepresentation.IntertwiningMap π := ⟨S.toSubmodule.subtype, fun _ => rfl⟩
  have hS : IsSmooth S.toRepresentation := (IsSubquotient.of_injective j Subtype.val_injective).isSmooth hπ
  let ι : T.toRepresentation.IntertwiningMap S.toRepresentation := ⟨Submodule.inclusion h, fun _ => rfl⟩
  let p : S.toRepresentation.IntertwiningMap (subQuot S T) := ⟨Submodule.mkQ _, fun _ => rfl⟩
  have hp : ∀ v, p v = 0 ↔ v.1 ∈ T.toSubmodule := fun v => Submodule.Quotient.mk_eq_zero _
  have hps : Function.Surjective p := Submodule.Quotient.mk_surjective _
  refine jhMult_exact (jacMap e ι) (jacMap e p) hσ
    (GlobalTheory.JacquetExact.jacMap_injective e hS ι (Submodule.inclusion_injective h))
    (GlobalTheory.JacquetExact.jacMap_surjective e p hps) (fun u => ?_) (fun v hv => ?_)
  · obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    have h0 : p (ι t) = 0 := (hp _).2 t.2
    show Submodule.Quotient.mk (p (ι t)) = 0
    rw [h0]
    rfl
  · obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    have h1 : p x ∈ twKer (subQuot S T) (unipRad k e) 1 := (Submodule.Quotient.mk_eq_zero _).1 hv
    obtain ⟨y, hy, hxy⟩ := exists_lift_twKer p hps h1
    have h2 : (x - y).1 ∈ T.toSubmodule := (hp _).1 (by rw [map_sub, hxy, sub_self])
    refine ⟨Submodule.Quotient.mk ⟨(x - y).1, h2⟩, ?_⟩
    show Submodule.Quotient.mk (x - y) = Submodule.Quotient.mk x
    refine (Submodule.Quotient.eq _).2 ?_
    rw [sub_sub_cancel_left]
    exact neg_mem hy

/- English proof (translation)
Establish `φ` using `Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := π)`. Take `⟨_, _⟩` from `isFiniteLength_iff_isNoetherian_isArtinian.1 hl`. Establish `: WellFoundedGT (Subrepresentation π)` using `φ.toOrderEmbedding.wellFoundedGT`. Establish `: WellFoundedLT (Subrepresentation π)` using `φ.toOrderEmbedding.wellFoundedLT`. Proceed by induction on `S using WellFoundedLT.induction with`.

Consider the case `ind S ih`. Break down `eq_or_ne S ⊥ with rfl | hne` into its components or cases. It suffices to derive a contradiction. Apply `hS` to reduce the goal to its premises. Establish `h0 : Subsingleton (⊥ : Subrepresentation π).toSubmodule` using `inferInstanceAs (Subsingleton (⊥ : Submodule ℂ V))`.

Establish `h1 : Subsingleton (Jacquet (⊥ : Subrepresentation π).toRepresentation (unipRad k e))` using `(Submodule.Quotient.mk_surjective _).subsingleton`. Conclude with `jhMult_of_subsingleton hσ _`. Take `⟨T, -, hT⟩` from `exists_le_covBy_of_lt (bot_lt_iff_ne_bot.2 hne)`. Set `ι : T.toRepresentation.IntertwiningMap S.toRepresentation` to `⟨Submodule.inclusion hT.le, fun _ => rfl⟩`. Set `p : S.toRepresentation.IntertwiningMap (subQuot S T)` to `⟨Submodule.mkQ _, fun _ => rfl⟩`.

Set `j : S.toRepresentation.IntertwiningMap π` to `⟨S.toSubmodule.subtype, fun _ => rfl⟩`. Rewrite `hS` using `[jhMult_jac_of_le e hσ hπ hT.le]`. Distinguish the cases in `h0 : jhMult σ (jac e T.toRepresentation) = 0`. Rewrite `hS` using `[h0, zero_add]`. Establish `hq : IsSubquotient (subQuot S T) S.toRepresentation` using `.of_surjective p (Submodule.Quotient.mk_surjective _)`.

Establish `hsm : IsSmooth (subQuot S T)` using `(hq.trans (.of_injective j Subtype.val_injective)).isSmooth hπ`. Conclude with `⟨⟨_, subQuot S T, hsm, isIrreducible_subQuot hT⟩, hq, hS⟩`. Take `⟨τ, h1, h2⟩` from `ih T hT.lt h0`. Conclude with `⟨τ, h1.trans (.of_injective ι (Submodule.inclusion_injective hT.le)), h2⟩`.
-/
theorem exists_irrRep_of_subrep (e : (Σ a, Fin (d a)) ≃ Fin N)
    {σ : Representation ℂ (Levi k fun a => Fin (d a)) U} (hσ : σ.IsIrreducible)
    {π : Representation ℂ (GL (Fin N) k) V} (hπ : IsSmooth π) (hl : HasFiniteLength π)
    (S : Subrepresentation π) (hS : jhMult σ (jac e S.toRepresentation) ≠ 0) :
    ∃ τ : IrrRep (GL (Fin N) k), IsSubquotient τ.ρ S.toRepresentation ∧ jhMult σ (jac e τ.ρ) ≠ 0 := by
  have φ := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := π)
  obtain ⟨_, _⟩ := isFiniteLength_iff_isNoetherian_isArtinian.1 hl
  have : WellFoundedGT (Subrepresentation π) := φ.toOrderEmbedding.wellFoundedGT
  have : WellFoundedLT (Subrepresentation π) := φ.toOrderEmbedding.wellFoundedLT
  induction S using WellFoundedLT.induction with
  | ind S ih =>
  rcases eq_or_ne S ⊥ with rfl | hne
  · exfalso
    apply hS
    have h0 : Subsingleton (⊥ : Subrepresentation π).toSubmodule :=
      inferInstanceAs (Subsingleton (⊥ : Submodule ℂ V))
    have h1 : Subsingleton (Jacquet (⊥ : Subrepresentation π).toRepresentation (unipRad k e)) :=
      (Submodule.Quotient.mk_surjective _).subsingleton
    exact jhMult_of_subsingleton hσ _
  obtain ⟨T, -, hT⟩ := exists_le_covBy_of_lt (bot_lt_iff_ne_bot.2 hne)
  let ι : T.toRepresentation.IntertwiningMap S.toRepresentation := ⟨Submodule.inclusion hT.le, fun _ => rfl⟩
  let p : S.toRepresentation.IntertwiningMap (subQuot S T) := ⟨Submodule.mkQ _, fun _ => rfl⟩
  let j : S.toRepresentation.IntertwiningMap π := ⟨S.toSubmodule.subtype, fun _ => rfl⟩
  rw [jhMult_jac_of_le e hσ hπ hT.le] at hS
  by_cases h0 : jhMult σ (jac e T.toRepresentation) = 0
  · rw [h0, zero_add] at hS
    have hq : IsSubquotient (subQuot S T) S.toRepresentation :=
      .of_surjective p (Submodule.Quotient.mk_surjective _)
    have hsm : IsSmooth (subQuot S T) :=
      (hq.trans (.of_injective j Subtype.val_injective)).isSmooth hπ
    exact ⟨⟨_, subQuot S T, hsm, isIrreducible_subQuot hT⟩, hq, hS⟩
  · obtain ⟨τ, h1, h2⟩ := ih T hT.lt h0
    exact ⟨τ, h1.trans (.of_injective ι (Submodule.inclusion_injective hT.le)), h2⟩

/- English proof (translation)
Introduce `k _ _ _ _ hA N V _ _ π hπ hl w ⟨hd, hw⟩`. Establish `hσ : (piTensor fun a => (w.get a).rep).IsIrreducible` using `GlobalTheory.ProdFiniteLength.piTensor_isIrreducible_of_schur _ (fun a => (w.get a).2.rep.irr) fun a φ hφ => GlobalTheory.SchurAdm.schur_admissible _ (KO k (Fin (w.get a).1)) GlobalTheory.SplitFlip.isOpen_KO GlobalTheory.SplitFlip.isCompact_KO _ _ (w.get a).2.rep.irr (hA k _ _ _ …`. Establish `hT1 : IsSubquotient π (⊤ : Subrepresentation π).toRepresentation` using `.of_surjective (topEquiv π).toIntertwiningMap (topEquiv π).surjective`. Establish `hT2 : IsSubquotient (⊤ : Subrepresentation π).toRepresentation π` using `.of_injective (topEquiv π).toIntertwiningMap (topEquiv π).injective`. Establish `h1 : jhMult (piTensor fun a => (w.get a).rep) (jac (stdBlocks (fun a => (w.get a).1) hd) (⊤ : Subrepresentation π).toRepresentation) ≠ 0` using `jhMult_ne_zero_iff.2 ((jhMult_ne_zero_iff.1 hw).trans (GlobalTheory.JacquetExact.isSubquotient_jac _ (hT2.isSmooth hπ) hT1))`.

Take `⟨τ, h2, h3⟩` from `exists_irrRep_of_subrep _ hσ hπ hl ⊤ h1`. Conclude with `⟨τ, h2.trans hT2, hd, h3⟩`.
-/
theorem exists_irrRep_wd : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL), ∀ {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → HasFiniteLength π → ∀ w : List (IrrGL k), Wd π w → ∃ τ : IrrRep (GL (Fin N) k), IsSubquotient τ.ρ π ∧ Wd τ.ρ w := by
  intro k _ _ _ _ hA N V _ _ π hπ hl w ⟨hd, hw⟩
  have hσ : (piTensor fun a => (w.get a).rep).IsIrreducible :=
    GlobalTheory.ProdFiniteLength.piTensor_isIrreducible_of_schur _ (fun a => (w.get a).2.rep.irr) fun a φ hφ =>
      GlobalTheory.SchurAdm.schur_admissible _ (KO k (Fin (w.get a).1)) GlobalTheory.SplitFlip.isOpen_KO
        GlobalTheory.SplitFlip.isCompact_KO _ _ (w.get a).2.rep.irr
        (hA k _ _ _ (w.get a).2.rep.smooth (w.get a).2.rep.irr) φ hφ
  have hT1 : IsSubquotient π (⊤ : Subrepresentation π).toRepresentation :=
    .of_surjective (topEquiv π).toIntertwiningMap (topEquiv π).surjective
  have hT2 : IsSubquotient (⊤ : Subrepresentation π).toRepresentation π :=
    .of_injective (topEquiv π).toIntertwiningMap (topEquiv π).injective
  have h1 : jhMult (piTensor fun a => (w.get a).rep)
      (jac (stdBlocks (fun a => (w.get a).1) hd) (⊤ : Subrepresentation π).toRepresentation) ≠ 0 :=
    jhMult_ne_zero_iff.2 ((jhMult_ne_zero_iff.1 hw).trans
      (GlobalTheory.JacquetExact.isSubquotient_jac _ (hT2.isSmooth hπ) hT1))
  obtain ⟨τ, h2, h3⟩ := exists_irrRep_of_subrep _ hσ hπ hl ⊤ h1
  exact ⟨τ, h2.trans hT2, hd, h3⟩

end GlobalTheory.CompanionTheory.WordIrr

end
