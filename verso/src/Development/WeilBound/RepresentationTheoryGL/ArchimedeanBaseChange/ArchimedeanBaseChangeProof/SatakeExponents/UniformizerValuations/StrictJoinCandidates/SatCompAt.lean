import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.InertInSec
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.BaseChangeWeyl.IrredCompSurj
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LemA

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.FX

open PositivityTheory.Rg.BcB.F.LemB in
/- English proof (translation)
Introduce `E _ _ _ n π hπ w hw σ b' ϖ ϖ' q q' α α' hσ hb' hϖ' hI hI' hS hS'`. Apply `PositivityTheory.Rg.BcB.F.LemB.bcWeyl` to reduce the goal to its premises. Take `⟨b, hbK, hb, p, hp, σ1, hc, hsat⟩` from `hS`. Take `⟨p0, hp0, hc0⟩` from `hσ`. Establish `hcj : ∀ x : E, cj w (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)`.

Establish `hex : ∃ s : w.adicCompletion E →+* w.adicCompletion E, Continuous s ∧ ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)`. Assume the negation of the conclusion as `hne`. Take `⟨x, -, hx⟩` from `hI.2.2.2.2.1`. Establish `hid : cj w = RingHom.id _` using `by rw [cj, dif_neg hne]`. Rewrite `hx` using `[hid, RingHom.id_apply, sub_self, map_zero]`.

Conclude with `zero_ne_one hx`. Establish `hcj' : cj w = hex.choose` using `by rw [cj, dif_pos hex]`. Introduce `x`. Rewrite using `[hcj']`. Conclude with `hex.choose_spec.2 x`.

Establish `hUL : ∀ g, g ∈ UL n w ↔ g ∈ UJ (cj w) (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E))`. Introduce `g`. Rewrite using `[UL, if_neg hw]`. Take `⟨e, he⟩` from `GlobalTheory.DefU.Inert.locU_equiv E n w (cj w) hcj hI.2.1`. Set `f` to `conjU (cj w) b hb (UL n w) hUL`.

Set `u : locU n w → UL n w` to `fun x => ⟨(e x).1, (hUL _).2 (e x).2⟩`. Establish `hu : ∀ g : UL n w, u (e.symm ⟨g.1, (hUL _).1 g.2⟩) = g` using `fun g => Subtype.ext (by simp [u])`. Establish `hpf : ∀ x, p x = f (u x)` using `fun x => Subtype.ext ((hp x).trans (by rw [conjU_val, he]))`. Establish `hp0u : ∀ x, p0 x = u x` using `fun x => Subtype.ext ((hp0 x).trans (by simp only [u]; rw [he]))`. Establish `hps : Function.Surjective p` using `fun y => ⟨e.symm ⟨(f.symm y).1, (hUL _).1 (f.symm y).2⟩, by rw [hpf, hu, MulEquiv.apply_symm_apply]⟩`.

Establish `hps0 : Function.Surjective p0` using `fun y => ⟨e.symm ⟨y.1, (hUL _).1 y.2⟩, by rw [hp0u, hu]⟩`. Take `⟨r, -, -, hr⟩` from `GlobalTheory.DefU.LocRet.exists_ret E n w`. Set `Ψ : GlobalTheory.DefU.AutSub E n` to `⟨π, hπ⟩`. Take `⟨-, F0, hF0, hFm, hF⟩` from `hc0`. Take `⟨-, F1, hF1, hFm', hF'⟩` from `hc`.

Set `F : Representation.IntertwiningMap (σ.ρ.comp p0) (Ψ.rep.comp (locU n w).subtype)` to `⟨F0.codRestrict π hFm, fun x => LinearMap.ext fun v => Subtype.ext (hF x v)⟩`. Set `F' : Representation.IntertwiningMap (σ1.ρ.comp p) (Ψ.rep.comp (locU n w).subtype)` to `⟨F1.codRestrict π hFm', fun x => LinearMap.ext fun v => Subtype.ext (hF' x v)⟩`. Establish `hG0 : F ≠ 0` using `fun h => hF0 (LinearMap.ext fun v => congrArg Subtype.val (DFunLike.congr_fun h v))`. Establish `hG1 : F' ≠ 0` using `fun h => hF1 (LinearMap.ext fun v => congrArg Subtype.val (DFunLike.congr_fun h v))`. Take `⟨-, h2⟩` from `GlobalTheory.CuspRep.CompUniq.isotypic (UA E n) (locU n w) Ψ.V σ.V σ1.V Ψ.rep (locU n w).subtype (σ.ρ.comp p0) (σ1.ρ.comp p) Ψ.isIrreducible_rep (irred_comp_surj σ.ρ p0 hps0 σ.irred) (irred_comp_surj σ1.ρ p hps σ1.irred) (fun g => ⟨r g, fun y => hr g y⟩) F hG0`.

Take `⟨T⟩` from `h2 F' hG1`. Establish `hs1 : SatUL b (ϖ : w.adicCompletion E) q σ α`. Use `⟨f, σ1, fun x => rfl, hsat, ⟨{ toLinearEquiv := T.toLinearEquiv, isIntertwining' := fun g => ?_ }⟩⟩` and prove the remaining obligations. Establish `h1 : p (e.symm ⟨g.1, (hUL _).1 g.2⟩) = f g` using `by rw [hpf, hu]`. Establish `h0 : p0 (e.symm ⟨g.1, (hUL _).1 g.2⟩) = g` using `by rw [hp0u, hu]`.

Use `T.isIntertwining' (e.symm ⟨g.1, (hUL _).1 g.2⟩)` as an intermediate fact. Rewrite `this` using `[MonoidHom.comp_apply, MonoidHom.comp_apply, h1, h0]`. Conclude with `this`. Establish `hne : (ϖ : w.adicCompletion E) ≠ 0` using `ϖ.ne_zero`. Establish `hunif : IsUnifAt ϖ`.

Use `⟨?_, hI.2.2.1⟩` and prove the remaining obligations. Establish `hv` using `hI.2.2.2.1`. Establish `h0 : Valued.v (ϖ : w.adicCompletion E) ≠ 0` using `by rw [hv]; exact WithZero.coe_ne_zero`. Establish `hu1 : ∀ h : Valued.v (ϖ : w.adicCompletion E) ≠ 0, WithZero.unzero h = Multiplicative.ofAdd (-1 : ℤ)` using `fun h => WithZero.coe_injective (by rw [WithZero.coe_unzero, hv])`. Use `show ordL (ϖ : w.adicCompletion E) = 1`.

Unfold `ordL`. Rewrite using `[dif_neg h0, hu1]`. Simplify using the standard rewrite rules. Conclude with `PositivityTheory.Rg.BcB.F.Inert.lem_b E n w hw b b' ϖ ϖ' q q' σ α α' ⟨hbK, hb⟩ hb' hunif hϖ' hI hI' hs1 hS'`.
-/
theorem satCompAt : SatCompAt := by
  intro E _ _ _ n π hπ w hw σ b' ϖ ϖ' q q' α α' hσ hb' hϖ' hI hI' hS hS'
  apply PositivityTheory.Rg.BcB.F.LemB.bcWeyl
  obtain ⟨b, hbK, hb, p, hp, σ1, hc, hsat⟩ := hS
  obtain ⟨p0, hp0, hc0⟩ := hσ

  have hcj : ∀ x : E, cj w (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x) := by
    have hex : ∃ s : w.adicCompletion E →+* w.adicCompletion E, Continuous s ∧
        ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x) := by
      by_contra hne
      obtain ⟨x, -, hx⟩ := hI.2.2.2.2.1
      have hid : cj w = RingHom.id _ := by rw [cj, dif_neg hne]
      rw [hid, RingHom.id_apply, sub_self, map_zero] at hx
      exact zero_ne_one hx
    have hcj' : cj w = hex.choose := by rw [cj, dif_pos hex]
    intro x
    rw [hcj']
    exact hex.choose_spec.2 x
  have hUL : ∀ g, g ∈ UL n w ↔ g ∈ UJ (cj w) (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
    intro g
    rw [UL, if_neg hw]
  obtain ⟨e, he⟩ := GlobalTheory.DefU.Inert.locU_equiv E n w (cj w) hcj hI.2.1
  let f := conjU (cj w) b hb (UL n w) hUL
  let u : locU n w → UL n w := fun x => ⟨(e x).1, (hUL _).2 (e x).2⟩
  have hu : ∀ g : UL n w, u (e.symm ⟨g.1, (hUL _).1 g.2⟩) = g := fun g => Subtype.ext (by simp [u])
  have hpf : ∀ x, p x = f (u x) := fun x => Subtype.ext ((hp x).trans (by rw [conjU_val, he]))
  have hp0u : ∀ x, p0 x = u x := fun x => Subtype.ext ((hp0 x).trans (by simp only [u]; rw [he]))
  have hps : Function.Surjective p := fun y =>
    ⟨e.symm ⟨(f.symm y).1, (hUL _).1 (f.symm y).2⟩, by rw [hpf, hu, MulEquiv.apply_symm_apply]⟩
  have hps0 : Function.Surjective p0 := fun y =>
    ⟨e.symm ⟨y.1, (hUL _).1 y.2⟩, by rw [hp0u, hu]⟩

  obtain ⟨r, -, -, hr⟩ := GlobalTheory.DefU.LocRet.exists_ret E n w
  let Ψ : GlobalTheory.DefU.AutSub E n := ⟨π, hπ⟩
  obtain ⟨-, F0, hF0, hFm, hF⟩ := hc0
  obtain ⟨-, F1, hF1, hFm', hF'⟩ := hc
  let F : Representation.IntertwiningMap (σ.ρ.comp p0) (Ψ.rep.comp (locU n w).subtype) :=
    ⟨F0.codRestrict π hFm, fun x => LinearMap.ext fun v => Subtype.ext (hF x v)⟩
  let F' : Representation.IntertwiningMap (σ1.ρ.comp p) (Ψ.rep.comp (locU n w).subtype) :=
    ⟨F1.codRestrict π hFm', fun x => LinearMap.ext fun v => Subtype.ext (hF' x v)⟩
  have hG0 : F ≠ 0 := fun h => hF0 (LinearMap.ext fun v => congrArg Subtype.val (DFunLike.congr_fun h v))
  have hG1 : F' ≠ 0 := fun h => hF1 (LinearMap.ext fun v => congrArg Subtype.val (DFunLike.congr_fun h v))
  obtain ⟨-, h2⟩ := GlobalTheory.CuspRep.CompUniq.isotypic (UA E n) (locU n w) Ψ.V σ.V σ1.V Ψ.rep (locU n w).subtype
    (σ.ρ.comp p0) (σ1.ρ.comp p) Ψ.isIrreducible_rep (irred_comp_surj σ.ρ p0 hps0 σ.irred)
    (irred_comp_surj σ1.ρ p hps σ1.irred) (fun g => ⟨r g, fun y => hr g y⟩) F hG0
  obtain ⟨T⟩ := h2 F' hG1

  have hs1 : SatUL b (ϖ : w.adicCompletion E) q σ α := by
    refine ⟨f, σ1, fun x => rfl, hsat, ⟨{ toLinearEquiv := T.toLinearEquiv, isIntertwining' := fun g => ?_ }⟩⟩
    have h1 : p (e.symm ⟨g.1, (hUL _).1 g.2⟩) = f g := by rw [hpf, hu]
    have h0 : p0 (e.symm ⟨g.1, (hUL _).1 g.2⟩) = g := by rw [hp0u, hu]
    have := T.isIntertwining' (e.symm ⟨g.1, (hUL _).1 g.2⟩)
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, h1, h0] at this
    exact this

  have hne : (ϖ : w.adicCompletion E) ≠ 0 := ϖ.ne_zero
  have hunif : IsUnifAt ϖ := by
    refine ⟨?_, hI.2.2.1⟩
    have hv := hI.2.2.2.1
    have h0 : Valued.v (ϖ : w.adicCompletion E) ≠ 0 := by rw [hv]; exact WithZero.coe_ne_zero
    have hu1 : ∀ h : Valued.v (ϖ : w.adicCompletion E) ≠ 0, WithZero.unzero h = Multiplicative.ofAdd (-1 : ℤ) := fun h =>
      WithZero.coe_injective (by rw [WithZero.coe_unzero, hv])
    show ordL (ϖ : w.adicCompletion E) = 1
    unfold ordL
    rw [dif_neg h0, hu1]
    simp
  exact PositivityTheory.Rg.BcB.F.Inert.lem_b E n w hw b b' ϖ ϖ' q q' σ α α' ⟨hbK, hb⟩ hb' hunif hϖ' hI hI' hs1 hS'

end PositivityTheory.Rg.BcB.F.FX

end
