import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.IntertwiningCandidates.StrictJoin
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.PolynomialPairSpaces.InfUniq

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.SpectralAccumulation

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.FX.Bo.Tw.StrictJoinAlt

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.FX.Bo

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Use `⟨by rw [Multiset.card_map]; exact h.1, ?_⟩` and prove the remaining obligations. Introduce and unpack `u _ ⟨φ, hφ, rfl⟩`. Express the relevant statement in the definitionally equal form `cap τ u (mulChi a χ φ) = _ • mulChi a χ φ`. Rewrite using `[cap_mulChi, h.2 _ φ hφ, map_smul, Multiset.map_map]`. Use `congr 2`.

Conclude with `Multiset.map_congr rfl fun x _ => by simp only [Function.comp_apply]; ring`.
-/
theorem hasInf_map {a : ℕ} {V : Submodule ℂ (Sm E a)} {τ : E →+* ℂ} {m : Multiset ℂ}
    (h : HasInfCharGL V τ m) (χ : HChar E) :
    HasInfCharGL (V.map (mulChi a χ).toLinearMap) τ (m.map (· + expo χ τ)) := by
  refine ⟨by rw [Multiset.card_map]; exact h.1, ?_⟩
  rintro u _ ⟨φ, hφ, rfl⟩
  change cap τ u (mulChi a χ φ) = _ • mulChi a χ φ
  rw [cap_mulChi, h.2 _ φ hφ, map_smul, Multiset.map_map]
  congr 2
  exact Multiset.map_congr rfl fun x _ => by simp only [Function.comp_apply]; ring

/- English proof (translation)
Take `⟨T, hT⟩` from `hV`. Set `M` to `mulChi a χ`. Use `⟨((M.submoduleMap V).symm.trans T).trans (M.submoduleMap V'), ?_⟩` and prove the remaining obligations. Introduce `o φ ψ hψ`. Use `set φ₀ := (M.submoduleMap V).symm φ with hφ₀`.

Use `set ψ₀ := (M.submoduleMap V).symm ψ with hψ₀`. Establish `eφ : φ.1 = M φ₀.1`. Use `congrArg Subtype.val ((M.submoduleMap V).apply_symm_apply φ)` as an intermediate fact. Rewrite using `[← this]`. Both sides reduce to the same expression.

Establish `eψ : ψ.1 = M ψ₀.1`. Use `congrArg Subtype.val ((M.submoduleMap V).apply_symm_apply ψ)` as an intermediate fact. Rewrite using `[← this]`. Both sides reduce to the same expression. Establish `key : ψ₀.1 = ((opMul χ o : ℂˣ) : ℂ) • act o φ₀.1 + opAdd χ o • φ₀.1`.

Apply `M.injective` to reduce the goal to its premises. Rewrite using `[← eψ, hψ, eφ]`. Conclude with `act_mulChi χ o φ₀.1`. Establish `hmem : act o φ₀.1 ∈ V`. Establish `: act o φ₀.1 = ((opMul χ o : ℂˣ) : ℂ)⁻¹ • (ψ₀.1 - opAdd χ o • φ₀.1)`.

Rewrite using `[key, add_sub_cancel_right, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul]`. Rewrite using `[this]`. Conclude with `V.smul_mem _ (V.sub_mem ψ₀.2 (V.smul_mem _ φ₀.2))`. Establish `hψ' : ψ₀ = ((opMul χ o : ℂˣ) : ℂ) • (⟨act o φ₀.1, hmem⟩ : V) + opAdd χ o • φ₀` using `Subtype.ext key`. Establish `h1` using `hT o φ₀ ⟨act o φ₀.1, hmem⟩ rfl`.

Express the relevant statement in the definitionally equal form `(M (T ψ₀).1) = act o (M (T φ₀).1)`. Rewrite using `[act_mulChi, hψ', map_add, map_smul, map_smul]`. Simplify using `only [Submodule.coe_add, Submodule.coe_smul, h1]`. Both sides reduce to the same expression.
-/
theorem isoV_map {a : ℕ} {V V' : Submodule ℂ (Sm E a)} (hV : IsoV V V') (χ : HChar E) :
    IsoV (V.map (mulChi a χ).toLinearMap) (V'.map (mulChi a χ).toLinearMap) := by
  obtain ⟨T, hT⟩ := hV
  let M := mulChi a χ
  refine ⟨((M.submoduleMap V).symm.trans T).trans (M.submoduleMap V'), ?_⟩
  intro o φ ψ hψ
  set φ₀ := (M.submoduleMap V).symm φ with hφ₀
  set ψ₀ := (M.submoduleMap V).symm ψ with hψ₀
  have eφ : φ.1 = M φ₀.1 := by
    have := congrArg Subtype.val ((M.submoduleMap V).apply_symm_apply φ); rw [← this]; rfl
  have eψ : ψ.1 = M ψ₀.1 := by
    have := congrArg Subtype.val ((M.submoduleMap V).apply_symm_apply ψ); rw [← this]; rfl
  have key : ψ₀.1 = ((opMul χ o : ℂˣ) : ℂ) • act o φ₀.1 + opAdd χ o • φ₀.1 := by
    apply M.injective
    rw [← eψ, hψ, eφ]
    exact act_mulChi χ o φ₀.1
  have hmem : act o φ₀.1 ∈ V := by
    have : act o φ₀.1 = ((opMul χ o : ℂˣ) : ℂ)⁻¹ • (ψ₀.1 - opAdd χ o • φ₀.1) := by
      rw [key, add_sub_cancel_right, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul]
    rw [this]
    exact V.smul_mem _ (V.sub_mem ψ₀.2 (V.smul_mem _ φ₀.2))
  have hψ' : ψ₀ = ((opMul χ o : ℂˣ) : ℂ) • (⟨act o φ₀.1, hmem⟩ : V) + opAdd χ o • φ₀ := Subtype.ext key
  have h1 := hT o φ₀ ⟨act o φ₀.1, hmem⟩ rfl
  change (M (T ψ₀).1) = act o (M (T φ₀).1)
  rw [act_mulChi, hψ', map_add, map_smul, map_smul]
  simp only [Submodule.coe_add, Submodule.coe_smul, h1]
  rfl

/- English proof (translation)
Take `⟨N, V⟩` from `x`. Take `⟨N', V'⟩` from `y`. Take `⟨e, hi⟩` from `h`. Simplify using `only at e`. Substitute `e` using the available equality.

Conclude with `⟨rfl, isoV_map hi χ⟩`.
-/
theorem sIso_tw {x y : Σ M : ℕ, Submodule ℂ (Sm E M)} (h : SIso x y) (χ : HChar E) :
    SIso (twPart χ x) (twPart χ y) := by
  obtain ⟨N, V⟩ := x
  obtain ⟨N', V'⟩ := y
  obtain ⟨e, hi⟩ := h
  dsimp only at e
  subst e
  exact ⟨rfl, isoV_map hi χ⟩

def SInf (x y : Σ M : ℕ, Submodule ℂ (Sm E M)) : Prop :=
  ∀ τ, ∃ m, HasInfCharGL x.2 τ m ∧ HasInfCharGL y.2 τ m

/- English proof (translation)
Simplify using `[parts]`.
-/
theorem length_parts {n : ℕ} (P : Pre E n) : (parts P).length = P.c := by simp [parts]

/- English proof (translation)
Take `⟨hc, hm⟩` from `h.2`. Rewrite using `[List.forall₂_iff_get]`. Use `⟨by simp [length_parts, hc], fun i h₁ h₂ => ?_⟩` and prove the remaining obligations. Introduce `τ`. Establish `hi : i < P.c` using `by simpa [length_parts] using h₁`.

Use `⟨(P.m ⟨i, hi⟩ τ).map (· + expo χ τ), ?_, ?_⟩` and prove the remaining obligations. Establish `e : ((parts P).map (twPart χ)).get ⟨i, h₁⟩ = twPart χ ⟨P.N ⟨i, hi⟩, P.V ⟨i, hi⟩⟩`. Simplify using `[parts]`. Rewrite using `[e]`. Conclude with `hasInf_map (P.inf _ τ) χ`.

Establish `e : ((parts P').map (twPart χ)).get ⟨i, h₂⟩ = twPart χ ⟨P'.N (Fin.cast hc ⟨i, hi⟩), P'.V (Fin.cast hc ⟨i, hi⟩)⟩`. Simplify using `[parts]`. Rewrite using `[e, hm ⟨i, hi⟩]`. Conclude with `hasInf_map (P'.inf _ τ) χ`.
-/
theorem sInf_tw {a : ℕ} {P P' : Pre E a} (h : Strict P P') (χ : HChar E) :
    List.Forall₂ SInf ((parts P).map (twPart χ)) ((parts P').map (twPart χ)) := by
  obtain ⟨hc, hm⟩ := h.2
  rw [List.forall₂_iff_get]
  refine ⟨by simp [length_parts, hc], fun i h₁ h₂ => ?_⟩
  intro τ
  have hi : i < P.c := by simpa [length_parts] using h₁
  refine ⟨(P.m ⟨i, hi⟩ τ).map (· + expo χ τ), ?_, ?_⟩
  · have e : ((parts P).map (twPart χ)).get ⟨i, h₁⟩ = twPart χ ⟨P.N ⟨i, hi⟩, P.V ⟨i, hi⟩⟩ := by
      simp [parts]
    rw [e]
    exact hasInf_map (P.inf _ τ) χ
  · have e : ((parts P').map (twPart χ)).get ⟨i, h₂⟩ =
        twPart χ ⟨P'.N (Fin.cast hc ⟨i, hi⟩), P'.V (Fin.cast hc ⟨i, hi⟩)⟩ := by
      simp [parts]
    rw [e, hm ⟨i, hi⟩]
    exact hasInf_map (P'.inf _ τ) χ

/- English proof (translation)
Establish `hc : P.c = P'.c` using `by rw [← length_parts, ← length_parts]; exact h₂.length_eq`. Use `⟨h₁, hc, fun i => funext fun τ => ?_⟩` and prove the remaining obligations. Establish `hi : i.1 < (parts P).length` using `by rw [length_parts]; exact i.2`. Establish `hi' : i.1 < (parts P').length` using `by rw [length_parts, ← hc]; exact i.2`. Take `⟨m, hm, hm'⟩` from `(List.forall₂_iff_get.1 h₂).2 i.1 hi hi' τ`.

Establish `e : (parts P).get ⟨i.1, hi⟩ = ⟨P.N i, P.V i⟩` using `by simp [parts]`. Establish `e' : (parts P').get ⟨i.1, hi'⟩ = ⟨P'.N (Fin.cast hc i), P'.V (Fin.cast hc i)⟩`. Simplify using `only [parts, List.get_ofFn]`. Both sides reduce to the same expression. Rewrite `hm` using `[e]`.

Rewrite `hm'` using `[e']`. Establish `e1` using `LemDd.InfUniq_holds E _ _ τ _ _ (P.discrete i).ne_bot (P.inf i τ) hm`. Establish `e2` using `LemDd.InfUniq_holds E _ _ τ _ _ (P'.discrete _).ne_bot (P'.inf _ τ) hm'`. Rewrite using `[e1, e2]`.
-/
theorem strict_of {n : ℕ} {P P' : Pre E n} (h₁ : List.Forall₂ SIso (parts P) (parts P'))
    (h₂ : List.Forall₂ SInf (parts P) (parts P')) : Strict P P' := by
  have hc : P.c = P'.c := by rw [← length_parts, ← length_parts]; exact h₂.length_eq
  refine ⟨h₁, hc, fun i => funext fun τ => ?_⟩
  have hi : i.1 < (parts P).length := by rw [length_parts]; exact i.2
  have hi' : i.1 < (parts P').length := by rw [length_parts, ← hc]; exact i.2
  obtain ⟨m, hm, hm'⟩ := (List.forall₂_iff_get.1 h₂).2 i.1 hi hi' τ
  have e : (parts P).get ⟨i.1, hi⟩ = ⟨P.N i, P.V i⟩ := by simp [parts]
  have e' : (parts P').get ⟨i.1, hi'⟩ = ⟨P'.N (Fin.cast hc i), P'.V (Fin.cast hc i)⟩ := by
    simp only [parts, List.get_ofFn]; rfl
  rw [e] at hm
  rw [e'] at hm'
  have e1 := LemDd.InfUniq_holds E _ _ τ _ _ (P.discrete i).ne_bot (P.inf i τ) hm
  have e2 := LemDd.InfUniq_holds E _ _ τ _ _ (P'.discrete _).ne_bot (P'.inf _ τ) hm'
  rw [e1, e2]

end PositivityTheory.Rg.BcB.F.FX.Bo.Tw.StrictJoinAlt

namespace PositivityTheory.Rg.BcB.F.FX.Bo.Tw

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.FX.Bo StrictJoinAlt

/- English proof (translation)
Introduce `E _ _ _ n a b χ₁ χ₂ Pa Pa' Pb Pb' D D' hJ hJ' ha hb`. Use `strict_of ?_ ?_` and prove the remaining obligations. Rewrite using `[hJ, hJ']`. Conclude with `List.rel_append (List.forall₂_map_left_iff.2 (List.forall₂_map_right_iff.2 (ha.1.imp fun _ _ h => sIso_tw h χ₁))) (List.forall₂_map_left_iff.2 (List.forall₂_map_right_iff.2 (hb.1.imp fun _ _ h => sIso_tw h χ₂)))`. Rewrite using `[hJ, hJ']`.

Conclude with `List.rel_append (sInf_tw ha χ₁) (sInf_tw hb χ₂)`.
-/
theorem StrictJoin_holds : StrictJoin := by
  intro E _ _ _ n a b χ₁ χ₂ Pa Pa' Pb Pb' D D' hJ hJ' ha hb
  refine strict_of ?_ ?_
  · rw [hJ, hJ']
    exact List.rel_append
      (List.forall₂_map_left_iff.2 (List.forall₂_map_right_iff.2 (ha.1.imp fun _ _ h => sIso_tw h χ₁)))
      (List.forall₂_map_left_iff.2 (List.forall₂_map_right_iff.2 (hb.1.imp fun _ _ h => sIso_tw h χ₂)))
  · rw [hJ, hJ']
    exact List.rel_append (sInf_tw ha χ₁) (sInf_tw hb χ₂)

end PositivityTheory.Rg.BcB.F.FX.Bo.Tw

end
