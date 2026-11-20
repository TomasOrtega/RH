import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.DeltaNear
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArchimedeanUnitaryPointsEquivUnitaryGroupStatement

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching

namespace UpperTheory.Gal.Wt

/- English proof (translation)
Introduce `hEB hEv hTor hQR hBd hEP E _ _ _ a τ W K ν d B hB U hU hBU hne κ hκ k`. Take `⟨e, he⟩` from `GlobalTheory.T.archimedeanUnitaryPoints_equiv_unitaryGroup E a τ`. Establish `hx : ∀ u : Matrix.unitaryGroup (Fin a) ℂ, ∃ x : infU E a, x.1 ∈ embU a τ ∧ cEmb τ x.1 = unitaryIncl a u` using `fun u => by`. Establish `h` using `he (e.symm u)`. Rewrite `h` using `[e.apply_symm_apply]`.

Conclude with `⟨⟨(e.symm u).1, (Subgroup.mem_inf.1 (e.symm u).2).1⟩, (e.symm u).2, h.symm⟩`. Use `choose x hx using fun z : Circle => (show ∃ x : infU E a, x.1 ∈ embU a τ ∧ cEmb τ x.1 = tor a k z by`. Take `⟨u, hu⟩` from `(hTor a k z).2.1`. Rewrite using `[← hu]`. Conclude with `hx u)`.

Name the introduced variables `hxu`. Establish `hc : IsCirc τ k x` using `hx`. Take `⟨S, hS, hBS⟩` from `hB.fin`. Establish `hexp : ∀ (T : Submodule ℂ (Circle → ℂ)) (Φ : Circle → UA E a → ℂ), (∀ z, Φ z ∈ S) → (∀ g, (fun z => Φ z g) ∈ T) → ∀ L : (UA E a → ℂ) →ₗ[ℂ] ℂ, (fun z => L (Φ z)) ∈ T` using `fun T Φ h1 h2 L => hEv S (UA E a) Circle (fun g => LinearMap.proj g ∘ₗ S.subtype) (fun m hm => Subtype.ext (funext hm)) T (fun z => ⟨Φ z, h1 z⟩) h2 (L ∘ₗ S.subtype)`. Take `⟨y₁, y₂, v, hv⟩` from `hne`.

Prove the components needed by the constructor for the conclusion. Take `⟨p, hp0, hp⟩` from `hEP E a τ U hU κ hκ _ (hBU y₁ y₂ v) hv`. Use `(hBd a k κ _).1 {w | ∃ y₁ y₂ v, w = p (B y₁ y₂ v)} ⟨_, ⟨y₁, y₂, v, rfl⟩, hp0⟩ ?_ ?_` and prove the remaining obligations. Introduce and unpack `u _ ⟨y₁, y₂, v, rfl⟩`. Take `⟨x', h1, h2⟩` from `hxu u`.

Conclude with `⟨_, _, _, by rw [← h2, ← hp _ h1 _ (hBU _ _ _), hB.inf x']⟩`. Introduce and unpack `_ ⟨y₁, y₂, v, rfl⟩ L`. Use `hexp _ _ (fun z => hBS _ _ _) (fun g => hB.le k x hc y₁ y₂ v g) (L ∘ₗ p)` as an intermediate fact. Use `this using 2 with z` and compare the differences between its conclusion and the goal. Rewrite using `[← (hx z).2, ← hp _ (hx z).1 _ (hBU _ _ _), hB.inf (x z)]`.

Both sides reduce to the same expression. Choose the witnesses or unpack the hypotheses as in `⟨y, v', hv'⟩ : ∃ y v', B 1 y v' ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Take `⟨u, b, hb, rfl⟩` from `hQR a y₁`.

Take `⟨x', -, h2⟩` from `hxu u`. Establish `e1` using `hB.inf x' 1 ((cEmb τ x'.1)⁻¹ * y₂) (W.rep x'⁻¹ v)`. Rewrite `e1` using `[h, map_zero, mul_one, mul_inv_cancel_left, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply, h2]`. Rewrite `hv` using `[hB.up b hb, ← e1, smul_zero]`. Conclude with `hv rfl`.

Take `⟨p, hp0, hp⟩` from `hEP E a τ U hU κ hκ _ (hBU 1 y v') hv'`. Use `(hBd a k κ _).2 _ hp0 fun L => ?_` and prove the remaining obligations. Establish `h1` using `hexp _ _ (fun z => hBS _ _ _) (fun g => hB.ge k x hc y v' g) (L ∘ₗ p)`. Establish `h2` using `hEB.2.1 _ _ _ _ (hEB.2.2.2.1 1 (psum ν k)).2 h1`. Rewrite using `[sub_eq_add_neg]`.

Use `h2 using 2 with z` and compare the differences between its conclusion and the goal. Rewrite using `[← (hx z).2, ← hp _ (hx z).1 _ (hBU _ _ _), hB.inf (x z), (hx z).2, mul_one, ← one_mul (tor a k z), hB.up _ (hTor a k z).1, (hTor a k z).2.2.1, map_smul, map_smul, one_mul, one_mul]`. Both sides reduce to the same expression.
-/
theorem famSum_of : ExpBasic → EvLem → TorFacts → QR → WtBd → EmbProj → FamSum := by
  intro hEB hEv hTor hQR hBd hEP E _ _ _ a τ W K ν d B hB U hU hBU hne κ hκ k
  obtain ⟨e, he⟩ := GlobalTheory.T.archimedeanUnitaryPoints_equiv_unitaryGroup E a τ
  have hx : ∀ u : Matrix.unitaryGroup (Fin a) ℂ, ∃ x : infU E a, x.1 ∈ embU a τ ∧ cEmb τ x.1 = unitaryIncl a u := fun u => by
    have h := he (e.symm u)
    rw [e.apply_symm_apply] at h
    exact ⟨⟨(e.symm u).1, (Subgroup.mem_inf.1 (e.symm u).2).1⟩, (e.symm u).2, h.symm⟩
  choose x hx using fun z : Circle => (show ∃ x : infU E a, x.1 ∈ embU a τ ∧ cEmb τ x.1 = tor a k z by
    obtain ⟨u, hu⟩ := (hTor a k z).2.1
    rw [← hu]
    exact hx u)
  rename_i hxu
  have hc : IsCirc τ k x := hx
  obtain ⟨S, hS, hBS⟩ := hB.fin
  have hexp : ∀ (T : Submodule ℂ (Circle → ℂ)) (Φ : Circle → UA E a → ℂ), (∀ z, Φ z ∈ S) → (∀ g, (fun z => Φ z g) ∈ T) →
      ∀ L : (UA E a → ℂ) →ₗ[ℂ] ℂ, (fun z => L (Φ z)) ∈ T := fun T Φ h1 h2 L =>
    hEv S (UA E a) Circle (fun g => LinearMap.proj g ∘ₗ S.subtype) (fun m hm => Subtype.ext (funext hm)) T
      (fun z => ⟨Φ z, h1 z⟩) h2 (L ∘ₗ S.subtype)
  obtain ⟨y₁, y₂, v, hv⟩ := hne
  constructor
  · obtain ⟨p, hp0, hp⟩ := hEP E a τ U hU κ hκ _ (hBU y₁ y₂ v) hv
    refine (hBd a k κ _).1 {w | ∃ y₁ y₂ v, w = p (B y₁ y₂ v)} ⟨_, ⟨y₁, y₂, v, rfl⟩, hp0⟩ ?_ ?_
    · rintro u _ ⟨y₁, y₂, v, rfl⟩
      obtain ⟨x', h1, h2⟩ := hxu u
      exact ⟨_, _, _, by rw [← h2, ← hp _ h1 _ (hBU _ _ _), hB.inf x']⟩
    · rintro _ ⟨y₁, y₂, v, rfl⟩ L
      have := hexp _ _ (fun z => hBS _ _ _) (fun g => hB.le k x hc y₁ y₂ v g) (L ∘ₗ p)
      convert this using 2 with z
      rw [← (hx z).2, ← hp _ (hx z).1 _ (hBU _ _ _), hB.inf (x z)]
      rfl
  · obtain ⟨y, v', hv'⟩ : ∃ y v', B 1 y v' ≠ 0 := by
      by_contra h
      push_neg at h
      obtain ⟨u, b, hb, rfl⟩ := hQR a y₁
      obtain ⟨x', -, h2⟩ := hxu u
      have e1 := hB.inf x' 1 ((cEmb τ x'.1)⁻¹ * y₂) (W.rep x'⁻¹ v)
      rw [h, map_zero, mul_one, mul_inv_cancel_left, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
        Module.End.one_apply, h2] at e1
      rw [hB.up b hb, ← e1, smul_zero] at hv
      exact hv rfl
    obtain ⟨p, hp0, hp⟩ := hEP E a τ U hU κ hκ _ (hBU 1 y v') hv'
    refine (hBd a k κ _).2 _ hp0 fun L => ?_
    have h1 := hexp _ _ (fun z => hBS _ _ _) (fun g => hB.ge k x hc y v' g) (L ∘ₗ p)
    have h2 := hEB.2.1 _ _ _ _ (hEB.2.2.2.1 1 (psum ν k)).2 h1
    rw [sub_eq_add_neg]
    convert h2 using 2 with z
    rw [← (hx z).2, ← hp _ (hx z).1 _ (hBU _ _ _), hB.inf (x z), (hx z).2, mul_one, ← one_mul (tor a k z),
      hB.up _ (hTor a k z).1, (hTor a k z).2.2.1, map_smul, map_smul, one_mul, one_mul]
    rfl

end UpperTheory.Gal.Wt

end
