import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSkewSignature
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripSizesSum
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SmGL

/- English proof (translation)
Introduce `G H V _ _ _ _ ρ χ φ n S hS h0 htop W' Vy _ _ _ _ Q Y hQ F hF`. Take `⟨T, f, hf⟩` from `hQ`. Set `g : T.toSubmodule →ₗ[ℂ] Vy` to `F.toLinearMap ∘ₗ f.toLinearMap`. Establish `hg : ∃ x, g x ≠ 0`. Assume the negation of the conclusion as `h`.

Use `push_neg at h`. Apply `hF` to reduce the goal to its premises. Apply `Representation.IntertwiningMap.ext` to reduce the goal to its premises. Use extensionality with `w`. Take `⟨x, rfl⟩` from `hf w`.

Conclude with `h x`. Set `P : ℕ → Prop` to `fun k => ∃ hk : k < n + 1, ∃ x : T.toSubmodule, (x : V) ∈ (S ⟨k, hk⟩).toSubmodule ∧ g x ≠ 0`. Establish `hex : ∃ k, P k`. Take `⟨x, hx⟩` from `hg`. Use `⟨n, Nat.lt_succ_self n, x, ?_, hx⟩` and prove the remaining obligations.

Establish `: S ⟨n, Nat.lt_succ_self n⟩ = ⊤` using `htop`. Rewrite using `[this]`. Discharge the goal by the elementary cases of `trivial`. Establish `hmin : ∀ k < Nat.find hex, ¬ P k` using `fun k hk => Nat.find_min hex hk`. Take `⟨hun, x0, hx0S, hx0⟩` from `Nat.find_spec hex`.

Establish `hu0 : Nat.find hex ≠ 0`. Introduce `h`. Establish `hS0 : S ⟨Nat.find hex, hun⟩ = ⊥`. Rewrite using `[← h0]`. Use `congr 1`.

Conclude with `Fin.ext h`. Rewrite `hx0S` using `[hS0]`. Establish `hx : x0 = 0` using `Subtype.ext ((Submodule.mem_bot ℂ).1 hx0S)`. Conclude with `hx0 (by rw [hx, map_zero])`. Take `⟨t0, ht0⟩` from `Nat.exists_eq_succ_of_ne_zero hu0`.

Set `t : Fin n` to `⟨t0, by omega⟩`. Establish `hts : t.succ = ⟨Nat.find hex, hun⟩` using `Fin.ext (by simp [t, ht0])`. Establish `hvan : ∀ x : T.toSubmodule, (x : V) ∈ (S t.castSucc).toSubmodule → g x = 0`. Introduce `x hx`. Assume the negation of the conclusion as `hne`.

Conclude with `hmin t0 (by omega) ⟨by omega, x, hx, hne⟩`. Set `M` to `(S t.succ).toSubmodule`. Set `N : Submodule ℂ M` to `(S t.castSucc).toSubmodule.comap M.subtype`. Set `B : Submodule ℂ M` to `T.toSubmodule.comap M.subtype`. Set `Rm : Representation ℂ H M` to `(twist (S t.succ).toRepresentation χ).comp φ`.

Set `Bs : Subrepresentation Rm` to `⟨B, fun h v hv => T.apply_mem_toSubmodule h hv⟩`. Set `NB : Submodule ℂ B` to `N.comap B.subtype`. Establish `hNB : ∀ h : H, NB ≤ NB.comap (Bs.toRepresentation h)`. Introduce `h x hx`. Conclude with `Submodule.smul_mem _ _ ((S t.castSucc).apply_mem_toSubmodule (φ h) hx)`.

Set `Q' : Representation ℂ H (B ⧸ NB)` to `Bs.toRepresentation.quotient NB hNB`. Use `⟨t, B ⧸ NB, inferInstance, inferInstance, Q', ?_, ?_⟩` and prove the remaining obligations. Set `ι : Q'.IntertwiningMap ((twist (subQuot (S t.succ) (S t.castSucc)) χ).comp φ)` to `⟨NB.mapQ N B.subtype le_rfl, fun h => by`. Use extensionality with `b`. Use the proof step `rfl⟩`.

Use `IsSubquotient.of_injective ι ?_` and prove the remaining obligations. Introduce `a b hab`. Proceed by induction on `a using Submodule.Quotient.induction_on with | _ a => ?_`. Proceed by induction on `b using Submodule.Quotient.induction_on with | _ b => ?_`. Express the relevant statement in the definitionally equal form `NB.mapQ N B.subtype le_rfl (Submodule.Quotient.mk a) = NB.mapQ N B.subtype le_rfl (Submodule.Quotient.mk b) at hab`.

Rewrite `hab` using `[Submodule.mapQ_apply, Submodule.mapQ_apply, Submodule.Quotient.eq]`. Rewrite using `[Submodule.Quotient.eq]`. Simplify `hab` using `[NB]`. Set `j : B →ₗ[ℂ] T.toSubmodule` to `LinearMap.codRestrict T.toSubmodule (M.subtype ∘ₗ B.subtype) (fun b => b.2)`. Set `ψ : B →ₗ[ℂ] Vy` to `g ∘ₗ j`.

Establish `hψ : NB ≤ LinearMap.ker ψ`. Introduce `x hx`. Conclude with `hvan (j x) hx`. Set `F' : Q'.IntertwiningMap Y` to `⟨NB.liftQ ψ hψ, fun h => by`. Use extensionality with `b`.

Express the relevant statement in the definitionally equal form `F (f (T.toRepresentation h (j b))) = Y h (F (f (j b)))`. Rewrite using `[f.isIntertwining, F.isIntertwining]⟩`. Use `⟨F', fun hF0 => ?_⟩` and prove the remaining obligations. Establish `hx0S' : (x0 : V) ∈ M`. Express the relevant statement in the definitionally equal form `(x0 : V) ∈ (S t.succ).toSubmodule`.

Rewrite using `[hts]`. Conclude with `hx0S`. Set `b0 : B` to `⟨⟨x0, hx0S'⟩, x0.2⟩`. Establish `h1 : F' (Submodule.Quotient.mk b0) = 0` using `by rw [hF0]; rfl`. Apply `hx0` to reduce the goal to its premises.

Conclude with `h1`.
-/
theorem exists_step_subquotient_ne_zero_of_filtration : ∀ {G H V : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (χ : G →* ℂˣ) (φ : H →* G) (n : ℕ) (S : Fin (n + 1) → Subrepresentation ρ), Monotone S → S 0 = ⊥ →
    S (Fin.last n) = ⊤ → ∀ {W' Vy : Type} [AddCommGroup W'] [Module ℂ W'] [AddCommGroup Vy] [Module ℂ Vy]
    (Q : Representation ℂ H W') (Y : Representation ℂ H Vy),
    GlobalTheory.SmGL.IsSubquotient Q ((GlobalTheory.SmGL.twist ρ χ).comp φ) → ∀ F : Q.IntertwiningMap Y, F ≠ 0 →
    ∃ (t : Fin n) (V' : Type) (_ : AddCommGroup V') (_ : Module ℂ V') (Q' : Representation ℂ H V'),
      GlobalTheory.SmGL.IsSubquotient Q' ((GlobalTheory.SmGL.twist (GlobalTheory.SmGL.subQuot (S t.succ) (S t.castSucc)) χ).comp φ) ∧
      ∃ F' : Q'.IntertwiningMap Y, F' ≠ 0 := by
  intro G H V _ _ _ _ ρ χ φ n S hS h0 htop W' Vy _ _ _ _ Q Y hQ F hF
  classical
  obtain ⟨T, f, hf⟩ := hQ
  let g : T.toSubmodule →ₗ[ℂ] Vy := F.toLinearMap ∘ₗ f.toLinearMap
  have hg : ∃ x, g x ≠ 0 := by
    by_contra h
    push_neg at h
    apply hF
    apply Representation.IntertwiningMap.ext
    ext w
    obtain ⟨x, rfl⟩ := hf w
    exact h x
  let P : ℕ → Prop := fun k => ∃ hk : k < n + 1, ∃ x : T.toSubmodule,
    (x : V) ∈ (S ⟨k, hk⟩).toSubmodule ∧ g x ≠ 0
  have hex : ∃ k, P k := by
    obtain ⟨x, hx⟩ := hg
    refine ⟨n, Nat.lt_succ_self n, x, ?_, hx⟩
    have : S ⟨n, Nat.lt_succ_self n⟩ = ⊤ := htop
    rw [this]
    trivial
  have hmin : ∀ k < Nat.find hex, ¬ P k := fun k hk => Nat.find_min hex hk
  obtain ⟨hun, x0, hx0S, hx0⟩ := Nat.find_spec hex
  have hu0 : Nat.find hex ≠ 0 := by
    intro h
    have hS0 : S ⟨Nat.find hex, hun⟩ = ⊥ := by
      rw [← h0]; congr 1; exact Fin.ext h
    rw [hS0] at hx0S
    have hx : x0 = 0 := Subtype.ext ((Submodule.mem_bot ℂ).1 hx0S)
    exact hx0 (by rw [hx, map_zero])
  obtain ⟨t0, ht0⟩ := Nat.exists_eq_succ_of_ne_zero hu0
  let t : Fin n := ⟨t0, by omega⟩
  have hts : t.succ = ⟨Nat.find hex, hun⟩ := Fin.ext (by simp [t, ht0])
  have hvan : ∀ x : T.toSubmodule, (x : V) ∈ (S t.castSucc).toSubmodule → g x = 0 := by
    intro x hx
    by_contra hne
    exact hmin t0 (by omega) ⟨by omega, x, hx, hne⟩
  let M := (S t.succ).toSubmodule
  let N : Submodule ℂ M := (S t.castSucc).toSubmodule.comap M.subtype
  let B : Submodule ℂ M := T.toSubmodule.comap M.subtype
  let Rm : Representation ℂ H M := (twist (S t.succ).toRepresentation χ).comp φ
  let Bs : Subrepresentation Rm := ⟨B, fun h v hv => T.apply_mem_toSubmodule h hv⟩
  let NB : Submodule ℂ B := N.comap B.subtype
  have hNB : ∀ h : H, NB ≤ NB.comap (Bs.toRepresentation h) := by
    intro h x hx
    exact Submodule.smul_mem _ _ ((S t.castSucc).apply_mem_toSubmodule (φ h) hx)
  let Q' : Representation ℂ H (B ⧸ NB) := Bs.toRepresentation.quotient NB hNB
  refine ⟨t, B ⧸ NB, inferInstance, inferInstance, Q', ?_, ?_⟩
  · let ι : Q'.IntertwiningMap ((twist (subQuot (S t.succ) (S t.castSucc)) χ).comp φ) :=
      ⟨NB.mapQ N B.subtype le_rfl, fun h => by
        ext b
        rfl⟩
    refine IsSubquotient.of_injective ι ?_
    intro a b hab
    induction a using Submodule.Quotient.induction_on with | _ a => ?_
    induction b using Submodule.Quotient.induction_on with | _ b => ?_
    change NB.mapQ N B.subtype le_rfl (Submodule.Quotient.mk a)
      = NB.mapQ N B.subtype le_rfl (Submodule.Quotient.mk b) at hab
    rw [Submodule.mapQ_apply, Submodule.mapQ_apply, Submodule.Quotient.eq] at hab
    rw [Submodule.Quotient.eq]
    simpa [NB] using hab
  · let j : B →ₗ[ℂ] T.toSubmodule :=
      LinearMap.codRestrict T.toSubmodule (M.subtype ∘ₗ B.subtype) (fun b => b.2)
    let ψ : B →ₗ[ℂ] Vy := g ∘ₗ j
    have hψ : NB ≤ LinearMap.ker ψ := by
      intro x hx
      exact hvan (j x) hx
    let F' : Q'.IntertwiningMap Y := ⟨NB.liftQ ψ hψ, fun h => by
      ext b
      change F (f (T.toRepresentation h (j b))) = Y h (F (f (j b)))
      rw [f.isIntertwining, F.isIntertwining]⟩
    refine ⟨F', fun hF0 => ?_⟩
    have hx0S' : (x0 : V) ∈ M := by
      change (x0 : V) ∈ (S t.succ).toSubmodule
      rw [hts]; exact hx0S
    let b0 : B := ⟨⟨x0, hx0S'⟩, x0.2⟩
    have h1 : F' (Submodule.Quotient.mk b0) = 0 := by rw [hF0]; rfl
    apply hx0
    exact h1

end GlobalTheory.SmGL
