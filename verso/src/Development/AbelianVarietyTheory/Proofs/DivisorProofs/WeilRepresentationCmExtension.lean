import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSubmoduleSupNeTop
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSubAug
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSBZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniqueMaximal

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.Published
open scoped TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.HoweAllPlaces

/- English proof (translation)
Assume the negation of the conclusion as `hb`. Take `⟨x, hx, hx0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hb`. Choose the witnesses or unpack the hypotheses as in `⟨p, hp⟩ : ∃ p, x p ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`.

Conclude with `hx0 (funext h)`. Apply `hne` to reduce the goal to its premises. Use `le_antisymm hP fun y _ => ?_` and prove the remaining obligations. Establish `: y = (y p / x p) • x`. Use function extensionality and compare the values at `q`.

Rewrite using `[Subsingleton.elim q p, Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ hp]`. Rewrite using `[this]`. Conclude with `P.smul_mem _ hx`.
-/
theorem eq_bot_of_subsingleton {D : Type} [Subsingleton D] (S P : Submodule ℂ (D → ℂ)) (hP : P ≤ S) (hne : P ≠ S) :
    P = ⊥ := by
  by_contra hb
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
  obtain ⟨p, hp⟩ : ∃ p, x p ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx0 (funext h)
  apply hne
  refine le_antisymm hP fun y _ => ?_
  have : y = (y p / x p) • x := by
    funext q
    rw [Subsingleton.elim q p, Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ hp]
  rw [this]
  exact P.smul_mem _ hx

end GlobalTheory.HoweAllPlaces

open GlobalTheory.HoweAllPlaces in

/- English proof (translation)
Introduce `hP hHD hMin F E _ _ _ _ _ σ hcm n d X W M ψ χX χW om hψ hX hXd hW hWd hrX hrW hhX hhW hweil v N N' hN hN'`. Establish `key : ThetaSub om v (N ⊔ N') → N ⊔ N' ≠ SB _ → N = N'`. Introduce `h1 h2`. Establish `a` using `hN.2 ⟨h1, h2⟩ le_sup_left`. Establish `b` using `hN'.2 ⟨h1, h2⟩ le_sup_right`.

Conclude with `le_antisymm (le_sup_left.trans b) (le_sup_right.trans a)`. Establish `hNS : N ≤ SB _` using `hN.1.1.2.1`. Establish `hNS' : N' ≤ SB _` using `hN'.1.1.2.1`. Break down `isEmpty_or_nonempty (E →ₐ[F] Fv F v) with hs | hs` into its components or cases. Conclude with `GlobalTheory.HoweNonsplit.unique_maximal hP hHD F E σ hcm n d X W M ψ χX χW om hψ hX hXd hW hWd hrX hrW hhX hhW hweil v hs N N' hN hN'`.

Break down `Nat.eq_zero_or_pos n with hn | hn` into its components or cases. Substitute `hn` using the available equality. Rewrite using `[eq_bot_of_subsingleton _ N hNS hN.1.2, eq_bot_of_subsingleton _ N' hNS' hN'.1.2]`. Break down `Nat.eq_zero_or_pos d with hd | hd` into its components or cases. Substitute `hd` using the available equality.

Rewrite using `[eq_bot_of_subsingleton _ N hNS hN.1.2, eq_bot_of_subsingleton _ N' hNS' hN'.1.2]`. Take `⟨χ, ι, hχ, hbij, htr⟩` from `GlobalTheory.SplitTransportPair.transport hP F E σ hcm n d X W M ψ χX χW om hψ hX hXd hW hWd hrX hrW hhX hhW hweil hn hd v hs`. Establish `hsN` using `(htr N hNS).1 hN.1.1`. Establish `hsN'` using `(htr N' hNS').1 hN'.1.1`. Establish `h1 : ThetaSub om v (N ⊔ N')` using `(htr _ (sup_le hNS hNS')).2 (by rw [Submodule.map_sup]; exact hsN.sup hsN')`.

Establish `hSB : (SB (Fin n × Fin d → Fv F v)).map ι = GlobalTheory.SplitWeil.SB _`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `hbij.mapsTo hx`.

Introduce `hy`. Take `⟨x, hx, rfl⟩` from `hbij.surjOn hy`. Conclude with `⟨x, hx, rfl⟩`. Establish `hne : ∀ P : Submodule ℂ ((Fin n × Fin d → Fv F v) → ℂ), P ≤ SB _ → P ≠ SB _ → P.map ι ≠ GlobalTheory.SplitWeil.SB _`. Introduce `P hP1 hP2 he`.

Apply `hP2` to reduce the goal to its premises. Use `le_antisymm hP1 fun x hx => ?_` and prove the remaining obligations. Establish `: ι x ∈ P.map ι` using `by rw [he, ← hSB]; exact Submodule.mem_map_of_mem hx`. Take `⟨y, hy, hyx⟩` from `this`. Rewrite `hy` using `[hbij.injOn (hP1 hy) hx hyx]`. Then use the resulting hypothesis.

Use `key h1 fun he => ?_` and prove the remaining obligations. Apply `GlobalTheory.ThetaGLSub.SumProper.main hP hMin _ n d hn hd χ hχ _ _ hsN hsN' (hne N hNS hN.1.2) (hne N' hNS' hN'.1.2)` to reduce the goal to its premises. Rewrite using `[← Submodule.map_sup, he, hSB]`.
-/
theorem GlobalTheory.HoweAllPlaces.main : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.Published.HoweDualityUnitary → GlobalTheory.Published.MinguezThetaGL → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ v : Pl F, ∀ N N', Maximal (fun P => ThetaSub om v P ∧ P ≠ SB _) N → Maximal (fun P => ThetaSub om v P ∧ P ≠ SB _) N' → N = N' := by
  intro hP hHD hMin F E _ _ _ _ _ σ hcm n d X W M ψ χX χW om hψ hX hXd hW hWd hrX hrW hhX hhW hweil v N N' hN hN'
  have key : ThetaSub om v (N ⊔ N') → N ⊔ N' ≠ SB _ → N = N' := by
    intro h1 h2
    have a := hN.2 ⟨h1, h2⟩ le_sup_left
    have b := hN'.2 ⟨h1, h2⟩ le_sup_right
    exact le_antisymm (le_sup_left.trans b) (le_sup_right.trans a)
  have hNS : N ≤ SB _ := hN.1.1.2.1
  have hNS' : N' ≤ SB _ := hN'.1.1.2.1
  rcases isEmpty_or_nonempty (E →ₐ[F] Fv F v) with hs | hs
  ·
    exact GlobalTheory.HoweNonsplit.unique_maximal hP hHD F E σ hcm n d X W M ψ χX χW om hψ hX hXd hW hWd hrX hrW hhX hhW hweil v hs N N' hN hN'
  · rcases Nat.eq_zero_or_pos n with hn | hn
    ·
      subst hn
      rw [eq_bot_of_subsingleton _ N hNS hN.1.2, eq_bot_of_subsingleton _ N' hNS' hN'.1.2]
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd
      rw [eq_bot_of_subsingleton _ N hNS hN.1.2, eq_bot_of_subsingleton _ N' hNS' hN'.1.2]

    obtain ⟨χ, ι, hχ, hbij, htr⟩ := GlobalTheory.SplitTransportPair.transport hP F E σ hcm n d X W M ψ χX χW om hψ hX hXd hW hWd hrX hrW hhX hhW hweil hn hd v hs
    have hsN := (htr N hNS).1 hN.1.1
    have hsN' := (htr N' hNS').1 hN'.1.1
    have h1 : ThetaSub om v (N ⊔ N') := (htr _ (sup_le hNS hNS')).2 (by rw [Submodule.map_sup]; exact hsN.sup hsN')
    have hSB : (SB (Fin n × Fin d → Fv F v)).map ι = GlobalTheory.SplitWeil.SB _ := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact hbij.mapsTo hx
      · intro hy
        obtain ⟨x, hx, rfl⟩ := hbij.surjOn hy
        exact ⟨x, hx, rfl⟩
    have hne : ∀ P : Submodule ℂ ((Fin n × Fin d → Fv F v) → ℂ), P ≤ SB _ → P ≠ SB _ → P.map ι ≠ GlobalTheory.SplitWeil.SB _ := by
      intro P hP1 hP2 he
      apply hP2
      refine le_antisymm hP1 fun x hx => ?_
      have : ι x ∈ P.map ι := by rw [he, ← hSB]; exact Submodule.mem_map_of_mem hx
      obtain ⟨y, hy, hyx⟩ := this
      rwa [hbij.injOn (hP1 hy) hx hyx] at hy
    refine key h1 fun he => ?_
    apply GlobalTheory.ThetaGLSub.SumProper.main hP hMin _ n d hn hd χ hχ _ _ hsN hsN' (hne N hNS hN.1.2) (hne N' hNS' hN'.1.2)
    rw [← Submodule.map_sup, he, hSB]
