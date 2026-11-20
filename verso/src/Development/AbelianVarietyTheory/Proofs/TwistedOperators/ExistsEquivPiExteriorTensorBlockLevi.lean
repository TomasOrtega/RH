import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmRep
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenNormalisedSubgroupSubset
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContractsTensorProductChain
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchurAdmissibleAlt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivExteriorTensorOfIrreducibleProdRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InjectiveTensorLiftEquivariantMapsOfIrreducible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIrreducibleSmoothQuotient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIrreducibleSecondFactorOfIrreducibleProduct
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.CuspRep.LocEx Topology
open scoped TensorProduct

namespace GlobalTheory.LeviFactor

section General

variable {G H V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H] [TopologicalSpace H]
  [IsTopologicalGroup H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def FinFixed (ρ : Representation ℂ G V) : Prop :=
  ∀ K : Subgroup G, IsOpen (K : Set G) → FiniteDimensional ℂ (fixed ρ K)

omit [IsTopologicalGroup G] [IsTopologicalGroup H] in

/- English proof (translation)
Introduce `K hK`. Use `h (K.map φ) (hφ _ hK)` as an intermediate fact. Use `Submodule.finiteDimensional_of_le (S₂ := fixed ρ (K.map φ)) fun v hv => mem_fix.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `mem_fix.1 hv x hx`.
-/
theorem FinFixed.comp {ρ : Representation ℂ G V} (h : FinFixed ρ) (φ : H →* G) (hφ : IsOpenMap φ) :
    FinFixed (ρ.comp φ : Representation ℂ H V) := by
  intro K hK
  have := h (K.map φ) (hφ _ hK)
  refine Submodule.finiteDimensional_of_le (S₂ := fixed ρ (K.map φ)) fun v hv => mem_fix.2 ?_
  rintro _ ⟨x, hx, rfl⟩
  exact mem_fix.1 hv x hx

/- English proof (translation)
Take `⟨h1, h2⟩` from `(hasFiniteLength_iff_wellFounded ρ).1 hl`. Establish `key : ∀ S : Subrepresentation ρ, FiniteDimensional ℂ (fixed S.toRepresentation K)`. Introduce `S`. Proceed by induction on `S using WellFoundedLT.induction with`. Consider the case `ind S ih`.

Break down `subsingleton_or_nontrivial S.toSubmodule with h0 | h0` into its components or cases. Use `infer_instance`. Set `ι : S.toRepresentation.IntertwiningMap ρ` to `⟨S.toSubmodule.subtype, fun g => rfl⟩`. Establish `hι : Function.Injective ι` using `Subtype.val_injective`. Establish `hs : IsSmooth S.toRepresentation` using `(IsSubquotient.of_injective ι hι).isSmooth hρ`.

Establish `hf : HasFiniteLength S.toRepresentation` using `IsFiniteLength.of_injective hl (f := Representation.IntertwiningMap.equivLinearMapAsModule _ _ ι) hι`. Take `⟨Y, _, _, τ, hτs, hτi, q, hq⟩` from `IrrQuot.exists_irreducible_smooth_quotient _ hs hf h0`. Establish `hfin` using `(hG Y τ hτs hτi).2 K hKo hKc`. Set `T : Subrepresentation ρ` to `GlobalTheory.JHMult.subMap ι q.ker`. Establish `hTS : T < S`.

Use `lt_of_le_of_ne (by rintro _ ⟨v, -, rfl⟩; exact v.2) fun e => ?_` and prove the remaining obligations. Use `((GlobalTheory.CuspRep.isIrreducible_iff τ).1 hτi).1` as an intermediate fact. Take `⟨y, hy⟩` from `exists_ne (0 : Y)`. Take `⟨v, rfl⟩` from `hq y`. Establish `hv : (v : V) ∈ T.toSubmodule` using `by rw [e]; exact v.2`.

Take `⟨w, hw, hwv⟩` from `hv`. Take `rfl : w = v` from `Subtype.ext hwv`. Conclude with `hy hw`. Establish `hT` using `ih T hTS`. Set `f : fixed S.toRepresentation K →ₗ[ℂ] fixed τ K` to `q.toLinearMap.restrict fun v hv => mem_fix.2 fun k hk => by show τ k (q v) = q v`.

Rewrite using `[← q.isIntertwining, mem_fix.1 hv k hk]`. Establish `hker : FiniteDimensional ℂ (LinearMap.ker f)`. Set `j : LinearMap.ker f →ₗ[ℂ] fixed T.toRepresentation K` to `{ toFun := fun v => ⟨⟨v.1.1.1, v.1.1, congrArg Subtype.val v.2, rfl⟩, mem_fix.2 fun k hk => Subtype.ext (congrArg (fun z : S.toSubmodule => (z : V)) (mem_fix.1 v.1.2 k hk))⟩ map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl }`. Conclude with `FiniteDimensional.of_injective j fun a b e => Subtype.ext (Subtype.ext (Subtype.ext (congrArg (fun z => z.1.1) e)))`. Conclude with `Module.Finite.of_exact (f := (LinearMap.ker f).subtype) (g := f.rangeRestrict) (by rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, Submodule.range_subtype]) f.surjective_rangeRestrict`.

Use `key ⊤` as an intermediate fact. Set `j : fixed ρ K →ₗ[ℂ] fixed (⊤ : Subrepresentation ρ).toRepresentation K` to `{ toFun := fun v => ⟨⟨v.1, trivial⟩, mem_fix.2 fun k hk => Subtype.ext (mem_fix.1 v.2 k hk)⟩ map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl }`. Conclude with `FiniteDimensional.of_injective j fun a b e => Subtype.ext (congrArg (fun z => z.1.1) e)`.
-/
theorem finiteDimensional_fixed_of_hasFiniteLength
    (hG : ∀ (Y : Type) [AddCommGroup Y] [Module ℂ Y] (π : Representation ℂ G Y),
      IsSmooth π → π.IsIrreducible → IsAdmissible π)
    {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) (hl : HasFiniteLength ρ) (K : Subgroup G)
    (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G)) : FiniteDimensional ℂ (fixed ρ K) := by
  obtain ⟨h1, h2⟩ := (hasFiniteLength_iff_wellFounded ρ).1 hl
  have key : ∀ S : Subrepresentation ρ, FiniteDimensional ℂ (fixed S.toRepresentation K) := by
    intro S
    induction S using WellFoundedLT.induction with
    | ind S ih =>
    rcases subsingleton_or_nontrivial S.toSubmodule with h0 | h0
    · infer_instance
    let ι : S.toRepresentation.IntertwiningMap ρ := ⟨S.toSubmodule.subtype, fun g => rfl⟩
    have hι : Function.Injective ι := Subtype.val_injective
    have hs : IsSmooth S.toRepresentation := (IsSubquotient.of_injective ι hι).isSmooth hρ
    have hf : HasFiniteLength S.toRepresentation :=
      IsFiniteLength.of_injective hl
        (f := Representation.IntertwiningMap.equivLinearMapAsModule _ _ ι) hι
    obtain ⟨Y, _, _, τ, hτs, hτi, q, hq⟩ := IrrQuot.exists_irreducible_smooth_quotient _ hs hf h0
    have hfin := (hG Y τ hτs hτi).2 K hKo hKc
    let T : Subrepresentation ρ := GlobalTheory.JHMult.subMap ι q.ker
    have hTS : T < S := by
      refine lt_of_le_of_ne (by rintro _ ⟨v, -, rfl⟩; exact v.2) fun e => ?_
      have := ((GlobalTheory.CuspRep.isIrreducible_iff τ).1 hτi).1
      obtain ⟨y, hy⟩ := exists_ne (0 : Y)
      obtain ⟨v, rfl⟩ := hq y
      have hv : (v : V) ∈ T.toSubmodule := by rw [e]; exact v.2
      obtain ⟨w, hw, hwv⟩ := hv
      obtain rfl : w = v := Subtype.ext hwv
      exact hy hw
    have hT := ih T hTS
    let f : fixed S.toRepresentation K →ₗ[ℂ] fixed τ K :=
      q.toLinearMap.restrict fun v hv => mem_fix.2 fun k hk => by
        show τ k (q v) = q v
        rw [← q.isIntertwining, mem_fix.1 hv k hk]
    have hker : FiniteDimensional ℂ (LinearMap.ker f) := by
      let j : LinearMap.ker f →ₗ[ℂ] fixed T.toRepresentation K :=
        { toFun := fun v => ⟨⟨v.1.1.1, v.1.1, congrArg Subtype.val v.2, rfl⟩,
            mem_fix.2 fun k hk => Subtype.ext (congrArg (fun z : S.toSubmodule => (z : V)) (mem_fix.1 v.1.2 k hk))⟩
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      exact FiniteDimensional.of_injective j fun a b e =>
        Subtype.ext (Subtype.ext (Subtype.ext (congrArg (fun z => z.1.1) e)))
    exact Module.Finite.of_exact (f := (LinearMap.ker f).subtype) (g := f.rangeRestrict)
      (by rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, Submodule.range_subtype])
      f.surjective_rangeRestrict
  have := key ⊤
  let j : fixed ρ K →ₗ[ℂ] fixed (⊤ : Subrepresentation ρ).toRepresentation K :=
    { toFun := fun v => ⟨⟨v.1, trivial⟩, mem_fix.2 fun k hk => Subtype.ext (mem_fix.1 v.2 k hk)⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact FiniteDimensional.of_injective j fun a b e => Subtype.ext (congrArg (fun z => z.1.1) e)

/- English proof (translation)
Establish `wd : ∀ (p p' : P) (c c' : G), c ∈ K → c' ∈ K → (p : G) * c = p' * c' → σ p u = σ p' u`. Introduce `p p' c c' hc hc' h`. Establish `hm : ((p'⁻¹ * p : P) : G) ∈ K`. Establish `: ((p'⁻¹ * p : P) : G) = c' * c⁻¹`. Simplify using `only [Subgroup.coe_mul, Subgroup.coe_inv]`.

Rewrite using `[inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h, mul_inv_cancel_right]`. Rewrite using `[this]`. Conclude with `mul_mem hc' (inv_mem hc)`. Establish `h2` using `hfix _ hm`. Rewrite `h2` using `[map_mul, Module.End.mul_apply]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]`. Use `_ = σ p' u := by rw [h2]`. Set `F : G → W` to `fun g => if h : ∃ p : P, ∃ c ∈ K, g = (p : G) * c then σ h.choose u else 0`. Establish `hF : ∀ (p : P) (c : G), c ∈ K → F ((p : G) * c) = σ p u`.

Introduce `p c hc`. Establish `h : ∃ p' : P, ∃ c' ∈ K, (p : G) * c = (p' : G) * c'` using `⟨p, c, hc, rfl⟩`. Simplify using `only [F, dif_pos h]`. Take `⟨c', hc', e⟩` from `h.choose_spec`. Conclude with `wd _ _ _ _ hc' hc e.symm`.

Establish `hF0 : ∀ g, (¬ ∃ p : P, ∃ c ∈ K, g = (p : G) * c) → F g = 0` using `fun g h => by`. Simplify using `only [F, dif_neg h]`. Establish `hmem : F ∈ indSpace P σ`. Introduce `h g`. Distinguish the cases in `hg : ∃ p : P, ∃ c ∈ K, g = (p : G) * c`.

Take `⟨p, c, hc, rfl⟩` from `hg`. Rewrite using `[← mul_assoc, show (h : G) * p = ((h * p : P) : G) from rfl, hF _ _ hc, hF _ _ hc, map_mul, Module.End.mul_apply]`. Establish `: ¬ ∃ p : P, ∃ c ∈ K, (h : G) * g = (p : G) * c`. Introduce and unpack `⟨p, c, hc, e⟩`. Conclude with `hg ⟨h⁻¹ * p, c, hc, by rw [Subgroup.coe_mul, mul_assoc, ← e]; simp⟩`.

Rewrite using `[hF0 _ hg, hF0 _ this, map_zero]`. Establish `hK : ∀ c ∈ K, ind P σ c ⟨F, hmem⟩ = ⟨F, hmem⟩`. Introduce `c hc`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `x`.

Use `show F (x * c) = F x`. Distinguish the cases in `hx : ∃ p : P, ∃ c' ∈ K, x = (p : G) * c'`. Take `⟨p, c', hc', rfl⟩` from `hx`. Rewrite using `[mul_assoc, hF _ _ (mul_mem hc' hc), hF _ _ hc']`. Establish `: ¬ ∃ p : P, ∃ c' ∈ K, x * c = (p : G) * c'`.

Introduce and unpack `⟨p, c', hc', e⟩`. Conclude with `hx ⟨p, c' * c⁻¹, mul_mem hc' (inv_mem hc), by rw [← mul_assoc, ← e, mul_inv_cancel_right]⟩`. Rewrite using `[hF0 _ hx, hF0 _ this]`. Use `⟨⟨⟨F, hmem⟩, mem_smoothPart_of_nhds (Filter.mem_of_superset (hKo.mem_nhds K.one_mem) hK)⟩, mem_fix.2 fun c hc => Subtype.ext (hK c hc), ?_⟩` and prove the remaining obligations. Use `show F 1 = u`.

Use `hF 1 1 K.one_mem` as an intermediate fact. Simplify using `using this`.
-/
theorem exists_fixed_smInd_apply_one (P : Subgroup G) (σ : Representation ℂ P W) (K : Subgroup G)
    (hKo : IsOpen (K : Set G)) (u : W) (hfix : ∀ p : P, (p : G) ∈ K → σ p u = u) :
    ∃ f ∈ fixed (smInd P σ) K, f.1.1 1 = u := by
  classical
  have wd : ∀ (p p' : P) (c c' : G), c ∈ K → c' ∈ K → (p : G) * c = p' * c' → σ p u = σ p' u := by
    intro p p' c c' hc hc' h
    have hm : ((p'⁻¹ * p : P) : G) ∈ K := by
      have : ((p'⁻¹ * p : P) : G) = c' * c⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h, mul_inv_cancel_right]
      rw [this]; exact mul_mem hc' (inv_mem hc)
    have h2 := hfix _ hm
    rw [map_mul, Module.End.mul_apply] at h2
    calc σ p u = σ p' (σ p'⁻¹ (σ p u)) := by
          rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
      _ = σ p' u := by rw [h2]
  let F : G → W := fun g => if h : ∃ p : P, ∃ c ∈ K, g = (p : G) * c then σ h.choose u else 0
  have hF : ∀ (p : P) (c : G), c ∈ K → F ((p : G) * c) = σ p u := by
    intro p c hc
    have h : ∃ p' : P, ∃ c' ∈ K, (p : G) * c = (p' : G) * c' := ⟨p, c, hc, rfl⟩
    simp only [F, dif_pos h]
    obtain ⟨c', hc', e⟩ := h.choose_spec
    exact wd _ _ _ _ hc' hc e.symm
  have hF0 : ∀ g, (¬ ∃ p : P, ∃ c ∈ K, g = (p : G) * c) → F g = 0 := fun g h => by
    simp only [F, dif_neg h]
  have hmem : F ∈ indSpace P σ := by
    intro h g
    by_cases hg : ∃ p : P, ∃ c ∈ K, g = (p : G) * c
    · obtain ⟨p, c, hc, rfl⟩ := hg
      rw [← mul_assoc, show (h : G) * p = ((h * p : P) : G) from rfl, hF _ _ hc, hF _ _ hc, map_mul,
        Module.End.mul_apply]
    · have : ¬ ∃ p : P, ∃ c ∈ K, (h : G) * g = (p : G) * c := by
        rintro ⟨p, c, hc, e⟩
        exact hg ⟨h⁻¹ * p, c, hc, by rw [Subgroup.coe_mul, mul_assoc, ← e]; simp⟩
      rw [hF0 _ hg, hF0 _ this, map_zero]
  have hK : ∀ c ∈ K, ind P σ c ⟨F, hmem⟩ = ⟨F, hmem⟩ := by
    intro c hc
    apply Subtype.ext; funext x
    show F (x * c) = F x
    by_cases hx : ∃ p : P, ∃ c' ∈ K, x = (p : G) * c'
    · obtain ⟨p, c', hc', rfl⟩ := hx
      rw [mul_assoc, hF _ _ (mul_mem hc' hc), hF _ _ hc']
    · have : ¬ ∃ p : P, ∃ c' ∈ K, x * c = (p : G) * c' := by
        rintro ⟨p, c', hc', e⟩
        exact hx ⟨p, c' * c⁻¹, mul_mem hc' (inv_mem hc), by rw [← mul_assoc, ← e, mul_inv_cancel_right]⟩
      rw [hF0 _ hx, hF0 _ this]
  refine ⟨⟨⟨F, hmem⟩, mem_smoothPart_of_nhds (Filter.mem_of_superset (hKo.mem_nhds K.one_mem) hK)⟩,
    mem_fix.2 fun c hc => Subtype.ext (hK c hc), ?_⟩
  show F 1 = u
  have := hF 1 1 K.one_mem
  simpa using this

/- English proof (translation)
Take `⟨hnt, hinv⟩` from `(GlobalTheory.CuspRep.isIrreducible_iff τ).1 hirr`. Take `⟨x, hx0⟩` from `exists_ne (0 : V)`. Set `r : Representation ℂ H V` to `τ.comp (MonoidHom.inr G H)`. Establish `hc : Continuous (MonoidHom.inr G H)` using `continuous_const.prodMk continuous_id`. Establish `hc' : Continuous (MonoidHom.inl G H)` using `continuous_id.prodMk continuous_const`.

Establish `hρ : IsSmooth r` using `isSmooth_comp hs _ hc`. Set `Kc : Subgroup H` to `stab r x ⊓ C`. Establish `hKco : IsOpen (Kc : Set H)` using `(hρ x).inter hCo`. Establish `hKcc : IsCompact (Kc : Set H)` using `hCc.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ hKco) fun k hk => hk.2`. Establish `hxKc : x ∈ fixed r Kc` using `mem_fix.2 fun k hk => hk.1`.

Establish `hnull : nullPart r Kc = ⊥`. Break down `hinv (nullPart r Kc) (fun g y hy => by` into its components or cases. Take `⟨g, h⟩` from `g`. Rewrite using `[TensorFactor.apply_pair]`. Conclude with `nullPart_comm r Kc (τ (g, 1)) (fun h z => TensorFactor.commute_apply τ g h z) (nullPart_act r Kc h hy)) with h | h`.

Conclude with `h`. Conclude with `absurd (eq_zero_of_mem_nullPart hρ hKcc hxKc (h ▸ Submodule.mem_top)) hx0`. Establish `h2 : ∀ Y : Submodule ℂ V, (∀ g, ∀ v ∈ Y, r g v ∈ Y) → Y ⊓ fixed r Kc = ⊥ → Y = ⊥` using `fun Y hY h => le_bot_iff.1 (hnull ▸ le_nullPart hρ hKcc Y hY h)`. Set `l : Representation ℂ G V` to `τ.comp (MonoidHom.inl G H)`. Set `L : Subgroup G` to `stab l x`.

Establish `hLo : IsOpen (L : Set G)` using `isSmooth_comp hs _ hc' x`. Set `U : Submodule ℂ V` to `fixed l L`. Establish `hU : ∀ g, ∀ v ∈ U, r g v ∈ U` using `fun g v hv => mem_fix.2 fun k hk => by`. Express the relevant statement in the definitionally equal form `τ (k, 1) (τ (1, g) v) = τ (1, g) v`. Rewrite using `[TensorFactor.commute_apply]`.

Conclude with `congrArg _ (mem_fix.1 hv k hk)`. Establish `hU0 : U ≠ ⊥` using `(Submodule.ne_bot_iff _).2 ⟨x, mem_fix.2 fun k hk => hk, hx0⟩`. Establish `hfin : ∀ K' : Subgroup H, IsOpen (K' : Set H) → FiniteDimensional ℂ ↥(U ⊓ fixed r K')`. Introduce `K' hK'`. Use `hadm (L.prod K') (hLo.prod hK')` as an intermediate fact.

Use `Submodule.finiteDimensional_of_le (S₂ := fixed τ (L.prod K')) fun v hv => mem_fix.2 ?_` and prove the remaining obligations. Introduce and unpack `⟨g, h⟩ hk`. Rewrite using `[TensorFactor.apply_pair]`. Establish `e1 : τ (1, h) v = v` using `mem_fix.1 hv.2 h hk.2`. Rewrite using `[e1]`.

Conclude with `mem_fix.1 hv.1 g hk.1`. Take `⟨π, ⟨f, hf0, hf⟩, hπ⟩` from `exists_irred hρ hKco h2 U hU hU0 hfin`. Establish `hS : ∀ T : π.ρ.IntertwiningMap π.ρ, ∃ c : ℂ, ∀ v, T v = c • v` using `fun T => by`. Take `⟨c, hc⟩` from `GlobalTheory.SchurAdm.schur_admissible H C hCo hCc π.V π.ρ π.irred hπ T.toLinearMap fun g v => T.isIntertwining _ _ g v`. Conclude with `⟨c, fun v => LinearMap.congr_fun hc v⟩`.

Take `⟨X, _, _, σ, hσs, hσi, ⟨e⟩⟩` from `TensorFactor.exists_equiv_extTensor G H V π.V τ π.ρ hs hirr π.irred (EvalInj.lift_subtype_injective H V π.V r π.ρ π.irred hS) ⟨f, hf0, hf⟩`. Use `⟨⟨X, σ, hσs, hσi⟩, ⟨π.V, π.ρ, π.smooth, π.irred⟩, fun K hK => ?_, ⟨e⟩⟩` and prove the remaining obligations. Use `((GlobalTheory.CuspRep.isIrreducible_iff π.ρ).1 π.irred).1` as an intermediate fact. Take `⟨y, hy⟩` from `exists_ne (0 : π.V)`. Take `⟨φ, hφ⟩` from `Module.Projective.exists_dual_eq_one ℂ hy`.

Use `hadm (K.prod (stab π.ρ y)) (hK.prod (π.smooth y))` as an intermediate fact. Set `j : fixed σ K →ₗ[ℂ] fixed τ (K.prod (stab π.ρ y))` to `(e.symm.toLinearEquiv.toLinearMap ∘ₗ (TensorProduct.mk ℂ X π.V).flip y).restrict fun w hw => mem_fix.2 fun g hg => by show τ g (e.symm.toIntertwiningMap (w ⊗ₜ y)) = e.symm.toIntertwiningMap (w ⊗ₜ y)`. Establish `h3 : π.ρ g.2 y = y` using `hg.2`. Rewrite using `[← e.symm.toIntertwiningMap.isIntertwining, extTensor_tmul, mem_fix.1 hw _ hg.1, h3]`. Use `FiniteDimensional.of_injective j fun a b hab => Subtype.ext ?_` and prove the remaining obligations.

Establish `h4 : (a : X) ⊗ₜ[ℂ] y = (b : X) ⊗ₜ[ℂ] y` using `e.symm.toLinearEquiv.injective (congrArg Subtype.val hab)`. Establish `h5` using `congrArg ((TensorProduct.rid ℂ X).toLinearMap ∘ₗ LinearMap.lTensor X φ) h4`. Simplify `h5` using `[hφ]`.
-/
theorem exists_extTensor (C : Subgroup H) (hCo : IsOpen (C : Set H)) (hCc : IsCompact (C : Set H))
    {τ : Representation ℂ (G × H) V} (hs : IsSmooth τ) (hirr : τ.IsIrreducible) (hadm : FinFixed τ) :
    ∃ (σ : IrrRep G) (ρ : IrrRep H), FinFixed σ.ρ ∧ Nonempty (τ.Equiv (extTensor σ.ρ ρ.ρ)) := by
  obtain ⟨hnt, hinv⟩ := (GlobalTheory.CuspRep.isIrreducible_iff τ).1 hirr
  obtain ⟨x, hx0⟩ := exists_ne (0 : V)
  let r : Representation ℂ H V := τ.comp (MonoidHom.inr G H)
  have hc : Continuous (MonoidHom.inr G H) := continuous_const.prodMk continuous_id
  have hc' : Continuous (MonoidHom.inl G H) := continuous_id.prodMk continuous_const
  have hρ : IsSmooth r := isSmooth_comp hs _ hc
  let Kc : Subgroup H := stab r x ⊓ C
  have hKco : IsOpen (Kc : Set H) := (hρ x).inter hCo
  have hKcc : IsCompact (Kc : Set H) :=
    hCc.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ hKco) fun k hk => hk.2
  have hxKc : x ∈ fixed r Kc := mem_fix.2 fun k hk => hk.1
  have hnull : nullPart r Kc = ⊥ := by
    rcases hinv (nullPart r Kc) (fun g y hy => by
      obtain ⟨g, h⟩ := g
      rw [TensorFactor.apply_pair]
      exact nullPart_comm r Kc (τ (g, 1)) (fun h z => TensorFactor.commute_apply τ g h z)
        (nullPart_act r Kc h hy)) with h | h
    · exact h
    · exact absurd (eq_zero_of_mem_nullPart hρ hKcc hxKc (h ▸ Submodule.mem_top)) hx0
  have h2 : ∀ Y : Submodule ℂ V, (∀ g, ∀ v ∈ Y, r g v ∈ Y) → Y ⊓ fixed r Kc = ⊥ → Y = ⊥ :=
    fun Y hY h => le_bot_iff.1 (hnull ▸ le_nullPart hρ hKcc Y hY h)
  let l : Representation ℂ G V := τ.comp (MonoidHom.inl G H)
  let L : Subgroup G := stab l x
  have hLo : IsOpen (L : Set G) := isSmooth_comp hs _ hc' x
  let U : Submodule ℂ V := fixed l L
  have hU : ∀ g, ∀ v ∈ U, r g v ∈ U := fun g v hv => mem_fix.2 fun k hk => by
    change τ (k, 1) (τ (1, g) v) = τ (1, g) v
    rw [TensorFactor.commute_apply]
    exact congrArg _ (mem_fix.1 hv k hk)
  have hU0 : U ≠ ⊥ := (Submodule.ne_bot_iff _).2 ⟨x, mem_fix.2 fun k hk => hk, hx0⟩
  have hfin : ∀ K' : Subgroup H, IsOpen (K' : Set H) → FiniteDimensional ℂ ↥(U ⊓ fixed r K') := by
    intro K' hK'
    have := hadm (L.prod K') (hLo.prod hK')
    refine Submodule.finiteDimensional_of_le (S₂ := fixed τ (L.prod K')) fun v hv => mem_fix.2 ?_
    rintro ⟨g, h⟩ hk
    rw [TensorFactor.apply_pair]
    have e1 : τ (1, h) v = v := mem_fix.1 hv.2 h hk.2
    rw [e1]
    exact mem_fix.1 hv.1 g hk.1
  obtain ⟨π, ⟨f, hf0, hf⟩, hπ⟩ := exists_irred hρ hKco h2 U hU hU0 hfin
  have hS : ∀ T : π.ρ.IntertwiningMap π.ρ, ∃ c : ℂ, ∀ v, T v = c • v := fun T => by
    obtain ⟨c, hc⟩ := GlobalTheory.SchurAdm.schur_admissible H C hCo hCc π.V π.ρ π.irred hπ T.toLinearMap
      fun g v => T.isIntertwining _ _ g v
    exact ⟨c, fun v => LinearMap.congr_fun hc v⟩
  obtain ⟨X, _, _, σ, hσs, hσi, ⟨e⟩⟩ := TensorFactor.exists_equiv_extTensor G H V π.V τ π.ρ hs hirr π.irred
    (EvalInj.lift_subtype_injective H V π.V r π.ρ π.irred hS) ⟨f, hf0, hf⟩
  refine ⟨⟨X, σ, hσs, hσi⟩, ⟨π.V, π.ρ, π.smooth, π.irred⟩, fun K hK => ?_, ⟨e⟩⟩
  have := ((GlobalTheory.CuspRep.isIrreducible_iff π.ρ).1 π.irred).1
  obtain ⟨y, hy⟩ := exists_ne (0 : π.V)
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one ℂ hy
  have := hadm (K.prod (stab π.ρ y)) (hK.prod (π.smooth y))
  let j : fixed σ K →ₗ[ℂ] fixed τ (K.prod (stab π.ρ y)) :=
    (e.symm.toLinearEquiv.toLinearMap ∘ₗ (TensorProduct.mk ℂ X π.V).flip y).restrict fun w hw =>
      mem_fix.2 fun g hg => by
        show τ g (e.symm.toIntertwiningMap (w ⊗ₜ y)) = e.symm.toIntertwiningMap (w ⊗ₜ y)
        have h3 : π.ρ g.2 y = y := hg.2
        rw [← e.symm.toIntertwiningMap.isIntertwining, extTensor_tmul, mem_fix.1 hw _ hg.1, h3]
  refine FiniteDimensional.of_injective j fun a b hab => Subtype.ext ?_
  have h4 : (a : X) ⊗ₜ[ℂ] y = (b : X) ⊗ₜ[ℂ] y := e.symm.toLinearEquiv.injective (congrArg Subtype.val hab)
  have h5 := congrArg ((TensorProduct.rid ℂ X).toLinearMap ∘ₗ LinearMap.lTensor X φ) h4
  simpa [hφ] using h5

end General

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `Γ _ _ _ _ V _ _ τ _ hirr _`. Take `⟨hnt, hinv⟩` from `(GlobalTheory.CuspRep.isIrreducible_iff τ).1 hirr`.

Establish `hg : ∀ g : ∀ j, Γ j, g = 1` using `fun g => funext fun j => j.elim0`. Use `haveI : IsSimpleModule ℂ V := { eq_bot_or_eq_top := fun W => hinv W fun g v hv => by rw [hg g, map_one]; exact hv }`. Establish `h1 : Module.finrank ℂ V = 1` using `isSimpleModule_iff_finrank_eq_one.1 inferInstance`. Use `haveI : Module.Finite ℂ V := Module.finite_of_finrank_eq_succ h1`. Use `⟨fun j => j.elim0, (LinearEquiv.ofFinrankEq V ℂ (by simp [h1])).trans (PiTensorProduct.isEmptyEquiv (Fin 0)).symm, fun g v => ?_⟩` and prove the remaining obligations.

Rewrite using `[hg g, map_one, map_one]`. Both sides reduce to the same expression. Consider the case `succ n ih`. Introduce `Γ _ _ _ hC V _ _ τ hs hirr hadm`. Apply the tactic sequence `let φ : (∀ j : Fin n, Γ j.succ) × Γ 0 →* ∀ j, Γ j := { toFun := fun p => Fin.cons p.2 p.1 map_one' := funext fun j => by cases j using Fin.cases <;> rfl map_mul' := fun a b => funext fun j => by cases j using Fin.cases <;> rfl }`.

Set `ψ : (∀ j : Fin n, Γ j.succ) × Γ 0 ≃ₜ ∀ j, Γ j` to `{ toFun := φ invFun := fun g => (fun j => g j.succ, g 0) left_inv := fun _ => rfl right_inv := fun g => Fin.cons_self_tail g continuous_toFun := continuous_pi fun j => by`. Consider the cases of `j using Fin.cases with`. Consider the case `zero => exact continuous_snd`. Consider the case `succ i => exact (continuous_apply i).comp continuous_fst`. Use `continuous_invFun := (continuous_pi fun j => continuous_apply j.succ).prodMk (continuous_apply 0) }`.

Take `⟨C, hCo, hCc⟩` from `hC 0`. Take `⟨σ, ρ, hσ, ⟨E⟩⟩` from `exists_extTensor C hCo hCc (isSmooth_comp hs φ ψ.continuous) ((MultiIrr.isIrreducible_iff_of_linearEquiv (ρ := τ.comp φ) φ ψ.surjective (LinearEquiv.refl ℂ V) fun _ _ => rfl).2 hirr) (hadm.comp φ ψ.isOpenMap)`. Take `⟨s', e', he'⟩` from `ih (fun j => Γ j.succ) (fun j => hC j.succ) σ.V σ.ρ σ.smooth σ.irr hσ`. Set `s : ∀ j, IrrRep (Γ j)` to `Fin.cons ρ s'`. Take `⟨c, hc⟩` from `GlobalTheory.OneFunctional.exists_piTensor_succ_equiv_map n fun j => (s j).V`.

Set `d : σ.V ⊗[ℂ] ρ.V ≃ₗ[ℂ] ⨂[ℂ] j, (s j).V` to `(TensorProduct.congr e' (LinearEquiv.refl ℂ ρ.V)).trans c`. Establish `hd : ∀ g z, d (extTensor σ.ρ ρ.ρ g z) = piTensor (fun j => (s j).ρ) (φ g) (d z)`. Introduce `g z`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp only [map_zero]`.

Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Consider the case `tmul a b`. Rewrite using `[extTensor_tmul]`. Use `show c (e' (σ.ρ g.1 a) ⊗ₜ ρ.ρ g.2 b) = _`. Rewrite using `[he']`.

Conclude with `(hc (fun j => (s j).ρ (φ g j)) (e' a) b).symm`. Use `⟨s, E.toLinearEquiv.trans d, fun g v => ?_⟩` and prove the remaining obligations. Take `⟨g, rfl⟩ : ∃ p, φ p = g` from `ψ.surjective g`. Conclude with `(congrArg d (E.toIntertwiningMap.isIntertwining _ _ g v)).trans (hd g _)`.
-/
theorem exists_piTensor_fin : ∀ (n : ℕ) (Γ : Fin n → Type) [∀ j, Group (Γ j)] [∀ j, TopologicalSpace (Γ j)]
    [∀ j, IsTopologicalGroup (Γ j)],
    (∀ j, ∃ C : Subgroup (Γ j), IsOpen (C : Set (Γ j)) ∧ IsCompact (C : Set (Γ j))) →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (∀ j, Γ j) V),
    IsSmooth τ → τ.IsIrreducible → FinFixed τ →
    ∃ (s : ∀ j, IrrRep (Γ j)) (e : V ≃ₗ[ℂ] ⨂[ℂ] j, (s j).V),
      ∀ g v, e (τ g v) = piTensor (fun j => (s j).ρ) g (e v) := by
  intro n
  induction n with
  | zero =>
    intro Γ _ _ _ _ V _ _ τ _ hirr _
    obtain ⟨hnt, hinv⟩ := (GlobalTheory.CuspRep.isIrreducible_iff τ).1 hirr
    have hg : ∀ g : ∀ j, Γ j, g = 1 := fun g => funext fun j => j.elim0
    haveI : IsSimpleModule ℂ V :=
      { eq_bot_or_eq_top := fun W => hinv W fun g v hv => by rw [hg g, map_one]; exact hv }
    have h1 : Module.finrank ℂ V = 1 := isSimpleModule_iff_finrank_eq_one.1 inferInstance
    haveI : Module.Finite ℂ V := Module.finite_of_finrank_eq_succ h1
    refine ⟨fun j => j.elim0, (LinearEquiv.ofFinrankEq V ℂ (by simp [h1])).trans
      (PiTensorProduct.isEmptyEquiv (Fin 0)).symm, fun g v => ?_⟩
    rw [hg g, map_one, map_one]
    rfl
  | succ n ih =>
    intro Γ _ _ _ hC V _ _ τ hs hirr hadm
    let φ : (∀ j : Fin n, Γ j.succ) × Γ 0 →* ∀ j, Γ j :=
      { toFun := fun p => Fin.cons p.2 p.1
        map_one' := funext fun j => by cases j using Fin.cases <;> rfl
        map_mul' := fun a b => funext fun j => by cases j using Fin.cases <;> rfl }
    let ψ : (∀ j : Fin n, Γ j.succ) × Γ 0 ≃ₜ ∀ j, Γ j :=
      { toFun := φ
        invFun := fun g => (fun j => g j.succ, g 0)
        left_inv := fun _ => rfl
        right_inv := fun g => Fin.cons_self_tail g
        continuous_toFun := continuous_pi fun j => by
          cases j using Fin.cases with
          | zero => exact continuous_snd
          | succ i => exact (continuous_apply i).comp continuous_fst
        continuous_invFun := (continuous_pi fun j => continuous_apply j.succ).prodMk (continuous_apply 0) }
    obtain ⟨C, hCo, hCc⟩ := hC 0
    obtain ⟨σ, ρ, hσ, ⟨E⟩⟩ := exists_extTensor C hCo hCc (isSmooth_comp hs φ ψ.continuous)
      ((MultiIrr.isIrreducible_iff_of_linearEquiv (ρ := τ.comp φ) φ ψ.surjective (LinearEquiv.refl ℂ V)
        fun _ _ => rfl).2 hirr) (hadm.comp φ ψ.isOpenMap)
    obtain ⟨s', e', he'⟩ := ih (fun j => Γ j.succ) (fun j => hC j.succ) σ.V σ.ρ σ.smooth σ.irr hσ
    let s : ∀ j, IrrRep (Γ j) := Fin.cons ρ s'
    obtain ⟨c, hc⟩ := GlobalTheory.OneFunctional.exists_piTensor_succ_equiv_map n fun j => (s j).V
    let d : σ.V ⊗[ℂ] ρ.V ≃ₗ[ℂ] ⨂[ℂ] j, (s j).V :=
      (TensorProduct.congr e' (LinearEquiv.refl ℂ ρ.V)).trans c
    have hd : ∀ g z, d (extTensor σ.ρ ρ.ρ g z) = piTensor (fun j => (s j).ρ) (φ g) (d z) := by
      intro g z
      induction z using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | add a b ha hb => simp only [map_add, ha, hb]
      | tmul a b =>
        rw [extTensor_tmul]
        show c (e' (σ.ρ g.1 a) ⊗ₜ ρ.ρ g.2 b) = _
        rw [he']
        exact (hc (fun j => (s j).ρ (φ g j)) (e' a) b).symm
    refine ⟨s, E.toLinearEquiv.trans d, fun g v => ?_⟩
    obtain ⟨g, rfl⟩ : ∃ p, φ p = g := ψ.surjective g
    exact (congrArg d (E.toIntertwiningMap.isIntertwining _ _ g v)).trans (hd g _)

/- English proof (translation)
Set `ε` to `Fintype.equivFin β`. Set `ψ : (∀ j, Γ j) ≃ₜ ∀ i, Γ (ε.symm i)` to `(Homeomorph.piCongrLeft (Y := Γ) ε.symm).symm`. Set `χ : (∀ j, Γ j) ≃* ∀ i, Γ (ε.symm i)` to `{ ψ.toEquiv with map_mul' := fun _ _ => rfl }`. Set `φ : (∀ i, Γ (ε.symm i)) →* ∀ j, Γ j` to `χ.symm.toMonoidHom`. Take `⟨s', e', he'⟩` from `exists_piTensor_fin _ (fun i => Γ (ε.symm i)) (fun i => hC _) V (τ.comp φ) (isSmooth_comp hs φ ψ.symm.continuous) ((MultiIrr.isIrreducible_iff_of_linearEquiv (ρ := τ.comp φ) φ χ.symm.surjective (LinearEquiv.refl ℂ V) fun _ _ => rfl).2 hirr) (hadm.comp φ ψ.symm.isOpenMap)`.

Take `⟨s, rfl⟩` from `(Equiv.piCongrLeft' (fun j => IrrRep (Γ j)) ε).surjective s'`. Set `r` to `PiTensorProduct.reindex ℂ (fun j => (s j).V) ε`. Establish `hr : ∀ g z, r (piTensor (fun j => (s j).ρ) g z) = piTensor (fun i => (s (ε.symm i)).ρ) (χ g) (r z)`. Introduce `g z`. Proceed by induction on `z using PiTensorProduct.induction_on with`.

Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Consider the case `smul_tprod c x`. Simplify using `only [map_smul, r, piTensor_tprod, PiTensorProduct.reindex_tprod]`. Both sides reduce to the same expression. Use `⟨s, ⟨.mk (e'.trans r.symm) fun g => LinearMap.ext fun v => r.injective ?_⟩⟩` and prove the remaining obligations.

Use `show r (r.symm (e' (τ g v))) = r (piTensor (fun j => (s j).ρ) g (r.symm (e' v)))`. Rewrite using `[hr]`. Use `(r.apply_symm_apply _).trans (Eq.trans ?_ (congrArg _ (r.apply_symm_apply (e' v)).symm))` and prove the remaining obligations. Establish `h1` using `he' (χ g) v`. Establish `h2 : φ (χ g) = g` using `χ.symm_apply_apply g`.

Rewrite `h1` using `[MonoidHom.comp_apply, h2]`. Conclude with `h1`.
-/
theorem exists_piTensor {β : Type} [Fintype β] (Γ : β → Type) [∀ j, Group (Γ j)] [∀ j, TopologicalSpace (Γ j)]
    [∀ j, IsTopologicalGroup (Γ j)]
    (hC : ∀ j, ∃ C : Subgroup (Γ j), IsOpen (C : Set (Γ j)) ∧ IsCompact (C : Set (Γ j)))
    {V : Type} [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (∀ j, Γ j) V)
    (hs : IsSmooth τ) (hirr : τ.IsIrreducible) (hadm : FinFixed τ) :
    ∃ s : ∀ j, IrrRep (Γ j), Nonempty (τ.Equiv (piTensor fun j => (s j).ρ)) := by
  let ε := Fintype.equivFin β
  let ψ : (∀ j, Γ j) ≃ₜ ∀ i, Γ (ε.symm i) := (Homeomorph.piCongrLeft (Y := Γ) ε.symm).symm
  let χ : (∀ j, Γ j) ≃* ∀ i, Γ (ε.symm i) := { ψ.toEquiv with map_mul' := fun _ _ => rfl }
  let φ : (∀ i, Γ (ε.symm i)) →* ∀ j, Γ j := χ.symm.toMonoidHom
  obtain ⟨s', e', he'⟩ := exists_piTensor_fin _ (fun i => Γ (ε.symm i)) (fun i => hC _) V (τ.comp φ)
    (isSmooth_comp hs φ ψ.symm.continuous)
    ((MultiIrr.isIrreducible_iff_of_linearEquiv (ρ := τ.comp φ) φ χ.symm.surjective (LinearEquiv.refl ℂ V)
        fun _ _ => rfl).2 hirr) (hadm.comp φ ψ.symm.isOpenMap)
  obtain ⟨s, rfl⟩ := (Equiv.piCongrLeft' (fun j => IrrRep (Γ j)) ε).surjective s'
  let r := PiTensorProduct.reindex ℂ (fun j => (s j).V) ε
  have hr : ∀ g z, r (piTensor (fun j => (s j).ρ) g z) =
      piTensor (fun i => (s (ε.symm i)).ρ) (χ g) (r z) := by
    intro g z
    induction z using PiTensorProduct.induction_on with
    | add a b ha hb => simp only [map_add, ha, hb]
    | smul_tprod c x =>
      simp only [map_smul, r, piTensor_tprod, PiTensorProduct.reindex_tprod]
      rfl
  refine ⟨s, ⟨.mk (e'.trans r.symm) fun g => LinearMap.ext fun v => r.injective ?_⟩⟩
  show r (r.symm (e' (τ g v))) = r (piTensor (fun j => (s j).ρ) g (r.symm (e' v)))
  rw [hr]
  refine (r.apply_symm_apply _).trans (Eq.trans ?_ (congrArg _ (r.apply_symm_apply (e' v)).symm))
  have h1 := he' (χ g) v
  have h2 : φ (χ g) = g := χ.symm_apply_apply g
  rw [MonoidHom.comp_apply, h2] at h1
  exact h1

/- English proof (translation)
Use `letI : LinearOrder β := LinearOrder.lift' (Fintype.equivFin β) (Fintype.equivFin β).injective`. Introduce `K hK`. Set `e : (Σ j, c j) ≃ (Σ j, c j)` to `Equiv.refl _`. Take `⟨h1, -, h3, -⟩` from `hBZ k`. Establish `hl` using `h3 β _ c e τ.V τ.ρ τ.smooth (hasFiniteLength_of_isIrreducible τ.irr)`.

Establish `ho : IsOpen (leviProj k e ⁻¹' ((K : Set (Levi k c)) ∩ (deltaHalf k c).ker))` using `(hK.inter (isSmoothChar_deltaHalf k)).preimage (ProdIrr.continuous_leviProj e)`. Take `⟨N, hN, hNS⟩` from `(mem_nhds_subtype _ _ _).1 (ho.mem_nhds (x := 1) (by`. Rewrite using `[Set.mem_preimage, map_one]`. Conclude with `⟨K.one_mem, one_mem _⟩))`. Take `⟨J, hJo, hJN, hJK, -⟩` from `exists_open_normalised_subgroup_subset k (Σ j, c j) N (by simpa using hN)`.

Establish `hJc : IsCompact (J : Set (GL (Σ j, c j) k))` using `SplitFlip.isCompact_KO.of_isClosed_subset (J.isClosed_of_isOpen hJo) hJK`. Establish `hfin` using `finiteDimensional_fixed_of_hasFiniteLength (h1 _) (isSmooth_parInd e τ.ρ) hl J hJo hJc`. Set `ev : fixed (parInd e τ.ρ) J →ₗ[ℂ] τ.V` to `{ toFun := fun f => f.1.1.1 1 map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl }`. Use `Submodule.finiteDimensional_of_le (S₂ := LinearMap.range ev) fun u hu => ?_` and prove the remaining obligations. Take `⟨f, hf, hf1⟩` from `exists_fixed_smInd_apply_one (parab k e) ((twist τ.ρ (deltaHalf k c)).comp (leviProj k e)) J hJo u fun p hp => by`.

Take `⟨a, b⟩` from `hNS (hJN hp)`. Establish `b' : deltaHalf k c (leviProj k e p) = 1` using `b`. Use `show (deltaHalf k c (leviProj k e p) : ℂ) • τ.ρ (leviProj k e p) u = u`. Rewrite using `[b', mem_fix.1 hu _ a, Units.val_one, one_smul]`. Conclude with `⟨⟨f, hf⟩, hf1⟩`.
-/
theorem finFixed_levi (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (β : Type) [Fintype β] (c : β → Type)
    [∀ j, Fintype (c j)] [∀ j, DecidableEq (c j)] (τ : IrrRep (Levi k c)) : FinFixed τ.ρ := by
  classical
  letI : LinearOrder β := LinearOrder.lift' (Fintype.equivFin β) (Fintype.equivFin β).injective
  intro K hK
  let e : (Σ j, c j) ≃ (Σ j, c j) := Equiv.refl _
  obtain ⟨h1, -, h3, -⟩ := hBZ k
  have hl := h3 β _ c e τ.V τ.ρ τ.smooth (hasFiniteLength_of_isIrreducible τ.irr)
  have ho : IsOpen (leviProj k e ⁻¹' ((K : Set (Levi k c)) ∩ (deltaHalf k c).ker)) :=
    (hK.inter (isSmoothChar_deltaHalf k)).preimage (ProdIrr.continuous_leviProj e)
  obtain ⟨N, hN, hNS⟩ := (mem_nhds_subtype _ _ _).1 (ho.mem_nhds (x := 1) (by
    rw [Set.mem_preimage, map_one]; exact ⟨K.one_mem, one_mem _⟩))
  obtain ⟨J, hJo, hJN, hJK, -⟩ := exists_open_normalised_subgroup_subset k (Σ j, c j) N (by simpa using hN)
  have hJc : IsCompact (J : Set (GL (Σ j, c j) k)) :=
    SplitFlip.isCompact_KO.of_isClosed_subset (J.isClosed_of_isOpen hJo) hJK
  have hfin := finiteDimensional_fixed_of_hasFiniteLength (h1 _) (isSmooth_parInd e τ.ρ) hl J hJo hJc
  let ev : fixed (parInd e τ.ρ) J →ₗ[ℂ] τ.V :=
    { toFun := fun f => f.1.1.1 1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range ev) fun u hu => ?_
  obtain ⟨f, hf, hf1⟩ := exists_fixed_smInd_apply_one (parab k e)
    ((twist τ.ρ (deltaHalf k c)).comp (leviProj k e)) J hJo u fun p hp => by
      obtain ⟨a, b⟩ := hNS (hJN hp)
      have b' : deltaHalf k c (leviProj k e p) = 1 := b
      show (deltaHalf k c (leviProj k e p) : ℂ) • τ.ρ (leviProj k e p) u = u
      rw [b', mem_fix.1 hu _ a, Units.val_one, one_smul]
  exact ⟨⟨f, hf⟩, hf1⟩

/- English proof (translation)
Introduce `hBZ k _ _ _ _ β _ c _ _ τ`. Conclude with `exists_piTensor (fun j => GL (c j) k) (fun j => ⟨GlobalTheory.SplitWeil.KO k (c j), SplitFlip.isOpen_KO, SplitFlip.isCompact_KO⟩) τ.ρ τ.smooth τ.irr (finFixed_levi hBZ k β c τ)`.
-/
theorem exists_equiv_piTensor_levi : GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (β : Type) [Fintype β] (c : β → Type) [∀ j, Fintype (c j)] [∀ j, DecidableEq (c j)] (τ : GlobalTheory.SmGL.IrrRep (GlobalTheory.SmGL.Levi k c)), ∃ s : ∀ j, GlobalTheory.SmGL.IrrRep (GL (c j) k), Nonempty (τ.ρ.Equiv (GlobalTheory.SmGL.piTensor fun j => (s j).ρ)) := by
  intro hBZ k _ _ _ _ β _ c _ _ τ
  exact exists_piTensor (fun j => GL (c j) k)
    (fun j => ⟨GlobalTheory.SplitWeil.KO k (c j), SplitFlip.isOpen_KO, SplitFlip.isCompact_KO⟩) τ.ρ τ.smooth τ.irr
    (finFixed_levi hBZ k β c τ)

end GlobalTheory.LeviFactor
