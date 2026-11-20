import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsingletonOfGiso
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SurjectiveIntertwinerQuotientEquiv
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibOrd.ChainFilt

section generic
variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ G V} {σ : Representation ℂ G W}

def subMap (f : V →ₗ[ℂ] W) (hf : ∀ x v, f (ρ x v) = σ x (f v)) (S : Subrepresentation ρ) :
    Subrepresentation σ :=
  ⟨S.toSubmodule.map f, by
    rintro g _ ⟨v, hv, rfl⟩
    exact ⟨ρ g v, S.apply_mem_toSubmodule g hv, hf g v⟩⟩

/- English proof (translation)
Introduce and unpack `_ ⟨v, hv, rfl⟩`. Conclude with `⟨v, h hv, rfl⟩`.
-/
theorem subMap_mono (f : V →ₗ[ℂ] W) (hf : ∀ x v, f (ρ x v) = σ x (f v))
    {S T : Subrepresentation ρ} (h : S ≤ T) : subMap f hf S ≤ subMap f hf T := by
  rintro _ ⟨v, hv, rfl⟩
  exact ⟨v, h hv, rfl⟩

/- English proof (translation)
The claim follows from `Subrepresentation.toSubmodule_injective (Submodule.map_bot f)`.
-/
theorem subMap_bot (f : V →ₗ[ℂ] W) (hf : ∀ x v, f (ρ x v) = σ x (f v)) :
    subMap f hf (⊥ : Subrepresentation ρ) = ⊥ :=
  Subrepresentation.toSubmodule_injective (Submodule.map_bot f)

/- English proof (translation)
Set `e : S.toSubmodule ≃ₗ[ℂ] (subMap f hf S).toSubmodule` to `Submodule.equivMapOfInjective f hi S.toSubmodule`. Establish `he : (T.toSubmodule.comap S.toSubmodule.subtype).map e.toLinearMap = (subMap f hf T).toSubmodule.comap (subMap f hf S).toSubmodule.subtype`. Use extensionality with `⟨w, hw⟩`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨v, hvS⟩, hvT, hv⟩`.

Establish `hv' : f v = w` using `congrArg Subtype.val hv`. Conclude with `⟨v, hvT, hv'⟩`. Introduce and unpack `⟨v, hvT, hv⟩`. Take `⟨u, hu, rfl⟩` from `hw`. Establish `huv : v = u` using `hi hv`.

Substitute `huv` using the available equality. Conclude with `⟨⟨v, hu⟩, hvT, Subtype.ext rfl⟩`. Set `q` to `Submodule.Quotient.equiv _ _ e he`. Use `⟨Representation.Equiv.mk q fun g => ?_⟩` and prove the remaining obligations. Use `Submodule.linearMap_qext _ ?_` and prove the remaining obligations.

Use extensionality with `v`. Use `show Submodule.Quotient.mk (e ⟨ρ g v.1, S.apply_mem_toSubmodule g v.2⟩) = Submodule.Quotient.mk (⟨σ g (f v.1), (subMap f hf S).apply_mem_toSubmodule g ⟨v.1, v.2, rfl⟩⟩ : _)`. Use `congr 1`. Conclude with `Subtype.ext (hf g v.1)`.
-/
theorem subQuot_subMap_equiv (f : V →ₗ[ℂ] W) (hf : ∀ x v, f (ρ x v) = σ x (f v))
    (hi : Function.Injective f) (S T : Subrepresentation ρ) :
    Nonempty ((subQuot S T).Equiv (subQuot (subMap f hf S) (subMap f hf T))) := by
  let e : S.toSubmodule ≃ₗ[ℂ] (subMap f hf S).toSubmodule :=
    Submodule.equivMapOfInjective f hi S.toSubmodule
  have he : (T.toSubmodule.comap S.toSubmodule.subtype).map e.toLinearMap =
      (subMap f hf T).toSubmodule.comap (subMap f hf S).toSubmodule.subtype := by
    ext ⟨w, hw⟩
    constructor
    · rintro ⟨⟨v, hvS⟩, hvT, hv⟩
      have hv' : f v = w := congrArg Subtype.val hv
      exact ⟨v, hvT, hv'⟩
    · rintro ⟨v, hvT, hv⟩
      obtain ⟨u, hu, rfl⟩ := hw
      have huv : v = u := hi hv
      subst huv
      exact ⟨⟨v, hu⟩, hvT, Subtype.ext rfl⟩
  let q := Submodule.Quotient.equiv _ _ e he
  refine ⟨Representation.Equiv.mk q fun g => ?_⟩
  refine Submodule.linearMap_qext _ ?_
  ext v
  show Submodule.Quotient.mk (e ⟨ρ g v.1, S.apply_mem_toSubmodule g v.2⟩) =
    Submodule.Quotient.mk (⟨σ g (f v.1), (subMap f hf S).apply_mem_toSubmodule g ⟨v.1, v.2, rfl⟩⟩ : _)
  congr 1
  exact Subtype.ext (hf g v.1)

end generic

section chain
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : ℕ} {R : ℕ → GRep k n → Prop} {Z : ℕ → Prop}

/- English proof (translation)
Apply the tactic sequence `induction h <;> omega`.
-/
theorem chain_le {a b : ℕ} {X : GRep k n} (h : Chain R Z a b X) : a ≤ b := by
  induction h <;> omega

/- English proof (translation)
Take `⟨F, hF1, hF2⟩ : ∃ F : ℕ → Subrepresentation X.ρ, (∀ i, i ≤ a → F i = ⊤) ∧ (∀ i, a < i → F i = subMap f hf (F' i))` from `⟨fun i => if i ≤ a then ⊤ else subMap f hf (F' i), fun i h => if_pos h, fun i h => if_neg (by omega)⟩`. Use `⟨F, ?_, hF1 a le_rfl, ?_, ?_⟩` and prove the remaining obligations. Introduce `i j hij`. Distinguish the cases in `h2 : i ≤ a`. Rewrite using `[hF1 i h2]`.

Conclude with `le_top`. Rewrite using `[hF2 i (by omega), hF2 j (by omega)]; exact subMap_mono f hf (hanti hij)`. Rewrite using `[hF2 b hab, hbot, subMap_bot]`. Introduce `i hai hib`. Break down `hai.eq_or_lt with rfl | hlt` into its components or cases.

Rewrite using `[hF1 a le_rfl, hF2 (a + 1) (by omega), htop]`. Conclude with `h0`. Rewrite using `[hF2 i hlt, hF2 (i + 1) (by omega)]`. Break down `hst i hlt hib with ⟨A, hR, ⟨e⟩⟩ | ⟨hZ, he⟩` into its components or cases. Take `⟨e'⟩` from `subQuot_subMap_equiv f hf hi (F' i) (F' (i + 1))`.

Conclude with `Or.inl ⟨A, hR, ⟨e'.symm.trans e⟩⟩`. Conclude with `Or.inr ⟨hZ, by rw [he]⟩`.
-/
theorem filt_extend {a b : ℕ} {X Y : GRep k n} (f : Y.V →ₗ[ℂ] X.V)
    (hf : ∀ x v, f (Y.ρ x v) = X.ρ x (f v)) (hi : Function.Injective f) (hab : a < b)
    (F' : ℕ → Subrepresentation Y.ρ) (hanti : Antitone F') (htop : F' (a + 1) = ⊤) (hbot : F' b = ⊥)
    (hst : ∀ i, a + 1 ≤ i → i < b →
      (∃ A, R i A ∧ Nonempty ((subQuot (F' i) (F' (i + 1))).Equiv A.ρ)) ∨ (Z i ∧ F' i = F' (i + 1)))
    (h0 : (∃ A, R a A ∧ Nonempty ((subQuot ⊤ (subMap f hf ⊤)).Equiv A.ρ)) ∨
      (Z a ∧ (⊤ : Subrepresentation X.ρ) = subMap f hf ⊤)) :
    ∃ F : ℕ → Subrepresentation X.ρ, Antitone F ∧ F a = ⊤ ∧ F b = ⊥ ∧ ∀ i, a ≤ i → i < b →
      (∃ A, R i A ∧ Nonempty ((subQuot (F i) (F (i + 1))).Equiv A.ρ)) ∨ (Z i ∧ F i = F (i + 1)) := by
  classical
  obtain ⟨F, hF1, hF2⟩ : ∃ F : ℕ → Subrepresentation X.ρ, (∀ i, i ≤ a → F i = ⊤) ∧
      (∀ i, a < i → F i = subMap f hf (F' i)) :=
    ⟨fun i => if i ≤ a then ⊤ else subMap f hf (F' i), fun i h => if_pos h,
      fun i h => if_neg (by omega)⟩
  refine ⟨F, ?_, hF1 a le_rfl, ?_, ?_⟩
  · intro i j hij
    by_cases h2 : i ≤ a
    · rw [hF1 i h2]; exact le_top
    · rw [hF2 i (by omega), hF2 j (by omega)]; exact subMap_mono f hf (hanti hij)
  · rw [hF2 b hab, hbot, subMap_bot]
  · intro i hai hib
    rcases hai.eq_or_lt with rfl | hlt
    · rw [hF1 a le_rfl, hF2 (a + 1) (by omega), htop]
      exact h0
    · rw [hF2 i hlt, hF2 (i + 1) (by omega)]
      rcases hst i hlt hib with ⟨A, hR, ⟨e⟩⟩ | ⟨hZ, he⟩
      · obtain ⟨e'⟩ := subQuot_subMap_equiv f hf hi (F' i) (F' (i + 1))
        exact Or.inl ⟨A, hR, ⟨e'.symm.trans e⟩⟩
      · exact Or.inr ⟨hZ, by rw [he]⟩

/- English proof (translation)
Introduce `k _ _ _ _ n R Z a b X h`. Proceed by induction on `h with`. Consider the case `nil a X hs`. Use `⟨fun _ => ⊥, fun _ _ _ => le_rfl, ?_, rfl, fun i h1 h2 => by omega⟩` and prove the remaining obligations. Use `Subrepresentation.toSubmodule_injective ?_` and prove the remaining obligations.

Use extensionality with `v`. Establish `: v = 0` using `Subsingleton.elim _ _`. Substitute `this` using the available equality. Conclude with `⟨fun _ => Submodule.zero_mem _, fun _ => Submodule.zero_mem _⟩`. Consider the case `@step a b X Y A hR hs hc ih`.

Take `⟨f, g, hf, hg, hi, hsur, he⟩` from `hs`. Take `⟨F', h1, h2, h3, h4⟩` from `ih`. Establish `hab` using `chain_le hc`. Use `filt_extend f hf hi (by omega) F' h1 h2 h3 h4 (Or.inl ⟨A, hR, ?_⟩)` and prove the remaining obligations. Take `⟨S, hS, e⟩` from `GlobalTheory.CompanionTheory.BZRes.KerQuot.exists_subQuot_top_ker_equiv X.ρ A.ρ ⟨g, fun x => LinearMap.ext (hg x)⟩ hsur`.

Establish `hS' : S = subMap f hf ⊤`. Use `Subrepresentation.toSubmodule_injective ?_` and prove the remaining obligations. Use `hS.trans ?_` and prove the remaining obligations. Use `show LinearMap.ker g = Submodule.map f ⊤`. Rewrite using `[Submodule.map_top, he]`.

Conclude with `hS' ▸ e`. Consider the case `@skip a b X Y hZ he hc ih`. Take `⟨e⟩` from `he`. Take `⟨F', h1, h2, h3, h4⟩` from `ih`. Establish `hab` using `chain_le hc`.

Use `filt_extend e.toLinearEquiv.toLinearMap (eint e) e.toLinearEquiv.injective (by omega) F' h1 h2 h3 h4 (Or.inr ⟨hZ, ?_⟩)` and prove the remaining obligations. Use `Subrepresentation.toSubmodule_injective ?_` and prove the remaining obligations. Use `show ⊤ = Submodule.map e.toLinearEquiv.toLinearMap ⊤`. Rewrite using `[Submodule.map_top, LinearEquiv.range]`.
-/
theorem exists_filtration : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (R : ℕ → GRep k n → Prop) (Z : ℕ → Prop) (a b : ℕ)
    (X : GRep k n), Chain R Z a b X → ∃ F : ℕ → Subrepresentation X.ρ, Antitone F ∧ F a = ⊤ ∧
      F b = ⊥ ∧ ∀ i, a ≤ i → i < b →
        (∃ A, R i A ∧ Nonempty ((subQuot (F i) (F (i + 1))).Equiv A.ρ)) ∨ (Z i ∧ F i = F (i + 1)) := by
  intro k _ _ _ _ n R Z a b X h
  induction h with
  | nil a X hs =>
    refine ⟨fun _ => ⊥, fun _ _ _ => le_rfl, ?_, rfl, fun i h1 h2 => by omega⟩
    refine Subrepresentation.toSubmodule_injective ?_
    ext v
    have : v = 0 := Subsingleton.elim _ _
    subst this
    exact ⟨fun _ => Submodule.zero_mem _, fun _ => Submodule.zero_mem _⟩
  | @step a b X Y A hR hs hc ih =>
    obtain ⟨f, g, hf, hg, hi, hsur, he⟩ := hs
    obtain ⟨F', h1, h2, h3, h4⟩ := ih
    have hab := chain_le hc
    refine filt_extend f hf hi (by omega) F' h1 h2 h3 h4 (Or.inl ⟨A, hR, ?_⟩)
    obtain ⟨S, hS, e⟩ := GlobalTheory.CompanionTheory.BZRes.KerQuot.exists_subQuot_top_ker_equiv X.ρ A.ρ
      ⟨g, fun x => LinearMap.ext (hg x)⟩ hsur
    have hS' : S = subMap f hf ⊤ := by
      refine Subrepresentation.toSubmodule_injective ?_
      refine hS.trans ?_
      show LinearMap.ker g = Submodule.map f ⊤
      rw [Submodule.map_top, he]
    exact hS' ▸ e
  | @skip a b X Y hZ he hc ih =>
    obtain ⟨e⟩ := he
    obtain ⟨F', h1, h2, h3, h4⟩ := ih
    have hab := chain_le hc
    refine filt_extend e.toLinearEquiv.toLinearMap (eint e) e.toLinearEquiv.injective (by omega)
      F' h1 h2 h3 h4 (Or.inr ⟨hZ, ?_⟩)
    refine Subrepresentation.toSubmodule_injective ?_
    show ⊤ = Submodule.map e.toLinearEquiv.toLinearMap ⊤
    rw [Submodule.map_top, LinearEquiv.range]

end chain

end GlobalTheory.CompanionTheory.LeibOrd.ChainFilt

end
