import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocSubSB

open GlobalTheory.WeilM GlobalTheory.HoweAdelic

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.HoweAdelic.TrivSup

/- English proof (translation)
Use `{ toNontrivial := ⟨⟨⊥, ⊤, fun h => ?_⟩⟩, eq_bot_or_eq_top := fun S => ?_ }` and prove the remaining obligations. Conclude with `bot_ne_top (α := Submodule ℂ ℂ) (congrArg Subrepresentation.toSubmodule h)`. Break down `eq_bot_or_eq_top (α := Submodule ℂ ℂ) S.toSubmodule with h | h` into its components or cases. Conclude with `Or.inl (Subrepresentation.ext h)`. Conclude with `Or.inr (Subrepresentation.ext h)`.
-/
theorem trivial_irr (G : Type) [Group G] : (Representation.trivial ℂ G ℂ).IsIrreducible := by
  refine { toNontrivial := ⟨⟨⊥, ⊤, fun h => ?_⟩⟩, eq_bot_or_eq_top := fun S => ?_ }
  · exact bot_ne_top (α := Submodule ℂ ℂ) (congrArg Subrepresentation.toSubmodule h)
  · rcases eq_bot_or_eq_top (α := Submodule ℂ ℂ) S.toSubmodule with h | h
    · exact Or.inl (Subrepresentation.ext h)
    · exact Or.inr (Subrepresentation.ext h)

/- English proof (translation)
Use `⟨fun v => ?_, fun K _ _ => inferInstance⟩` and prove the remaining obligations. Establish `: {g : G | Representation.trivial ℂ G ℂ g v = v} = Set.univ` using `by ext; simp`. Rewrite using `[this]`. Conclude with `isOpen_univ`.
-/
theorem trivial_adm (G : Type) [Group G] [TopologicalSpace G] :
    GlobalTheory.PRep.IsAdmissible (Representation.trivial ℂ G ℂ) := by
  refine ⟨fun v => ?_, fun K _ _ => inferInstance⟩
  have : {g : G | Representation.trivial ℂ G ℂ g v = v} = Set.univ := by ext; simp
  rw [this]; exact isOpen_univ

/- English proof (translation)
Take `⟨hN, -⟩` from `isFiniteLength_iff_isNoetherian_isArtinian.1 hf`. Establish `: IsCoatomic (Submodule (MonoidAlgebra ℂ H) Θ.asModule)` using `inferInstance`. Establish `hc : IsCoatomic (Subrepresentation Θ)` using `(Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := Θ)).isCoatomic_iff.2 this`. Take `h | ⟨C, hC, hle⟩` from `hc.eq_top_or_exists_le_coatom S`. Conclude with `absurd h hS`.

Conclude with `⟨C, hC, hle⟩`.
-/
theorem exists_coatom_of_finiteLength {H T : Type} [Group H] [AddCommGroup T] [Module ℂ T] (Θ : Representation ℂ H T)
    (hf : IsFiniteLength (MonoidAlgebra ℂ H) Θ.asModule) (S : Subrepresentation Θ) (hS : S ≠ ⊤) :
    ∃ C : Subrepresentation Θ, IsCoatom C ∧ S ≤ C := by
  obtain ⟨hN, -⟩ := isFiniteLength_iff_isNoetherian_isArtinian.1 hf
  have : IsCoatomic (Submodule (MonoidAlgebra ℂ H) Θ.asModule) := inferInstance
  have hc : IsCoatomic (Subrepresentation Θ) :=
    (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := Θ)).isCoatomic_iff.2 this
  obtain h | ⟨C, hC, hle⟩ := hc.eq_top_or_exists_le_coatom S
  · exact absurd h hS
  · exact ⟨C, hC, hle⟩

end GlobalTheory.HoweAdelic.TrivSup

namespace GlobalTheory.HoweAdelic

open TrivSup in

/- English proof (translation)
Introduce `Y G H _ _ _ _ _ om hHD hom N N' hN hN' hNe hN'e hsup`. Take `⟨⟨T, _, _, Θ, p, ⟨hpair, hsurj, hker⟩, -, hfl, huniq⟩, -⟩` from `hHD ℂ (Representation.trivial ℂ G ℂ) (trivial_irr G) (trivial_adm G)`. Set `q : SB Y →ₗ[ℂ] T` to `(TensorProduct.lid ℂ T).toLinearMap ∘ₗ p`. Establish `hqsurj : Function.Surjective q` using `(TensorProduct.lid ℂ T).surjective.comp hsurj`. Establish `hq : ∀ (h : H) (φ φ₁ : SB Y), (φ₁ : Y → ℂ) = om (1, h) φ → q φ₁ = Θ h (q φ)`.

Introduce `h φ φ₁ e`. Simplify using `only [q, LinearMap.comp_apply, LinearEquiv.coe_coe]`. Rewrite using `[hpair 1 h φ φ₁ e]`. Proceed by induction on `p φ using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul a t => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Establish `hkerq : ∀ x : SB Y, q x = 0 → (x : Y → ℂ) ∈ locAug om`. Introduce `x hx`. Establish `hp : p x = 0` using `by simpa [q] using hx`.

Assume the negation of the conclusion as `hnot`. Set `L : Submodule ℂ (SB Y)` to `(locAug om).comap (SB Y).subtype`. Establish `hxL : L.mkQ x ≠ 0`. Rewrite using `[Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Conclude with `hnot`.

Choose the witnesses or unpack the hypotheses as in `⟨l, hl⟩ : ∃ l : Module.Dual ℂ (SB Y ⧸ L), l (L.mkQ x) ≠ 0 := by`. Assume the negation of the conclusion as `hall`. Use `push_neg at hall`. Conclude with `hxL ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 hall)`. Establish `hf : GlobalTheory.Published.IsLeftHom om (Representation.trivial ℂ G ℂ) (l ∘ₗ L.mkQ)`.

Introduce `g φ φ₁ e`. Establish `hmem : φ₁ - φ ∈ L` using `by show ((φ₁ - φ : SB Y) : Y → ℂ) ∈ locAug om`. Rewrite using `[Submodule.coe_sub, e]`. Conclude with `Submodule.subset_span ⟨g, φ, φ.2, rfl⟩`. Establish `h0 : L.mkQ (φ₁ - φ) = 0`.

Rewrite using `[Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Conclude with `hmem`. Rewrite `h0` using `[map_sub]`. Simplify using `only [LinearMap.comp_apply, Representation.trivial, MonoidHom.one_apply, Module.End.one_apply]`. Rewrite using `[sub_eq_zero.1 h0]`.

Conclude with `hl ((hker x).1 hp _ hf)`. Establish `key : ∀ M, IsLocSub om M → M ≠ SB Y → ∃ C : Subrepresentation Θ, IsCoatom C ∧ ∀ φ : SB Y, (φ : Y → ℂ) ∈ M → q φ ∈ C.toSubmodule`. Introduce `M hM hMne`. Take `⟨S, hSdef⟩ : ∃ S : Subrepresentation Θ, S.toSubmodule = (M.comap (SB Y).subtype).map q` from `⟨⟨(M.comap (SB Y).subtype).map q, by`. Introduce and unpack `h _ ⟨φ, hφ, rfl⟩`.

Conclude with `⟨⟨om (1, h) φ, hom _ φ φ.2⟩, hM.2.2 h φ hφ, hq h φ _ rfl⟩⟩, rfl⟩`. Establish `hS : S ≠ ⊤`. Introduce `hS`. Apply `hMne` to reduce the goal to its premises. Use `le_antisymm hM.2.1 (fun φ hφ => ?_)` and prove the remaining obligations.

Establish `h1 : q ⟨φ, hφ⟩ ∈ S.toSubmodule` using `by rw [hS]; exact Submodule.mem_top`. Rewrite `h1` using `[hSdef]`. Take `⟨ψ, hψ, e⟩` from `h1`. Establish `hd` using `hkerq (⟨φ, hφ⟩ - ψ) (by rw [map_sub, e, sub_self])`. Establish `h2 : φ = (((⟨φ, hφ⟩ : SB Y) - ψ : SB Y) : Y → ℂ) + ψ` using `by simp`.

Rewrite using `[h2]`. Conclude with `M.add_mem (hM.1 hd) hψ`. Take `⟨C, hC, hle⟩` from `exists_coatom_of_finiteLength Θ hfl S hS`. Use `⟨C, hC, fun φ hφ => hle (show q φ ∈ S.toSubmodule from ?_)⟩` and prove the remaining obligations. Rewrite using `[hSdef]`.

Conclude with `⟨φ, hφ, rfl⟩`. Take `⟨C, hC, hCN⟩` from `key N hN hNe`. Take `⟨C', hC', hCN'⟩` from `key N' hN' hN'e`. Take `rfl` from `huniq C C' hC hC'`. Apply `hC.1` to reduce the goal to its premises.

Use `Subrepresentation.toSubmodule_injective (eq_top_iff.2 fun t _ => ?_)` and prove the remaining obligations. Take `⟨φ, rfl⟩` from `hqsurj t`. Establish `hφ : (φ : Y → ℂ) ∈ N ⊔ N'` using `by rw [hsup]; exact φ.2`. Take `⟨a, ha, b, hb, e⟩` from `Submodule.mem_sup.1 hφ`. Establish `h3 : φ = ⟨a, hN.2.1 ha⟩ + ⟨b, hN'.2.1 hb⟩` using `Subtype.ext (by simp [e])`.

Rewrite using `[h3, map_add]`. Conclude with `C.toSubmodule.add_mem (hCN _ ha) (hCN' _ hb)`.
-/
theorem sup_ne_SB_of_howeDuality : ∀ {Y G H : Type} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H] [TopologicalSpace Y]
    (om : G × H →* Module.End ℂ (Y → ℂ)), GlobalTheory.Published.HoweDualityFor om → (∀ x, ∀ φ ∈ SB Y, om x φ ∈ SB Y) →
    ∀ N N', IsLocSub om N → IsLocSub om N' → N ≠ SB Y → N' ≠ SB Y → N ⊔ N' ≠ SB Y := by
  intro Y G H _ _ _ _ _ om hHD hom N N' hN hN' hNe hN'e hsup
  obtain ⟨⟨T, _, _, Θ, p, ⟨hpair, hsurj, hker⟩, -, hfl, huniq⟩, -⟩ :=
    hHD ℂ (Representation.trivial ℂ G ℂ) (trivial_irr G) (trivial_adm G)
  let q : SB Y →ₗ[ℂ] T := (TensorProduct.lid ℂ T).toLinearMap ∘ₗ p
  have hqsurj : Function.Surjective q := (TensorProduct.lid ℂ T).surjective.comp hsurj
  have hq : ∀ (h : H) (φ φ₁ : SB Y), (φ₁ : Y → ℂ) = om (1, h) φ → q φ₁ = Θ h (q φ) := by
    intro h φ φ₁ e
    simp only [q, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hpair 1 h φ φ₁ e]
    induction p φ using TensorProduct.induction_on with
    | zero => simp
    | tmul a t => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  have hkerq : ∀ x : SB Y, q x = 0 → (x : Y → ℂ) ∈ locAug om := by
    intro x hx
    have hp : p x = 0 := by simpa [q] using hx
    by_contra hnot
    let L : Submodule ℂ (SB Y) := (locAug om).comap (SB Y).subtype
    have hxL : L.mkQ x ≠ 0 := by
      rw [Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact hnot
    obtain ⟨l, hl⟩ : ∃ l : Module.Dual ℂ (SB Y ⧸ L), l (L.mkQ x) ≠ 0 := by
      by_contra hall; push_neg at hall
      exact hxL ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 hall)
    have hf : GlobalTheory.Published.IsLeftHom om (Representation.trivial ℂ G ℂ) (l ∘ₗ L.mkQ) := by
      intro g φ φ₁ e
      have hmem : φ₁ - φ ∈ L := by
        show ((φ₁ - φ : SB Y) : Y → ℂ) ∈ locAug om
        rw [Submodule.coe_sub, e]
        exact Submodule.subset_span ⟨g, φ, φ.2, rfl⟩
      have h0 : L.mkQ (φ₁ - φ) = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact hmem
      rw [map_sub] at h0
      simp only [LinearMap.comp_apply, Representation.trivial, MonoidHom.one_apply, Module.End.one_apply]
      rw [sub_eq_zero.1 h0]
    exact hl ((hker x).1 hp _ hf)
  have key : ∀ M, IsLocSub om M → M ≠ SB Y →
      ∃ C : Subrepresentation Θ, IsCoatom C ∧ ∀ φ : SB Y, (φ : Y → ℂ) ∈ M → q φ ∈ C.toSubmodule := by
    intro M hM hMne
    obtain ⟨S, hSdef⟩ : ∃ S : Subrepresentation Θ, S.toSubmodule = (M.comap (SB Y).subtype).map q :=
      ⟨⟨(M.comap (SB Y).subtype).map q, by
        rintro h _ ⟨φ, hφ, rfl⟩
        exact ⟨⟨om (1, h) φ, hom _ φ φ.2⟩, hM.2.2 h φ hφ, hq h φ _ rfl⟩⟩, rfl⟩
    have hS : S ≠ ⊤ := by
      intro hS
      apply hMne
      refine le_antisymm hM.2.1 (fun φ hφ => ?_)
      have h1 : q ⟨φ, hφ⟩ ∈ S.toSubmodule := by rw [hS]; exact Submodule.mem_top
      rw [hSdef] at h1
      obtain ⟨ψ, hψ, e⟩ := h1
      have hd := hkerq (⟨φ, hφ⟩ - ψ) (by rw [map_sub, e, sub_self])
      have h2 : φ = (((⟨φ, hφ⟩ : SB Y) - ψ : SB Y) : Y → ℂ) + ψ := by simp
      rw [h2]; exact M.add_mem (hM.1 hd) hψ
    obtain ⟨C, hC, hle⟩ := exists_coatom_of_finiteLength Θ hfl S hS
    refine ⟨C, hC, fun φ hφ => hle (show q φ ∈ S.toSubmodule from ?_)⟩
    rw [hSdef]; exact ⟨φ, hφ, rfl⟩
  obtain ⟨C, hC, hCN⟩ := key N hN hNe
  obtain ⟨C', hC', hCN'⟩ := key N' hN' hN'e
  obtain rfl := huniq C C' hC hC'
  apply hC.1
  refine Subrepresentation.toSubmodule_injective (eq_top_iff.2 fun t _ => ?_)
  obtain ⟨φ, rfl⟩ := hqsurj t
  have hφ : (φ : Y → ℂ) ∈ N ⊔ N' := by rw [hsup]; exact φ.2
  obtain ⟨a, ha, b, hb, e⟩ := Submodule.mem_sup.1 hφ
  have h3 : φ = ⟨a, hN.2.1 ha⟩ + ⟨b, hN'.2.1 hb⟩ := Subtype.ext (by simp [e])
  rw [h3, map_add]
  exact C.toSubmodule.add_mem (hCN _ ha) (hCN' _ hb)

end GlobalTheory.HoweAdelic
