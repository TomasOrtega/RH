import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.SquareIntegrableSegment
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GenericUnlinkedGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitarisableSegmentTwistPrecedesAddOneLe
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LanglandsClassificationUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StandardModulePropertiesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpehLanglandsQuotientStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SegmentLinkedShiftStatement

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel GlobalTheory.UnitaryDual GlobalTheory.GenericUnitary

namespace GlobalTheory.GenericUnitaryBridge

/- English proof (translation)
Take `⟨n, c⟩` from `w`. Take `⟨n', c'⟩` from `δ`. Take `⟨hd1, hc1⟩` from `h`. Take `⟨hd2, hc2⟩` from `isSpeh_one (⟨n', c'⟩ : IrrGL k)`. Take `rfl : n = n'` from `hd1.symm.trans hd2`.

Take `⟨φ⟩` from `hc2.unique hc1`. Conclude with `((IrrGL.of_rep _).symm.trans (IrrGL.of_eq_of.2 ⟨φ⟩)).trans (IrrGL.of_rep _)`.
-/
theorem eq_of_isSpeh_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {δ w : IrrGL k} (h : IsSpeh δ 1 w.rep) : w = δ := by
  obtain ⟨n, c⟩ := w
  obtain ⟨n', c'⟩ := δ
  obtain ⟨hd1, hc1⟩ := h
  obtain ⟨hd2, hc2⟩ := isSpeh_one (⟨n', c'⟩ : IrrGL k)
  obtain rfl : n = n' := hd1.symm.trans hd2
  obtain ⟨φ⟩ := hc2.unique hc1
  exact ((IrrGL.of_rep _).symm.trans (IrrGL.of_eq_of.2 ⟨φ⟩)).trans (IrrGL.of_rep _)

/- English proof (translation)
Introduce `hU hSq hGen hLM hSC k _ _ _ _ _ N V _ _ π hs hi hu hg`. Establish `ord` using `GlobalTheory.LocGL.UnitaryOrder.add_one_le_of_precedes k`. Set `Good : Segment k → Prop` to `fun Δ => ∃ (δ : IrrGL k) (Γ : Segment k) (t : ℝ), IsLSeg Γ δ.rep ∧ IsUnitarisable δ.rep ∧ Δ = Γ.nu (t : ℂ)`. Establish `key : ∀ (w : IrrGL k) (r : ℝ), IsUnitarySpeh w → ∃ 𝔫 : Multiset (Segment k), IsL 𝔫 (w.nu (r : ℂ)).rep ∧ (∀ Γ ∈ 𝔫, Good Γ) ∧ (IsUnitaryLSeg w ∨ ∃ (Γ : Segment k) (t : ℝ), Γ.nu (t : ℂ) ∈ 𝔫 ∧ Γ.nu ((t - 1 : ℝ) : ℂ) ∈ 𝔫)`. Introduce and unpack `w r ⟨δ, m, hsq, hm, hsp⟩`.

Take `⟨Δ, hΔ⟩` from `hSq k δ hsq`. Use `⟨_, hD k ord δ w Δ m hΔ hsq.2.1 hsp r, ?_, ?_⟩` and prove the remaining obligations. Introduce `Γ hΓ`. Take `⟨i, rfl⟩` from `List.mem_ofFn.1 (Multiset.mem_coe.1 hΓ)`. Conclude with `⟨δ, Δ, _, hΔ, hsq.2.1, rfl⟩`.

Break down `Nat.lt_or_ge m 2 with h2 | h2` into its components or cases. Use `left`. Take `rfl : m = 1` from `by omega`. Take `rfl` from `eq_of_isSpeh_one hsp`. Conclude with `⟨⟨Δ, hΔ⟩, hsq.2.1⟩`.

Use `right`. Use `⟨Δ, r + ((m : ℝ) - 1) / 2, Multiset.mem_coe.2 (List.mem_ofFn.2 ⟨⟨0, by omega⟩, ?_⟩), Multiset.mem_coe.2 (List.mem_ofFn.2 ⟨⟨1, by omega⟩, ?_⟩)⟩` and prove the remaining obligations. Simplify using the standard rewrite rules. Use `congr 2`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Take `⟨u, τ, hu1, hτ1, h, x, hd, hx, ⟨φ⟩⟩` from `hU k N V π hs hi hu`. Establish `hfac : ∀ j, ∃ (y : IrrGL k) (s : ℝ), IsUnitarySpeh y ∧ x j = y.nu (s : ℂ)`. Introduce `j`. Establish `hm : x j ∈ factors u τ` using `hx ▸ List.mem_ofFn.2 ⟨j, rfl⟩`.

Break down `List.mem_append.1 hm with hm | hm` into its components or cases. Conclude with `⟨x j, 0, hu1 _ hm, by simp⟩`. Take `⟨p, hp, hm⟩` from `List.mem_flatMap.1 hm`. Break down `List.mem_pair.1 hm with e | e` into its components or cases. Conclude with `⟨p.1, p.2, (hτ1 p hp).1, e⟩`.

Conclude with `⟨p.1, -p.2, (hτ1 p hp).1, e⟩`. Use `choose y s hy hxs using hfac`. Establish `h𝔪 : ∀ j, ∃ 𝔪 : Multiset (Segment k), IsL 𝔪 (x j).rep ∧ ∀ Γ ∈ 𝔪, Good Γ` using `fun j => by`. Take `⟨𝔪, h1, h2, -⟩` from `key (y j) (s j) (hy j)`. Conclude with `⟨𝔪, hxs j ▸ h1, h2⟩`.

Use `choose 𝔪 h𝔪L h𝔪G using h𝔪`. Establish `hL : IsL (∑ j, 𝔪 j) π` using `hB k hLM Good (fun 𝔫 h𝔫 => hA k hSC ord 𝔫 h𝔫) h N x hd 𝔪 h𝔪L h𝔪G V π hi ⟨φ⟩`. Take `⟨h', Δ', z, hd', hunl, hz, ⟨ψ⟩⟩` from `hGen k N V π hs hi hg`. Establish `hL' : IsL (Finset.univ.val.map Δ') π` using `⟨h', z, hd', ⟨Δ', ⟨rfl, fun i j hij hP => hunl i j hij.ne hP.1⟩, hz⟩, (isCosocle_self hi).of_equiv (.refl _) ψ⟩`. Establish `heq : ∑ j, 𝔪 j = Finset.univ.val.map Δ'` using `(hLM k).1 _ _ (IrrGL.of π hs hi) (hL.of_equiv (IrrGL.equivOf π hs hi)) (hL'.of_equiv (IrrGL.equivOf π hs hi))`.

Establish `hno : ∀ Γ ∈ ∑ j, 𝔪 j, ∀ Γ' ∈ ∑ j, 𝔪 j, ¬ Γ.Linked Γ'`. Rewrite using `[heq]`. Introduce `Γ hΓ Γ' hΓ' hl`. Take `⟨i, -, rfl⟩` from `Multiset.mem_map.1 hΓ`. Take `⟨i', -, rfl⟩` from `Multiset.mem_map.1 hΓ'`.

Distinguish the cases in `e : i = i'`. Substitute `e` using the available equality. Conclude with `Segment.not_linked_self _ hl`. Conclude with `hunl i i' e hl`. Establish `hgood : ∀ (w : IrrGL k) (r : ℝ), IsUnitarySpeh w → w.nu (r : ℂ) ∈ List.ofFn x → IsUnitaryLSeg w`.

Introduce `w r hw hmem`. Take `⟨j, hj⟩` from `List.mem_ofFn.1 hmem`. Take `⟨𝔫, h1, -, h3⟩` from `key w r hw`. Break down `h3 with h3 | ⟨Γ, t, h4, h5⟩` into its components or cases. Conclude with `h3`.

Establish `e : 𝔫 = 𝔪 j` using `(hLM k).1 _ _ (x j) (hj ▸ h1) (h𝔪L j)`. Substitute `e` using the available equality. Conclude with `absurd (hF k Γ t) (hno _ (Multiset.mem_sum.2 ⟨j, Finset.mem_univ _, h4⟩) _ (Multiset.mem_sum.2 ⟨j, Finset.mem_univ _, h5⟩))`. Use `⟨u, τ, fun w hw => hgood w 0 (hu1 w hw) ?_, fun p hp => ⟨hgood p.1 p.2 (hτ1 p hp).1 ?_, (hτ1 p hp).2⟩, h, x, hd, hx, ⟨φ⟩⟩` and prove the remaining obligations. Rewrite using `[hx]`.

Simplify using `only [Complex.ofReal_zero, IrrGL.nu_zero]`. Conclude with `List.mem_append_left _ hw`. Rewrite using `[hx]`. Conclude with `List.mem_append_right _ (List.mem_flatMap.2 ⟨p, hp, by simp⟩)`.
-/
theorem of_lemmas (hA : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k], GlobalTheory.Published.StandardCosocleGL → (∀ (δ δ' : IrrGL k) (Δ Δ' : Segment k), IsLSeg Δ δ.rep → IsUnitarisable δ.rep → IsLSeg Δ' δ'.rep →
      IsUnitarisable δ'.rep → ∀ x y : ℝ, (Δ.nu x).Precedes (Δ'.nu y) → x + 1 ≤ y) →
    ∀ 𝔫 : Multiset (Segment k), (∀ Δ ∈ 𝔫, ∃ (δ : IrrGL k) (Γ : Segment k) (t : ℝ), IsLSeg Γ δ.rep ∧
      IsUnitarisable δ.rep ∧ Δ = Γ.nu (t : ℂ)) → ∃ y : IrrGL k, IsL 𝔫 y.rep) (hB : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k], GlobalTheory.Published.LanglandsMultisegments →
    ∀ (P : Segment k → Prop), (∀ 𝔫 : Multiset (Segment k), (∀ Δ ∈ 𝔫, P Δ) → ∃ y : IrrGL k, IsL 𝔫 y.rep) →
    ∀ (h N : ℕ) (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N) (𝔪 : Fin h → Multiset (Segment k)),
      (∀ j, IsL (𝔪 j) (x j).rep) → (∀ j, ∀ Δ ∈ 𝔪 j, P Δ) →
      ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), π.IsIrreducible →
        Nonempty (π.Equiv (prodIrr x hd)) → IsL (∑ j, 𝔪 j) π) (hD : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], (∀ (δ δ' : IrrGL k) (Δ Δ' : Segment k), IsLSeg Δ δ.rep → IsUnitarisable δ.rep → IsLSeg Δ' δ'.rep →
      IsUnitarisable δ'.rep → ∀ x y : ℝ, (Δ.nu x).Precedes (Δ'.nu y) → x + 1 ≤ y) →
    ∀ (δ x : IrrGL k) (Δ : Segment k) (m : ℕ), IsLSeg Δ δ.rep → IsUnitarisable δ.rep → IsSpeh δ m x.rep →
      ∀ s : ℝ, IsL ↑(List.ofFn fun i : Fin m => Δ.nu ((s + ((m : ℝ) - 1) / 2 - (i : ℕ) : ℝ) : ℂ)) (x.nu (s : ℂ)).rep) (hF : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Δ : Segment k) (t : ℝ), (Δ.nu (t : ℂ)).Linked (Δ.nu ((t - 1 : ℝ) : ℂ))) :
    GlobalTheory.Published.UnitaryDualGL → GlobalTheory.Published.SquareIntegrableSegment → GlobalTheory.Published.GenericUnlinkedGL →
      GlobalTheory.Published.LanglandsMultisegments → GlobalTheory.Published.StandardCosocleGL → GlobalTheory.Published.GenericUnitaryDualGL := by
  intro hU hSq hGen hLM hSC k _ _ _ _ _ N V _ _ π hs hi hu hg
  have ord := GlobalTheory.LocGL.UnitaryOrder.add_one_le_of_precedes k
  let Good : Segment k → Prop := fun Δ => ∃ (δ : IrrGL k) (Γ : Segment k) (t : ℝ), IsLSeg Γ δ.rep ∧
      IsUnitarisable δ.rep ∧ Δ = Γ.nu (t : ℂ)
  have key : ∀ (w : IrrGL k) (r : ℝ), IsUnitarySpeh w → ∃ 𝔫 : Multiset (Segment k), IsL 𝔫 (w.nu (r : ℂ)).rep ∧
      (∀ Γ ∈ 𝔫, Good Γ) ∧ (IsUnitaryLSeg w ∨ ∃ (Γ : Segment k) (t : ℝ), Γ.nu (t : ℂ) ∈ 𝔫 ∧
        Γ.nu ((t - 1 : ℝ) : ℂ) ∈ 𝔫) := by
    rintro w r ⟨δ, m, hsq, hm, hsp⟩
    obtain ⟨Δ, hΔ⟩ := hSq k δ hsq
    refine ⟨_, hD k ord δ w Δ m hΔ hsq.2.1 hsp r, ?_, ?_⟩
    · intro Γ hΓ
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 (Multiset.mem_coe.1 hΓ)
      exact ⟨δ, Δ, _, hΔ, hsq.2.1, rfl⟩
    · rcases Nat.lt_or_ge m 2 with h2 | h2
      · left
        obtain rfl : m = 1 := by omega
        obtain rfl := eq_of_isSpeh_one hsp
        exact ⟨⟨Δ, hΔ⟩, hsq.2.1⟩
      · right
        refine ⟨Δ, r + ((m : ℝ) - 1) / 2, Multiset.mem_coe.2 (List.mem_ofFn.2 ⟨⟨0, by omega⟩, ?_⟩),
          Multiset.mem_coe.2 (List.mem_ofFn.2 ⟨⟨1, by omega⟩, ?_⟩)⟩
        · simp
        · congr 2
          push_cast
          ring
  obtain ⟨u, τ, hu1, hτ1, h, x, hd, hx, ⟨φ⟩⟩ := hU k N V π hs hi hu
  have hfac : ∀ j, ∃ (y : IrrGL k) (s : ℝ), IsUnitarySpeh y ∧ x j = y.nu (s : ℂ) := by
    intro j
    have hm : x j ∈ factors u τ := hx ▸ List.mem_ofFn.2 ⟨j, rfl⟩
    rcases List.mem_append.1 hm with hm | hm
    · exact ⟨x j, 0, hu1 _ hm, by simp⟩
    · obtain ⟨p, hp, hm⟩ := List.mem_flatMap.1 hm
      rcases List.mem_pair.1 hm with e | e
      · exact ⟨p.1, p.2, (hτ1 p hp).1, e⟩
      · exact ⟨p.1, -p.2, (hτ1 p hp).1, e⟩
  choose y s hy hxs using hfac
  have h𝔪 : ∀ j, ∃ 𝔪 : Multiset (Segment k), IsL 𝔪 (x j).rep ∧ ∀ Γ ∈ 𝔪, Good Γ := fun j => by
    obtain ⟨𝔪, h1, h2, -⟩ := key (y j) (s j) (hy j)
    exact ⟨𝔪, hxs j ▸ h1, h2⟩
  choose 𝔪 h𝔪L h𝔪G using h𝔪
  have hL : IsL (∑ j, 𝔪 j) π :=
    hB k hLM Good (fun 𝔫 h𝔫 => hA k hSC ord 𝔫 h𝔫) h N x hd 𝔪 h𝔪L h𝔪G V π hi ⟨φ⟩
  obtain ⟨h', Δ', z, hd', hunl, hz, ⟨ψ⟩⟩ := hGen k N V π hs hi hg
  have hL' : IsL (Finset.univ.val.map Δ') π :=
    ⟨h', z, hd', ⟨Δ', ⟨rfl, fun i j hij hP => hunl i j hij.ne hP.1⟩, hz⟩,
      (isCosocle_self hi).of_equiv (.refl _) ψ⟩
  have heq : ∑ j, 𝔪 j = Finset.univ.val.map Δ' :=
    (hLM k).1 _ _ (IrrGL.of π hs hi) (hL.of_equiv (IrrGL.equivOf π hs hi)) (hL'.of_equiv (IrrGL.equivOf π hs hi))
  have hno : ∀ Γ ∈ ∑ j, 𝔪 j, ∀ Γ' ∈ ∑ j, 𝔪 j, ¬ Γ.Linked Γ' := by
    rw [heq]
    intro Γ hΓ Γ' hΓ' hl
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hΓ
    obtain ⟨i', -, rfl⟩ := Multiset.mem_map.1 hΓ'
    by_cases e : i = i'
    · subst e
      exact Segment.not_linked_self _ hl
    · exact hunl i i' e hl
  have hgood : ∀ (w : IrrGL k) (r : ℝ), IsUnitarySpeh w → w.nu (r : ℂ) ∈ List.ofFn x → IsUnitaryLSeg w := by
    intro w r hw hmem
    obtain ⟨j, hj⟩ := List.mem_ofFn.1 hmem
    obtain ⟨𝔫, h1, -, h3⟩ := key w r hw
    rcases h3 with h3 | ⟨Γ, t, h4, h5⟩
    · exact h3
    · have e : 𝔫 = 𝔪 j := (hLM k).1 _ _ (x j) (hj ▸ h1) (h𝔪L j)
      subst e
      exact absurd (hF k Γ t) (hno _ (Multiset.mem_sum.2 ⟨j, Finset.mem_univ _, h4⟩) _
        (Multiset.mem_sum.2 ⟨j, Finset.mem_univ _, h5⟩))
  refine ⟨u, τ, fun w hw => hgood w 0 (hu1 w hw) ?_, fun p hp => ⟨hgood p.1 p.2 (hτ1 p hp).1 ?_, (hτ1 p hp).2⟩,
    h, x, hd, hx, ⟨φ⟩⟩
  · rw [hx]
    simp only [Complex.ofReal_zero, IrrGL.nu_zero]
    exact List.mem_append_left _ hw
  · rw [hx]
    exact List.mem_append_right _ (List.mem_flatMap.2 ⟨p, hp, by simp⟩)

/- English proof (translation)
The claim follows from `of_lemmas GlobalTheory.T.langlands_classification_unitary GlobalTheory.T.standard_module_properties GlobalTheory.T.speh_langlands_quotient GlobalTheory.T.segment_linked_shift`.
-/
theorem genericUnitaryDualGL_of_hypotheses : GlobalTheory.Published.UnitaryDualGL → GlobalTheory.Published.SquareIntegrableSegment →
    GlobalTheory.Published.GenericUnlinkedGL → GlobalTheory.Published.LanglandsMultisegments → GlobalTheory.Published.StandardCosocleGL →
    GlobalTheory.Published.GenericUnitaryDualGL :=
  of_lemmas GlobalTheory.T.langlands_classification_unitary GlobalTheory.T.standard_module_properties GlobalTheory.T.speh_langlands_quotient GlobalTheory.T.segment_linked_shift

end GlobalTheory.GenericUnitaryBridge
