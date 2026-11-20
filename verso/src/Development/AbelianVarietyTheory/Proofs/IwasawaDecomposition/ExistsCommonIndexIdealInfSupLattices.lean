import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThClass
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIndexIdeal

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.BetaEx
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

/- English proof (translation)
Establish `hsub : ∀ N : Submodule (𝓞 E) (Fin n → E), N ≤ M' ⊔ M → Bdd N`. Introduce `N hN`. Take `⟨k, hk, h⟩` from `hb`. Conclude with `⟨k, hk, fun v hv => h v (hN hv)⟩`. Establish `key : ∀ s : Finset (Fin n → E), (∀ x ∈ s, x ∈ M) → ∃ 𝔞 : Ideal (𝓞 E), 𝔞 ≠ ⊥ ∧ detSpan (M ⊓ M') = 𝔞 • detSpan ((M ⊓ M') ⊔ Submodule.span (𝓞 E) (s : Set (Fin n → E))) ∧ detSpan M' = 𝔞 • detSpan (M' ⊔ Submodule.span (𝓞 E) (s : Set (Fin n → E))) ∧ Ideal.absNorm 𝔞 = (M ⊓ M').toAddSubg …`.

Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => intro _; exact ⟨⊤, by simp, by simp, by simp, by simp⟩`. Consider the case `insert m s _ ih`. Introduce `hs`.

Take `⟨𝔞, h0, h1, h1', h2⟩` from `ih fun x hx => hs x (Finset.mem_insert_of_mem hx)`. Establish `hsM : Submodule.span (𝓞 E) (s : Set (Fin n → E)) ≤ M` using `Submodule.span_le.2 fun x hx => hs x (Finset.mem_insert_of_mem hx)`. Use `set N := (M ⊓ M') ⊔ Submodule.span (𝓞 E) (s : Set (Fin n → E)) with hN`. Use `set S := M' ⊔ Submodule.span (𝓞 E) (s : Set (Fin n → E)) with hS`. Establish `hm : m ∈ M` using `hs m (Finset.mem_insert_self _ _)`.

Establish `hmM : Submodule.span (𝓞 E) {m} ≤ M` using `(Submodule.span_singleton_le_iff_mem _ _).2 hm`. Establish `e : (M ⊓ M') ⊔ Submodule.span (𝓞 E) ((insert m s : Finset (Fin n → E)) : Set (Fin n → E)) = N ⊔ Submodule.span (𝓞 E) {m}`. Rewrite using `[Finset.coe_insert, Submodule.span_insert, hN, sup_assoc, sup_comm (Submodule.span _ {m})]`. Establish `e' : M' ⊔ Submodule.span (𝓞 E) ((insert m s : Finset (Fin n → E)) : Set (Fin n → E)) = S ⊔ Submodule.span (𝓞 E) {m}`. Rewrite using `[Finset.coe_insert, Submodule.span_insert, hS, sup_assoc, sup_comm (Submodule.span _ {m})]`.

Establish `hNS : N = M ⊓ S`. Rewrite using `[hN, hS, inf_sup_assoc_of_le _ hsM]`. Establish `hb1 : Bdd (N ⊔ Submodule.span (𝓞 E) {m})` using `hsub _ (le_sup_of_le_right (sup_le (sup_le inf_le_left hsM) hmM))`. Establish `hb2 : Bdd (S ⊔ Submodule.span (𝓞 E) {m})` using `hsub _ (sup_le (sup_le_sup_left hsM _) (le_sup_of_le_right hmM))`. Establish `hc : (N.comap (LinearMap.toSpanSingleton (𝓞 E) _ m) : Ideal (𝓞 E)) = S.comap (LinearMap.toSpanSingleton (𝓞 E) _ m)`.

Use extensionality with `a`. Rewrite using `[hNS]`. Conclude with `⟨fun h => h.2, fun h => ⟨M.smul_mem a hm, h⟩⟩`. Rewrite using `[e, e']`. Use `⟨𝔞 * (N.comap (LinearMap.toSpanSingleton (𝓞 E) _ m) : Ideal (𝓞 E)), ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Use `mul_ne_zero h0 ?_` and prove the remaining obligations. Take `⟨a, ha, ham⟩` from `ht m hm`. Conclude with `(Submodule.ne_bot_iff _).2 ⟨a, (le_sup_left : M ⊓ M' ≤ N) ⟨M.smul_mem a hm, ham⟩, ha⟩`. Rewrite using `[h1, Submodule.mul_smul, ← detSpan_cyclic N m hb1]`. Rewrite using `[h1', hc, Submodule.mul_smul, ← detSpan_cyclic S m hb2]`.

Rewrite using `[map_mul, h2, index_cyclic]`. Conclude with `AddSubgroup.relIndex_mul_relIndex _ _ _ (Submodule.toAddSubgroup_mono le_sup_left) (Submodule.toAddSubgroup_mono le_sup_left)`. Establish `hfg : M.FG`. Take `⟨k, hk, h⟩` from `hsub M le_sup_right`. Establish `hs : (stdLat E n).FG` using `Submodule.fg_pi fun _ => by`.

Rewrite using `[Submodule.one_eq_span]`. Conclude with `Submodule.fg_span_singleton _`. Apply `Submodule.fg_of_fg_map_injective (LinearMap.lsmul (𝓞 E) (Fin n → E) k) (fun x y hxy => smul_right_injective _ hk hxy)` to reduce the goal to its premises. Conclude with `hs.of_le (by rintro _ ⟨v, hv, rfl⟩; exact h v hv)`. Take `⟨s, rfl⟩` from `hfg`.

Use `key s fun x hx => Submodule.subset_span hx` as an intermediate fact. Rewrite `this` using `[sup_eq_right.2 inf_le_left]`. Then use the resulting hypothesis.
-/
theorem exists_index_ideal_inf_sup (E : Type) [Field E] [NumberField E] (n : ℕ)
    (M M' : Submodule (𝓞 E) (Fin n → E)) (hb : Bdd (M' ⊔ M))
    (ht : ∀ m ∈ M, ∃ a : 𝓞 E, a ≠ 0 ∧ a • m ∈ M') :
    ∃ 𝔞 : Ideal (𝓞 E), 𝔞 ≠ ⊥ ∧ detSpan (M ⊓ M') = 𝔞 • detSpan M ∧
      detSpan M' = 𝔞 • detSpan (M' ⊔ M) ∧
      Ideal.absNorm 𝔞 = (M ⊓ M').toAddSubgroup.relIndex M.toAddSubgroup := by
  classical
  have hsub : ∀ N : Submodule (𝓞 E) (Fin n → E), N ≤ M' ⊔ M → Bdd N := by
    intro N hN
    obtain ⟨k, hk, h⟩ := hb
    exact ⟨k, hk, fun v hv => h v (hN hv)⟩
  have key : ∀ s : Finset (Fin n → E), (∀ x ∈ s, x ∈ M) →
      ∃ 𝔞 : Ideal (𝓞 E), 𝔞 ≠ ⊥ ∧
        detSpan (M ⊓ M') = 𝔞 • detSpan ((M ⊓ M') ⊔ Submodule.span (𝓞 E) (s : Set (Fin n → E))) ∧
        detSpan M' = 𝔞 • detSpan (M' ⊔ Submodule.span (𝓞 E) (s : Set (Fin n → E))) ∧
        Ideal.absNorm 𝔞 = (M ⊓ M').toAddSubgroup.relIndex
          ((M ⊓ M') ⊔ Submodule.span (𝓞 E) (s : Set (Fin n → E))).toAddSubgroup := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; exact ⟨⊤, by simp, by simp, by simp, by simp⟩
    | insert m s _ ih =>
      intro hs
      obtain ⟨𝔞, h0, h1, h1', h2⟩ := ih fun x hx => hs x (Finset.mem_insert_of_mem hx)
      have hsM : Submodule.span (𝓞 E) (s : Set (Fin n → E)) ≤ M :=
        Submodule.span_le.2 fun x hx => hs x (Finset.mem_insert_of_mem hx)
      set N := (M ⊓ M') ⊔ Submodule.span (𝓞 E) (s : Set (Fin n → E)) with hN
      set S := M' ⊔ Submodule.span (𝓞 E) (s : Set (Fin n → E)) with hS
      have hm : m ∈ M := hs m (Finset.mem_insert_self _ _)
      have hmM : Submodule.span (𝓞 E) {m} ≤ M := (Submodule.span_singleton_le_iff_mem _ _).2 hm
      have e : (M ⊓ M') ⊔ Submodule.span (𝓞 E) ((insert m s : Finset (Fin n → E)) : Set (Fin n → E)) =
          N ⊔ Submodule.span (𝓞 E) {m} := by
        rw [Finset.coe_insert, Submodule.span_insert, hN, sup_assoc, sup_comm (Submodule.span _ {m})]
      have e' : M' ⊔ Submodule.span (𝓞 E) ((insert m s : Finset (Fin n → E)) : Set (Fin n → E)) =
          S ⊔ Submodule.span (𝓞 E) {m} := by
        rw [Finset.coe_insert, Submodule.span_insert, hS, sup_assoc, sup_comm (Submodule.span _ {m})]
      have hNS : N = M ⊓ S := by
        rw [hN, hS, inf_sup_assoc_of_le _ hsM]
      have hb1 : Bdd (N ⊔ Submodule.span (𝓞 E) {m}) :=
        hsub _ (le_sup_of_le_right (sup_le (sup_le inf_le_left hsM) hmM))
      have hb2 : Bdd (S ⊔ Submodule.span (𝓞 E) {m}) :=
        hsub _ (sup_le (sup_le_sup_left hsM _) (le_sup_of_le_right hmM))
      have hc : (N.comap (LinearMap.toSpanSingleton (𝓞 E) _ m) : Ideal (𝓞 E)) =
          S.comap (LinearMap.toSpanSingleton (𝓞 E) _ m) := by
        ext a
        rw [hNS]
        exact ⟨fun h => h.2, fun h => ⟨M.smul_mem a hm, h⟩⟩
      rw [e, e']
      refine ⟨𝔞 * (N.comap (LinearMap.toSpanSingleton (𝓞 E) _ m) : Ideal (𝓞 E)), ?_, ?_, ?_, ?_⟩
      · refine mul_ne_zero h0 ?_
        obtain ⟨a, ha, ham⟩ := ht m hm
        exact (Submodule.ne_bot_iff _).2
          ⟨a, (le_sup_left : M ⊓ M' ≤ N) ⟨M.smul_mem a hm, ham⟩, ha⟩
      · rw [h1, Submodule.mul_smul, ← detSpan_cyclic N m hb1]
      · rw [h1', hc, Submodule.mul_smul, ← detSpan_cyclic S m hb2]
      · rw [map_mul, h2, index_cyclic]
        exact AddSubgroup.relIndex_mul_relIndex _ _ _ (Submodule.toAddSubgroup_mono le_sup_left)
          (Submodule.toAddSubgroup_mono le_sup_left)
  have hfg : M.FG := by
    obtain ⟨k, hk, h⟩ := hsub M le_sup_right
    have hs : (stdLat E n).FG := Submodule.fg_pi fun _ => by
      rw [Submodule.one_eq_span]; exact Submodule.fg_span_singleton _
    apply Submodule.fg_of_fg_map_injective (LinearMap.lsmul (𝓞 E) (Fin n → E) k)
      (fun x y hxy => smul_right_injective _ hk hxy)
    exact hs.of_le (by rintro _ ⟨v, hv, rfl⟩; exact h v hv)
  obtain ⟨s, rfl⟩ := hfg
  have := key s fun x hx => Submodule.subset_span hx
  rwa [sup_eq_right.2 inf_le_left] at this

end GlobalTheory.BetaEx
