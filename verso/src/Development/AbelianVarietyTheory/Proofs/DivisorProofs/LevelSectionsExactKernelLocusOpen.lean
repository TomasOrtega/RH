import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverCompImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSemiAbelianImage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormallyUnramifiedAdjointRingActionScheme
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleSpreadSubring
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeSubsetOfGeom
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.LevTrivOpen

variable {S : Scheme.{0}}

/- English proof (translation)
Use `⟨fun h => h ⟨p, rfl⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `h _ ⟨q, rfl⟩`. Rewrite using `[Subsingleton.elim q p]` and apply the resulting hypothesis.
-/
theorem range_subset_iff_mem {k : Type} [Field k] (x : Sp k ⟶ S) (U : Set S) (p : Sp k) :
    Set.range x.base ⊆ U ↔ x.base p ∈ U := by
  refine ⟨fun h => h ⟨p, rfl⟩, ?_⟩
  rintro h _ ⟨q, rfl⟩
  rwa [Subsingleton.elim q p]

/- English proof (translation)
Establish `h0 : lev 0 = 1`. Use `hadd 0 0` as an intermediate fact. Rewrite `this` using `[add_zero]`. Conclude with `(mul_eq_left.1 this.symm)`. Proceed by induction on `n with`.

Consider the case `zero => rw [zero_smul, pow_zero, h0]`. Consider the case `succ n ih => rw [succ_nsmul, hadd, ih, pow_succ]`.
-/
theorem pow_nsmul {G : Over S} [GrpObj G] {h : ℕ} (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ G))
    (hadd : ∀ a b, lev (a + b) = lev a * lev b) (n : ℕ) (c : Fin h ⊕ Fin h → ℤ) : lev (n • c) = lev c ^ n := by
  have h0 : lev 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact (mul_eq_left.1 this.symm)
  induction n with
  | zero => rw [zero_smul, pow_zero, h0]
  | succ n ih => rw [succ_nsmul, hadd, ih, pow_succ]

end GlobalTheory.LevTrivOpen

open GlobalTheory.LevCover GlobalTheory.LevTrivOpen in
/- English proof (translation)
Introduce `S _ M t G _ _ h lev hab hM hadd hpow k _ _ x₀ hx₀`. Establish `hu : IsUnit (M : Γ(S, ⊤))`. Use `(GlobalTheory.SiegelTor.isUnit_natCast (n := M) (by omega)).map (t.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of (GlobalTheory.SiegelTor.cycAway M))).inv.hom)` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis. Take `⟨-, hfin, het⟩` from `GlobalTheory.GrpTangent.finiteEtale_mulN_torsion G (hG := hab) hu`.

Establish `hU : ∀ f : 𝟙_ (Over S) ⟶ G, ∃ U : S.Opens, IsClosed (U : Set S) ∧ (f ^ M = 1 → ∀ (k' : Type) [Field k'] [IsAlgClosed k'] (x : Sp k' ⟶ S), (toUnit (Over.mk x) ≫ f = 1 ↔ Set.range x.base ⊆ U))` using `fun f => by`. Distinguish the cases in `hf : f ^ M = 1`. Take `⟨U, hUc, HU⟩` from `GlobalTheory.TorsionSections.clopenCond_torsion_eq (n := M) (T := 𝟙_ (Over S)) hf (one_pow M)`. Use `⟨U, hUc, fun _ k' _ _ x => ?_⟩` and prove the remaining obligations. Use `HU (Over.mk x) (toUnit (Over.mk x))` as an intermediate fact.

Simplify using `only [MonObj.comp_one] at this`. Simplify using `using this`. Conclude with `⟨⊤, isClosed_univ, fun h => absurd h hf⟩`. Use `choose Uf hUc HU using hU`. Take `⟨κ, _, q, hq⟩` from `exists_finite_mod (Fin h ⊕ Fin h → ℤ) (show 0 < M by omega)`.

Set `P : (Fin h ⊕ Fin h → ℤ) → Prop` to `fun a => ∃ b, a = M • b`. Set `A : (Fin h ⊕ Fin h → ℤ) → Set S` to `fun a => {s | s ∈ (Uf (lev a) : Set S) ↔ P a}`. Establish `hAo : ∀ a, IsOpen (A a)` using `fun a => by`. Distinguish the cases in `hp : P a`. Use `(Uf (lev a)).isOpen using 1` and compare the differences between its conclusion and the goal.

Use extensionality with `s`. Simplify using `only [A, Set.mem_setOf_eq, hp, iff_true, SetLike.mem_coe]`. Use `(hUc (lev a)).isOpen_compl using 1` and compare the differences between its conclusion and the goal. Use extensionality with `s`. Simplify using `only [A, Set.mem_setOf_eq, hp, iff_false, Set.mem_compl_iff, SetLike.mem_coe]`.

Establish `hAq : ∀ a a', q a = q a' → A a = A a'` using `fun a a' e => by`. Take `⟨c, rfl⟩` from `hq a a' e`. Establish `hl : lev (a + M • c) = lev a` using `by rw [hadd, pow_nsmul lev hadd, hpow, _root_.mul_one]`. Establish `hP : P (a + M • c) ↔ P a` using `⟨fun ⟨b, hb⟩ => ⟨b - c, by rw [smul_sub, ← hb]; abel⟩, fun ⟨b, hb⟩ => ⟨b + c, by rw [hb, smul_add]⟩⟩`. Use extensionality with `s`.

Simplify using `only [A, Set.mem_setOf_eq, hl, hP]`. Set `pick : κ → (Fin h ⊕ Fin h → ℤ)` to `fun c => if hc : ∃ a, q a = c then hc.choose else 0`. Establish `hpick : ∀ a, A a = A (pick (q a))` using `fun a => by`. Establish `hc : ∃ a', q a' = q a` using `⟨a, rfl⟩`. Use `hAq _ _ ?_` and prove the remaining obligations.

Simplify using `only [pick, dif_pos hc]`. Conclude with `hc.choose_spec.symm`. Use `⟨⟨⋂ c, A (pick c), isOpen_iInter_of_finite fun c => hAo _⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨p, rfl⟩`. Simplify using `only [TopologicalSpace.Opens.coe_mk, Set.mem_iInter]`.

Introduce `c`. Use `show x₀.base p ∈ (Uf (lev (pick c)) : Set S) ↔ P (pick c)`. Rewrite using `[← range_subset_iff_mem, ← HU _ (hpow _) k x₀]`. Conclude with `hx₀ _`. Introduce `k' _ _ x hx a`.

Take `⟨p⟩` from `(inferInstance : Nonempty (Sp k'))`. Establish `h1` using `hx ⟨p, rfl⟩`. Simplify using `only [TopologicalSpace.Opens.coe_mk, Set.mem_iInter] at h1`. Establish `h2 : x.base p ∈ A a` using `by rw [hpick]; exact h1 _`. Rewrite using `[HU _ (hpow a) k' x, range_subset_iff_mem _ _ p]`.

Conclude with `h2`.
-/
theorem GlobalTheory.levTriv_locus_open : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (M : ℕ) (t : S ⟶ Sp (cycAway M)) (G : Over S) [GrpObj G] [IsCommMonObj G] (h : ℕ) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ G)), IsAbelianScheme G → 3 ≤ M → (∀ a b, lev (a + b) = lev a * lev b) → (∀ a, lev a ^ M = 1) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x₀ : Sp k ⟶ S), (∀ a, (toUnit (Over.mk x₀) ≫ lev a = 1 ↔ ∃ b, a = M • b)) → ∃ W : S.Opens, Set.range x₀.base ⊆ W ∧ ∀ (k' : Type) [Field k'] [IsAlgClosed k'] (x : Sp k' ⟶ S), Set.range x.base ⊆ W → ∀ a, (toUnit (Over.mk x) ≫ lev a = 1 ↔ ∃ b, a = M • b) := by
  intro S _ M t G _ _ h lev hab hM hadd hpow k _ _ x₀ hx₀
  have hu : IsUnit (M : Γ(S, ⊤)) := by
    have := (GlobalTheory.SiegelTor.isUnit_natCast (n := M) (by omega)).map
      (t.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of (GlobalTheory.SiegelTor.cycAway M))).inv.hom)
    rwa [map_natCast] at this
  obtain ⟨-, hfin, het⟩ := GlobalTheory.GrpTangent.finiteEtale_mulN_torsion G (hG := hab) hu
  have hU : ∀ f : 𝟙_ (Over S) ⟶ G, ∃ U : S.Opens, IsClosed (U : Set S) ∧ (f ^ M = 1 → ∀ (k' : Type) [Field k']
      [IsAlgClosed k'] (x : Sp k' ⟶ S), (toUnit (Over.mk x) ≫ f = 1 ↔ Set.range x.base ⊆ U)) := fun f => by
    by_cases hf : f ^ M = 1
    · obtain ⟨U, hUc, HU⟩ := GlobalTheory.TorsionSections.clopenCond_torsion_eq (n := M) (T := 𝟙_ (Over S)) hf (one_pow M)
      refine ⟨U, hUc, fun _ k' _ _ x => ?_⟩
      have := HU (Over.mk x) (toUnit (Over.mk x))
      simp only [MonObj.comp_one] at this
      simpa using this
    · exact ⟨⊤, isClosed_univ, fun h => absurd h hf⟩
  choose Uf hUc HU using hU
  classical
  obtain ⟨κ, _, q, hq⟩ := exists_finite_mod (Fin h ⊕ Fin h → ℤ) (show 0 < M by omega)
  let P : (Fin h ⊕ Fin h → ℤ) → Prop := fun a => ∃ b, a = M • b
  let A : (Fin h ⊕ Fin h → ℤ) → Set S := fun a => {s | s ∈ (Uf (lev a) : Set S) ↔ P a}
  have hAo : ∀ a, IsOpen (A a) := fun a => by
    by_cases hp : P a
    · convert (Uf (lev a)).isOpen using 1
      ext s
      simp only [A, Set.mem_setOf_eq, hp, iff_true, SetLike.mem_coe]
    · convert (hUc (lev a)).isOpen_compl using 1
      ext s
      simp only [A, Set.mem_setOf_eq, hp, iff_false, Set.mem_compl_iff, SetLike.mem_coe]
  have hAq : ∀ a a', q a = q a' → A a = A a' := fun a a' e => by
    obtain ⟨c, rfl⟩ := hq a a' e
    have hl : lev (a + M • c) = lev a := by rw [hadd, pow_nsmul lev hadd, hpow, _root_.mul_one]
    have hP : P (a + M • c) ↔ P a :=
      ⟨fun ⟨b, hb⟩ => ⟨b - c, by rw [smul_sub, ← hb]; abel⟩, fun ⟨b, hb⟩ => ⟨b + c, by rw [hb, smul_add]⟩⟩
    ext s
    simp only [A, Set.mem_setOf_eq, hl, hP]
  let pick : κ → (Fin h ⊕ Fin h → ℤ) := fun c => if hc : ∃ a, q a = c then hc.choose else 0
  have hpick : ∀ a, A a = A (pick (q a)) := fun a => by
    have hc : ∃ a', q a' = q a := ⟨a, rfl⟩
    refine hAq _ _ ?_
    simp only [pick, dif_pos hc]
    exact hc.choose_spec.symm
  refine ⟨⟨⋂ c, A (pick c), isOpen_iInter_of_finite fun c => hAo _⟩, ?_, ?_⟩
  · rintro _ ⟨p, rfl⟩
    simp only [TopologicalSpace.Opens.coe_mk, Set.mem_iInter]
    intro c
    show x₀.base p ∈ (Uf (lev (pick c)) : Set S) ↔ P (pick c)
    rw [← range_subset_iff_mem, ← HU _ (hpow _) k x₀]
    exact hx₀ _
  · intro k' _ _ x hx a
    obtain ⟨p⟩ := (inferInstance : Nonempty (Sp k'))
    have h1 := hx ⟨p, rfl⟩
    simp only [TopologicalSpace.Opens.coe_mk, Set.mem_iInter] at h1
    have h2 : x.base p ∈ A a := by rw [hpick]; exact h1 _
    rw [HU _ (hpow a) k' x, range_subset_iff_mem _ _ p]
    exact h2
