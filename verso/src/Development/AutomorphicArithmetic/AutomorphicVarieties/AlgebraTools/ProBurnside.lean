import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ProfDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.BurnsideHom

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

/- English proof (translation)
Introduce `h`. Proceed by induction on `h with`. Consider the case `zero`. Introduce `S _ hS`. Use `⟨Fin.elim0, fun f hf _ => ?_⟩` and prove the remaining obligations.

Establish `hbot : S = ⊥` using `Subgroup.eq_bot_of_card_le S (by simpa using hS)`. Rewrite `hf` using `[hbot, Subgroup.mem_bot]`. Conclude with `hf`. Consider the case `succ h ih`. Introduce `S hfin hS`.

Distinguish the cases in `htriv : ∀ f ∈ S, f = 1`. Conclude with `⟨fun _ => 1, fun f hf _ => htriv f hf⟩`. Use `push_neg at htriv`. Take `⟨f₀, hf₀, hne⟩` from `htriv`. Choose the witnesses or unpack the hypotheses as in `⟨g, hg⟩ : ∃ g, f₀ g ≠ 1 := by`.

Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `hne (MonoidHom.ext hc)`. Set `ev : S →* Multiplicative (ZMod l)` to `{ toFun := fun f => (f : G →* Multiplicative (ZMod l)) g map_one' := rfl map_mul' := fun _ _ => rfl }`. Establish `hrange : Nat.card ev.range = l`.

Establish `hdvd : Nat.card ev.range ∣ l`. Use `Subgroup.card_subgroup_dvd_card ev.range` as an intermediate fact. Simplify `this` using `[Nat.card_zmod]`. Break down `(Nat.dvd_prime hl.out).mp hdvd with h1 | h1` into its components or cases. It suffices to derive a contradiction.

Establish `hbot : ev.range = ⊥` using `Subgroup.eq_bot_of_card_eq _ h1`. Establish `hmem : ev ⟨f₀, hf₀⟩ ∈ ev.range` using `⟨_, rfl⟩`. Rewrite `hmem` using `[hbot, Subgroup.mem_bot]`. Conclude with `hg hmem`. Conclude with `h1`.

Establish `hcardS : Nat.card ev.ker * l = Nat.card S`. Use `Subgroup.card_mul_index ev.ker` as an intermediate fact. Rewrite `this` using `[Subgroup.index_ker, hrange]`. Conclude with `this`. Set `S' : Subgroup (G →* Multiplicative (ZMod l))` to `ev.ker.map S.subtype`.

Establish `hS' : Nat.card S' = Nat.card ev.ker` using `Subgroup.card_map_of_injective S.subtype_injective`. Establish `hfin' : Finite S'` using `Nat.finite_of_card_ne_zero (by`. Rewrite using `[hS']`. Introduce `h0`. Establish `: Nat.card S = 0` using `by rw [← hcardS, h0, zero_mul]`.

Conclude with `(Nat.card_pos (α := S)).ne' this)`. Establish `hle : Nat.card S' ≤ l ^ h`. Rewrite using `[hS']`. Establish `hlpos : 0 < l` using `hl.out.pos`. Establish `: Nat.card ev.ker * l ≤ l ^ h * l`.

Rewrite using `[hcardS, ← pow_succ]`. Conclude with `hS`. Conclude with `Nat.le_of_mul_le_mul_right this hlpos`. Take `⟨x', hx'⟩` from `ih S' hfin' hle`. Use `⟨Fin.cons g x', fun f hf hall => ?_⟩` and prove the remaining obligations.

Establish `hfg : f g = 1` using `by simpa using hall 0`. Establish `hmem : f ∈ S'` using `⟨⟨f, hf⟩, hfg, rfl⟩`. Conclude with `hx' f hmem fun i => by simpa using hall i.succ`.
-/
private theorem count_step (l : ℕ) [hl : Fact l.Prime] (G : Type) [Group G] :
    ∀ (h : ℕ) (S : Subgroup (G →* Multiplicative (ZMod l))), Finite S → Nat.card S ≤ l ^ h →
      ∃ x : Fin h → G, ∀ f ∈ S, (∀ i, f (x i) = 1) → f = 1 := by
  intro h
  induction h with
  | zero =>
    intro S _ hS
    refine ⟨Fin.elim0, fun f hf _ => ?_⟩
    have hbot : S = ⊥ := Subgroup.eq_bot_of_card_le S (by simpa using hS)
    rw [hbot, Subgroup.mem_bot] at hf
    exact hf
  | succ h ih =>
    intro S hfin hS
    by_cases htriv : ∀ f ∈ S, f = 1
    · exact ⟨fun _ => 1, fun f hf _ => htriv f hf⟩
    push_neg at htriv
    obtain ⟨f₀, hf₀, hne⟩ := htriv
    obtain ⟨g, hg⟩ : ∃ g, f₀ g ≠ 1 := by
      by_contra hc
      push_neg at hc
      exact hne (MonoidHom.ext hc)
    let ev : S →* Multiplicative (ZMod l) :=
      { toFun := fun f => (f : G →* Multiplicative (ZMod l)) g
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hrange : Nat.card ev.range = l := by
      have hdvd : Nat.card ev.range ∣ l := by
        have := Subgroup.card_subgroup_dvd_card ev.range
        simpa [Nat.card_zmod] using this
      rcases (Nat.dvd_prime hl.out).mp hdvd with h1 | h1
      · exfalso
        have hbot : ev.range = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
        have hmem : ev ⟨f₀, hf₀⟩ ∈ ev.range := ⟨_, rfl⟩
        rw [hbot, Subgroup.mem_bot] at hmem
        exact hg hmem
      · exact h1
    have hcardS : Nat.card ev.ker * l = Nat.card S := by
      have := Subgroup.card_mul_index ev.ker
      rw [Subgroup.index_ker, hrange] at this
      exact this
    let S' : Subgroup (G →* Multiplicative (ZMod l)) := ev.ker.map S.subtype
    have hS' : Nat.card S' = Nat.card ev.ker := Subgroup.card_map_of_injective S.subtype_injective
    have hfin' : Finite S' := Nat.finite_of_card_ne_zero (by
      rw [hS']
      intro h0
      have : Nat.card S = 0 := by rw [← hcardS, h0, zero_mul]
      exact (Nat.card_pos (α := S)).ne' this)
    have hle : Nat.card S' ≤ l ^ h := by
      rw [hS']
      have hlpos : 0 < l := hl.out.pos
      have : Nat.card ev.ker * l ≤ l ^ h * l := by
        rw [hcardS, ← pow_succ]
        exact hS
      exact Nat.le_of_mul_le_mul_right this hlpos
    obtain ⟨x', hx'⟩ := ih S' hfin' hle
    refine ⟨Fin.cons g x', fun f hf hall => ?_⟩
    have hfg : f g = 1 := by simpa using hall 0
    have hmem : f ∈ S' := ⟨⟨f, hf⟩, hfg, rfl⟩
    exact hx' f hmem fun i => by simpa using hall i.succ

/- English proof (translation)
Introduce `l _ G _ _ _ _ _ hpro`. Establish `partA : ∀ s : Set G, (∀ f : G →* Multiplicative (ZMod l), IsOpen (f.ker : Set G) → (∀ g ∈ s, f g = 1) → f = 1) → TopGen s`. Introduce `s hs`. Set `H` to `(Subgroup.closure s).topologicalClosure`. Establish `hHc : IsClosed (H : Set G)` using `Subgroup.isClosed_topologicalClosure _`.

Use `show Dense (Subgroup.closure s : Set G)`. Rewrite using `[dense_iff_closure_eq, Set.eq_univ_iff_forall]`. Introduce `g`. Assume the negation of the conclusion as `hg`. Establish `hg' : g ∉ (H : Set G)`.

Rewrite using `[Subgroup.topologicalClosure_coe]`. Conclude with `hg`. Take `⟨N, hN⟩` from `ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one (U := (fun n => g * n) ⁻¹' (H : Set G)ᶜ) (hHc.isOpen_compl.preimage (continuous_const_mul g)) (by simp only [Set.mem_preimage, Set.mem_compl_iff, mul_one]; exact hg')`. Set `Ns : Subgroup G` to `N.toOpenSubgroup`. Use `haveI : Ns.Normal := N.isNormal'`.

Use `haveI : Finite (G ⧸ Ns) := Subgroup.quotient_finite_of_isOpen _ N.isOpen'`. Set `K` to `H.map (QuotientGroup.mk' Ns)`. Establish `hK : K = ⊤`. Use `UpperTheory.V.CF.burnsideHom l (G ⧸ Ns) (hpro N) K (fun f hf => ?_)` and prove the remaining obligations. Set `F` to `f.comp (QuotientGroup.mk' Ns)`.

Establish `hFo : IsOpen (F.ker : Set G)`. Use `Subgroup.isOpen_mono (H₁ := Ns) (fun x hx => ?_) N.isOpen'` and prove the remaining obligations. Rewrite using `[MonoidHom.mem_ker]`. Simplify using `[F, (QuotientGroup.eq_one_iff x).mpr hx]`. Establish `hF : F = 1` using `hs F hFo (fun x hx => by`.

Establish `hxH : x ∈ H` using `Subgroup.le_topologicalClosure _ (Subgroup.subset_closure hx)`. Conclude with `hf ⟨x, hxH, rfl⟩)`. Use extensionality with `q`. Simplify `DFunLike.congr_fun hF q` using `[F]`. Establish `hgK : (QuotientGroup.mk' Ns g) ∈ K`.

Rewrite using `[hK]`. Conclude with `Subgroup.mem_top _`. Take `⟨y, hyH, hy⟩` from `hgK`. Establish `hyg : y⁻¹ * g ∈ Ns` using `QuotientGroup.eq.mp hy`. Establish `hn : g⁻¹ * y ∈ Ns`.

Use `Ns.inv_mem hyg` as an intermediate fact. Simplify using `using this`. Establish `hU` using `hN hn`. Simplify using `only [Set.mem_preimage, Set.mem_compl_iff, mul_inv_cancel_left] at hU`. Conclude with `hU hyH`.

Use `⟨partA, fun h hfin hcard => ?_⟩` and prove the remaining obligations. Set `S : Subgroup (G →* Multiplicative (ZMod l))` to `{ carrier := {f | IsOpen (f.ker : Set G)} one_mem' := by show IsOpen ((1 : G →* Multiplicative (ZMod l)).ker : Set G)`. Rewrite using `[MonoidHom.ker_one]`. Conclude with `isOpen_univ`. Use the proof step `mul_mem' := fun {a b} ha hb => by show IsOpen ((a * b).ker : Set G)`.

Use `Subgroup.isOpen_mono (H₁ := a.ker ⊓ b.ker) (fun x hx => ?_) ?_` and prove the remaining obligations. Rewrite `hx` using `[Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker]`. Rewrite using `[MonoidHom.mem_ker, MonoidHom.mul_apply, hx.1, hx.2, one_mul]`. Rewrite using `[Subgroup.coe_inf]`. Conclude with `IsOpen.inter ha hb`.

Use the proof step `inv_mem' := fun {a} ha => by show IsOpen ((a⁻¹).ker : Set G)`. Establish `: (a⁻¹).ker = a.ker`. Use extensionality with `x`. Simplify using `[MonoidHom.mem_ker]`. Rewrite using `[this]`.

Conclude with `ha }`. Use `haveI : Finite S := hfin.to_subtype`. Establish `hle : Nat.card S ≤ l ^ h`. Establish `: Nat.card S = {f : G →* Multiplicative (ZMod l) | IsOpen (f.ker : Set G)}.ncard` using `Nat.card_coe_set_eq _`. Rewrite using `[this]`.

Conclude with `hcard`. Take `⟨x, hx⟩` from `count_step l G h S inferInstance hle`. Conclude with `⟨x, partA _ fun f hf hv => hx f hf fun i => hv _ ⟨i, rfl⟩⟩`.
-/
theorem UpperTheory.V.AlgebraTools.topGen_of_hom :
    ∀ (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G], IsProL l G →
      (∀ s : Set G, (∀ f : G →* Multiplicative (ZMod l), IsOpen (f.ker : Set G) → (∀ g ∈ s, f g = 1) → f = 1) → TopGen s) ∧
      (∀ h : ℕ, {f : G →* Multiplicative (ZMod l) | IsOpen (f.ker : Set G)}.Finite →
        {f : G →* Multiplicative (ZMod l) | IsOpen (f.ker : Set G)}.ncard ≤ l ^ h → ∃ x : Fin h → G, TopGen (Set.range x)) := by
  intro l _ G _ _ _ _ _ hpro
  have partA : ∀ s : Set G, (∀ f : G →* Multiplicative (ZMod l), IsOpen (f.ker : Set G) →
      (∀ g ∈ s, f g = 1) → f = 1) → TopGen s := by
    intro s hs
    let H := (Subgroup.closure s).topologicalClosure
    have hHc : IsClosed (H : Set G) := Subgroup.isClosed_topologicalClosure _
    show Dense (Subgroup.closure s : Set G)
    rw [dense_iff_closure_eq, Set.eq_univ_iff_forall]
    intro g
    by_contra hg
    have hg' : g ∉ (H : Set G) := by
      rw [Subgroup.topologicalClosure_coe]
      exact hg
    obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
      (U := (fun n => g * n) ⁻¹' (H : Set G)ᶜ)
      (hHc.isOpen_compl.preimage (continuous_const_mul g))
      (by simp only [Set.mem_preimage, Set.mem_compl_iff, mul_one]; exact hg')
    let Ns : Subgroup G := N.toOpenSubgroup
    haveI : Ns.Normal := N.isNormal'
    haveI : Finite (G ⧸ Ns) := Subgroup.quotient_finite_of_isOpen _ N.isOpen'
    let K := H.map (QuotientGroup.mk' Ns)
    have hK : K = ⊤ := by
      refine UpperTheory.V.CF.burnsideHom l (G ⧸ Ns) (hpro N) K (fun f hf => ?_)
      let F := f.comp (QuotientGroup.mk' Ns)
      have hFo : IsOpen (F.ker : Set G) := by
        refine Subgroup.isOpen_mono (H₁ := Ns) (fun x hx => ?_) N.isOpen'
        rw [MonoidHom.mem_ker]
        simp [F, (QuotientGroup.eq_one_iff x).mpr hx]
      have hF : F = 1 := hs F hFo (fun x hx => by
        have hxH : x ∈ H := Subgroup.le_topologicalClosure _ (Subgroup.subset_closure hx)
        exact hf ⟨x, hxH, rfl⟩)
      ext q
      simpa [F] using DFunLike.congr_fun hF q
    have hgK : (QuotientGroup.mk' Ns g) ∈ K := by
      rw [hK]
      exact Subgroup.mem_top _
    obtain ⟨y, hyH, hy⟩ := hgK
    have hyg : y⁻¹ * g ∈ Ns := QuotientGroup.eq.mp hy
    have hn : g⁻¹ * y ∈ Ns := by
      have := Ns.inv_mem hyg
      simpa using this
    have hU := hN hn
    simp only [Set.mem_preimage, Set.mem_compl_iff, mul_inv_cancel_left] at hU
    exact hU hyH
  refine ⟨partA, fun h hfin hcard => ?_⟩
  let S : Subgroup (G →* Multiplicative (ZMod l)) :=
    { carrier := {f | IsOpen (f.ker : Set G)}
      one_mem' := by
        show IsOpen ((1 : G →* Multiplicative (ZMod l)).ker : Set G)
        rw [MonoidHom.ker_one]
        exact isOpen_univ
      mul_mem' := fun {a b} ha hb => by
        show IsOpen ((a * b).ker : Set G)
        refine Subgroup.isOpen_mono (H₁ := a.ker ⊓ b.ker) (fun x hx => ?_) ?_
        · rw [Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker] at hx
          rw [MonoidHom.mem_ker, MonoidHom.mul_apply, hx.1, hx.2, one_mul]
        · rw [Subgroup.coe_inf]
          exact IsOpen.inter ha hb
      inv_mem' := fun {a} ha => by
        show IsOpen ((a⁻¹).ker : Set G)
        have : (a⁻¹).ker = a.ker := by
          ext x
          simp [MonoidHom.mem_ker]
        rw [this]
        exact ha }
  haveI : Finite S := hfin.to_subtype
  have hle : Nat.card S ≤ l ^ h := by
    have : Nat.card S = {f : G →* Multiplicative (ZMod l) | IsOpen (f.ker : Set G)}.ncard :=
      Nat.card_coe_set_eq _
    rw [this]
    exact hcard
  obtain ⟨x, hx⟩ := count_step l G h S inferInstance hle
  exact ⟨x, partA _ fun f hf hv => hx f hf fun i => hv _ ⟨i, rfl⟩⟩
