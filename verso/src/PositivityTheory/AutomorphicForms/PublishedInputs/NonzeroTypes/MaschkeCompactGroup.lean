import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.SmoothRepIrreducibleSubcontainingVector

noncomputable section

namespace UpperTheory.NonzeroTypeTheory.MaschkeCompactGroup

variable {K : Type} [Group K] {m : ℕ}

/- English proof (translation)
Use `Subgroup.isOpen_of_mem_nhds (MonoidHom.ker V) (g := 1) (Filter.mem_of_superset ((isOpen_iInter_of_finite fun i : Fin m => hs (Pi.single i 1)).mem_nhds (by simp)) fun g hg => ?_)` and prove the remaining obligations. Use `MonoidHom.mem_ker.2 ((Pi.basisFun ℂ (Fin m)).ext fun i => ?_)` and prove the remaining obligations. Rewrite using `[Pi.basisFun_apply]`. Conclude with `Set.mem_iInter.1 hg i`.
-/
theorem ker_isOpen [TopologicalSpace K] [IsTopologicalGroup K] (V : Representation ℂ K (Fin m → ℂ))
    (hs : GlobalTheory.PRep.IsSmooth V) : IsOpen ((MonoidHom.ker V : Subgroup K) : Set K) := by
  refine Subgroup.isOpen_of_mem_nhds (MonoidHom.ker V) (g := 1) (Filter.mem_of_superset
    ((isOpen_iInter_of_finite fun i : Fin m => hs (Pi.single i 1)).mem_nhds (by simp)) fun g hg => ?_)
  refine MonoidHom.mem_ker.2 ((Pi.basisFun ℂ (Fin m)).ext fun i => ?_)
  rw [Pi.basisFun_apply]
  exact Set.mem_iInter.1 hg i

/- English proof (translation)
Establish `: Finite (K ⧸ MonoidHom.ker V)` using `Subgroup.quotient_finite_of_isOpen _ (ker_isOpen V hs)`. Set `_ : Fintype (K ⧸ MonoidHom.ker V)` to `Fintype.ofFinite _`. Set `ρ : K ⧸ MonoidHom.ker V →* Module.End ℂ (Fin m → ℂ)` to `QuotientGroup.lift (MonoidHom.ker V) V le_rfl`. Establish `hρ : ∀ k : K, ρ (k : K ⧸ MonoidHom.ker V) = V k` using `fun k => rfl`. Establish `hmul : ∀ a b : K ⧸ MonoidHom.ker V, ∀ w, ρ a (ρ b w) = ρ (a * b) w` using `fun a b w => by`.

Rewrite using `[map_mul]`. Both sides reduce to the same expression. Establish `hρU : ∀ g, ∀ u ∈ U, ρ g u ∈ U`. Introduce `g u hu`. Take `⟨k, rfl⟩` from `QuotientGroup.mk_surjective g`.

Rewrite using `[hρ]`. Conclude with `hU k u hu`. Take `⟨T, hT⟩` from `Submodule.exists_isCompl U`. Set `π` to `U.projection T hT`. Establish `hπU : ∀ v, π v ∈ U` using `fun v => Submodule.projection_apply_mem hT v`.

Establish `hπid : ∀ u ∈ U, π u = u` using `fun u hu => Submodule.projection_apply_of_mem_left hT hu`. Set `P : Module.End ℂ (Fin m → ℂ)` to `∑ g : K ⧸ MonoidHom.ker V, (ρ g).comp (π.comp (ρ g⁻¹))`. Establish `hP : ∀ v, P v = ∑ g : K ⧸ MonoidHom.ker V, ρ g (π (ρ g⁻¹ v))` using `fun v => by`. Simplify using `only [P, LinearMap.sum_apply, LinearMap.comp_apply]`. Establish `hPU : ∀ v, P v ∈ U` using `fun v => by`.

Rewrite using `[hP]`. Conclude with `Submodule.sum_mem _ fun g _ => hρU g _ (hπU _)`. Establish `hPid : ∀ u ∈ U, P u = Fintype.card (K ⧸ MonoidHom.ker V) • u`. Introduce `u hu`. Establish `h1 : ∀ g : K ⧸ MonoidHom.ker V, ρ g (π (ρ g⁻¹ u)) = u` using `fun g => by`.

Rewrite using `[hπid _ (hρU _ _ hu), hmul, mul_inv_cancel, map_one]`. Both sides reduce to the same expression. Rewrite using `[hP, Finset.sum_congr rfl fun g _ => h1 g, Finset.sum_const, Finset.card_univ]`. Establish `hPeq : ∀ h v, P (ρ h v) = ρ h (P v)`. Introduce `h v`.

Rewrite using `[hP, hP, map_sum]`. Use `Fintype.sum_equiv (Equiv.mulLeft h⁻¹) _ _ fun x => ?_` and prove the remaining obligations. Simplify using `only [Equiv.coe_mulLeft]`. Rewrite using `[hmul h, mul_inv_cancel_left, mul_inv_rev, inv_inv, ← hmul]`. Establish `hc : (Fintype.card (K ⧸ MonoidHom.ker V) : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 Fintype.card_ne_zero`.

Set `f : (Fin m → ℂ) →ₗ[ℂ] U` to `LinearMap.codRestrict U (((Fintype.card (K ⧸ MonoidHom.ker V) : ℂ)⁻¹) • P) (fun v => U.smul_mem _ (hPU v))`. Establish `hf : ∀ x : U, f x = x`. Introduce `x`. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `((Fintype.card (K ⧸ MonoidHom.ker V) : ℂ)⁻¹) • P x = x`.

Rewrite using `[hPid _ x.2, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]`. Establish `hker : ∀ x, x ∈ LinearMap.ker f ↔ P x = 0`. Introduce `x`. Rewrite using `[LinearMap.mem_ker, ← Submodule.coe_eq_zero]`. Express the relevant statement in the definitionally equal form `((Fintype.card (K ⧸ MonoidHom.ker V) : ℂ)⁻¹) • P x = 0 ↔ P x = 0`.

Rewrite using `[smul_eq_zero]`. Simplify using `[hc]`. Use `⟨LinearMap.ker f, LinearMap.isCompl_of_proj hf, fun k s hs => ?_⟩` and prove the remaining obligations. Rewrite `hs`, the goal using `[hker]`. Rewrite using `[← hρ, hPeq, hs, map_zero]`.
-/
theorem maschke [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
    (V : Representation ℂ K (Fin m → ℂ)) (hs : GlobalTheory.PRep.IsSmooth V)
    (U : Submodule ℂ (Fin m → ℂ)) (hU : ∀ k, ∀ u ∈ U, V k u ∈ U) :
    ∃ S : Submodule ℂ (Fin m → ℂ), IsCompl U S ∧ ∀ k, ∀ s ∈ S, V k s ∈ S := by
  classical
  have : Finite (K ⧸ MonoidHom.ker V) := Subgroup.quotient_finite_of_isOpen _ (ker_isOpen V hs)
  let _ : Fintype (K ⧸ MonoidHom.ker V) := Fintype.ofFinite _
  let ρ : K ⧸ MonoidHom.ker V →* Module.End ℂ (Fin m → ℂ) :=
    QuotientGroup.lift (MonoidHom.ker V) V le_rfl
  have hρ : ∀ k : K, ρ (k : K ⧸ MonoidHom.ker V) = V k := fun k => rfl
  have hmul : ∀ a b : K ⧸ MonoidHom.ker V, ∀ w, ρ a (ρ b w) = ρ (a * b) w := fun a b w => by
    rw [map_mul]; rfl
  have hρU : ∀ g, ∀ u ∈ U, ρ g u ∈ U := by
    intro g u hu
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective g
    rw [hρ]
    exact hU k u hu
  obtain ⟨T, hT⟩ := Submodule.exists_isCompl U
  let π := U.projection T hT
  have hπU : ∀ v, π v ∈ U := fun v => Submodule.projection_apply_mem hT v
  have hπid : ∀ u ∈ U, π u = u := fun u hu => Submodule.projection_apply_of_mem_left hT hu
  let P : Module.End ℂ (Fin m → ℂ) := ∑ g : K ⧸ MonoidHom.ker V, (ρ g).comp (π.comp (ρ g⁻¹))
  have hP : ∀ v, P v = ∑ g : K ⧸ MonoidHom.ker V, ρ g (π (ρ g⁻¹ v)) := fun v => by
    simp only [P, LinearMap.sum_apply, LinearMap.comp_apply]
  have hPU : ∀ v, P v ∈ U := fun v => by
    rw [hP]
    exact Submodule.sum_mem _ fun g _ => hρU g _ (hπU _)
  have hPid : ∀ u ∈ U, P u = Fintype.card (K ⧸ MonoidHom.ker V) • u := by
    intro u hu
    have h1 : ∀ g : K ⧸ MonoidHom.ker V, ρ g (π (ρ g⁻¹ u)) = u := fun g => by
      rw [hπid _ (hρU _ _ hu), hmul, mul_inv_cancel, map_one]
      rfl
    rw [hP, Finset.sum_congr rfl fun g _ => h1 g, Finset.sum_const, Finset.card_univ]
  have hPeq : ∀ h v, P (ρ h v) = ρ h (P v) := by
    intro h v
    rw [hP, hP, map_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft h⁻¹) _ _ fun x => ?_
    simp only [Equiv.coe_mulLeft]
    rw [hmul h, mul_inv_cancel_left, mul_inv_rev, inv_inv, ← hmul]
  have hc : (Fintype.card (K ⧸ MonoidHom.ker V) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  let f : (Fin m → ℂ) →ₗ[ℂ] U :=
    LinearMap.codRestrict U (((Fintype.card (K ⧸ MonoidHom.ker V) : ℂ)⁻¹) • P)
      (fun v => U.smul_mem _ (hPU v))
  have hf : ∀ x : U, f x = x := by
    intro x
    apply Subtype.ext
    change ((Fintype.card (K ⧸ MonoidHom.ker V) : ℂ)⁻¹) • P x = x
    rw [hPid _ x.2, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have hker : ∀ x, x ∈ LinearMap.ker f ↔ P x = 0 := by
    intro x
    rw [LinearMap.mem_ker, ← Submodule.coe_eq_zero]
    change ((Fintype.card (K ⧸ MonoidHom.ker V) : ℂ)⁻¹) • P x = 0 ↔ P x = 0
    rw [smul_eq_zero]
    simp [hc]
  refine ⟨LinearMap.ker f, LinearMap.isCompl_of_proj hf, fun k s hs => ?_⟩
  rw [hker] at hs ⊢
  rw [← hρ, hPeq, hs, map_zero]

end UpperTheory.NonzeroTypeTheory.MaschkeCompactGroup

namespace UpperTheory.NonzeroTypeTheory

open MaschkeCompactGroup in
/- English proof (translation)
Introduce `K _ _ _ _ m V hs v0 hv0`. Establish `hbot : (∀ k, ∀ w ∈ (⊥ : Submodule ℂ (Fin m → ℂ)), V k w ∈ (⊥ : Submodule ℂ (Fin m → ℂ))) ∧ v0 ∉ (⊥ : Submodule ℂ (Fin m → ℂ))`. Use `⟨fun k w hw => ?_, fun h => hv0 ((Submodule.mem_bot ℂ).1 h)⟩` and prove the remaining obligations. Rewrite `hw`, the goal using `[Submodule.mem_bot]`. Rewrite using `[hw, map_zero]`.

Take `⟨U, ⟨hUst, hv0U⟩, hUmax⟩` from `set_has_maximal_iff_noetherian.mpr inferInstance {W : Submodule ℂ (Fin m → ℂ) | (∀ k, ∀ w ∈ W, V k w ∈ W) ∧ v0 ∉ W} ⟨⊥, hbot⟩`. Take `⟨S, hUS, hSst⟩` from `maschke V hs U hUst`. Set `p` to `S.projection U hUS.symm`. Establish `hpS : ∀ v, p v ∈ S` using `fun v => Submodule.projection_apply_mem hUS.symm v`. Establish `hpid : ∀ s ∈ S, p s = s` using `fun s hs => Submodule.projection_apply_of_mem_left hUS.symm hs`.

Establish `hp0 : ∀ v, p v = 0 ↔ v ∈ U` using `fun v => Submodule.projection_apply_eq_zero_iff hUS.symm`. Establish `hdec : ∀ v, v - p v ∈ U` using `fun v => Submodule.sub_projection_mem hUS.symm v`. Establish `hpU : ∀ u ∈ U, p u = 0` using `fun u hu => (hp0 u).2 hu`. Establish `hpv0 : p v0 ≠ 0` using `fun h => hv0U ((hp0 v0).1 h)`. Establish `key : ∀ W : Submodule ℂ (Fin m → ℂ), W ≤ S → (∀ k, ∀ w ∈ W, V k w ∈ W) → W ≠ ⊥ → p v0 ∈ W`.

Introduce `W hWS hWst hW0`. Establish `hsup : ∀ k, ∀ x ∈ U ⊔ W, V k x ∈ U ⊔ W`. Introduce `k x hx`. Take `⟨u, hu, w, hw, rfl⟩` from `Submodule.mem_sup.1 hx`. Rewrite using `[map_add]`.

Conclude with `Submodule.add_mem_sup (hUst k u hu) (hWst k w hw)`. Establish `hmem : v0 ∈ U ⊔ W`. Assume the negation of the conclusion as `hn`. Use `hUmax (U ⊔ W) ⟨hsup, hn⟩ (lt_of_le_of_ne le_sup_left fun heq => hW0 ?_)` and prove the remaining obligations. Use `eq_bot_iff.2 ((le_inf (le_sup_right.trans heq.ge) hWS).trans (disjoint_iff.1 hUS.disjoint).le)` and prove the remaining obligations.

Take `⟨u, hu, w, hw, hsum⟩` from `Submodule.mem_sup.1 hmem`. Rewrite using `[← hsum, map_add, hpU u hu, zero_add, hpid w (hWS hw)]`. Conclude with `hw`. Use `⟨S, p, fun h => hpv0 ?_, hSst, fun S' hS'S hS'st => ?_, hpS, hpid, fun k v => ?_, hpv0⟩` and prove the remaining obligations. Use `hpS v0` as an intermediate fact.

Rewrite `this` using `[h, Submodule.mem_bot]`. Conclude with `this`. Distinguish the cases in `h0 : S' = ⊥`. Conclude with `Or.inl h0`. Use `right`.

Establish `h1` using `key S' hS'S hS'st h0`. Take `⟨T, hST, hTst⟩` from `maschke V hs S' hS'st`. Establish `hST0 : S ⊓ T = ⊥`. Assume the negation of the conclusion as `hn`. Establish `h2` using `key (S ⊓ T) inf_le_left (fun k x hx => Submodule.mem_inf.2 ⟨hSst k x (Submodule.mem_inf.1 hx).1, hTst k x (Submodule.mem_inf.1 hx).2⟩) hn`.

Establish `h3 : p v0 ∈ S' ⊓ T` using `Submodule.mem_inf.2 ⟨h1, (Submodule.mem_inf.1 h2).2⟩`. Rewrite `h3` using `[disjoint_iff.1 hST.disjoint, Submodule.mem_bot]`. Conclude with `hpv0 h3`. Use `le_antisymm hS'S fun s hs => ?_` and prove the remaining obligations. Establish `hs' : s ∈ S' ⊔ T` using `by rw [hST.sup_eq_top]; exact Submodule.mem_top`.

Take `⟨a, ha, t, ht, hat⟩` from `Submodule.mem_sup.1 hs'`. Establish `htS : t ∈ S`. Establish `: t = s - a` using `by rw [← hat]; abel`. Rewrite using `[this]`. Conclude with `S.sub_mem hs (hS'S ha)`.

Establish `ht0 : t = 0`. Establish `: t ∈ S ⊓ T` using `Submodule.mem_inf.2 ⟨htS, ht⟩`. Rewrite `this` using `[hST0, Submodule.mem_bot]`. Then use the resulting hypothesis. Rewrite using `[← hat, ht0, add_zero]`. Conclude with `ha`.

Establish `hv : V k v = V k (p v) + V k (v - p v)`. Rewrite using `[← map_add]`. Use `congr 1`. Normalize the expressions using the abelian group laws. Rewrite using `[hv, map_add, hpid _ (hSst k _ (hpS v)), hpU _ (hUst k _ (hdec v)), add_zero]`.
-/
theorem invariantComplement_holds : SmoothRepIrreducibleSubcontainingVector := by
  intro K _ _ _ _ m V hs v0 hv0
  classical
  have hbot : (∀ k, ∀ w ∈ (⊥ : Submodule ℂ (Fin m → ℂ)), V k w ∈ (⊥ : Submodule ℂ (Fin m → ℂ))) ∧
      v0 ∉ (⊥ : Submodule ℂ (Fin m → ℂ)) := by
    refine ⟨fun k w hw => ?_, fun h => hv0 ((Submodule.mem_bot ℂ).1 h)⟩
    rw [Submodule.mem_bot] at hw ⊢
    rw [hw, map_zero]
  obtain ⟨U, ⟨hUst, hv0U⟩, hUmax⟩ := set_has_maximal_iff_noetherian.mpr inferInstance
    {W : Submodule ℂ (Fin m → ℂ) | (∀ k, ∀ w ∈ W, V k w ∈ W) ∧ v0 ∉ W} ⟨⊥, hbot⟩
  obtain ⟨S, hUS, hSst⟩ := maschke V hs U hUst
  let p := S.projection U hUS.symm
  have hpS : ∀ v, p v ∈ S := fun v => Submodule.projection_apply_mem hUS.symm v
  have hpid : ∀ s ∈ S, p s = s := fun s hs => Submodule.projection_apply_of_mem_left hUS.symm hs
  have hp0 : ∀ v, p v = 0 ↔ v ∈ U := fun v => Submodule.projection_apply_eq_zero_iff hUS.symm
  have hdec : ∀ v, v - p v ∈ U := fun v => Submodule.sub_projection_mem hUS.symm v
  have hpU : ∀ u ∈ U, p u = 0 := fun u hu => (hp0 u).2 hu
  have hpv0 : p v0 ≠ 0 := fun h => hv0U ((hp0 v0).1 h)

  have key : ∀ W : Submodule ℂ (Fin m → ℂ), W ≤ S → (∀ k, ∀ w ∈ W, V k w ∈ W) → W ≠ ⊥ → p v0 ∈ W := by
    intro W hWS hWst hW0
    have hsup : ∀ k, ∀ x ∈ U ⊔ W, V k x ∈ U ⊔ W := by
      intro k x hx
      obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.1 hx
      rw [map_add]
      exact Submodule.add_mem_sup (hUst k u hu) (hWst k w hw)
    have hmem : v0 ∈ U ⊔ W := by
      by_contra hn
      refine hUmax (U ⊔ W) ⟨hsup, hn⟩ (lt_of_le_of_ne le_sup_left fun heq => hW0 ?_)
      refine eq_bot_iff.2 ((le_inf (le_sup_right.trans heq.ge) hWS).trans (disjoint_iff.1 hUS.disjoint).le)
    obtain ⟨u, hu, w, hw, hsum⟩ := Submodule.mem_sup.1 hmem
    rw [← hsum, map_add, hpU u hu, zero_add, hpid w (hWS hw)]
    exact hw
  refine ⟨S, p, fun h => hpv0 ?_, hSst, fun S' hS'S hS'st => ?_, hpS, hpid, fun k v => ?_, hpv0⟩
  · have := hpS v0
    rw [h, Submodule.mem_bot] at this
    exact this
  · by_cases h0 : S' = ⊥
    · exact Or.inl h0
    right
    have h1 := key S' hS'S hS'st h0
    obtain ⟨T, hST, hTst⟩ := maschke V hs S' hS'st
    have hST0 : S ⊓ T = ⊥ := by
      by_contra hn
      have h2 := key (S ⊓ T) inf_le_left
        (fun k x hx => Submodule.mem_inf.2 ⟨hSst k x (Submodule.mem_inf.1 hx).1, hTst k x (Submodule.mem_inf.1 hx).2⟩) hn
      have h3 : p v0 ∈ S' ⊓ T := Submodule.mem_inf.2 ⟨h1, (Submodule.mem_inf.1 h2).2⟩
      rw [disjoint_iff.1 hST.disjoint, Submodule.mem_bot] at h3
      exact hpv0 h3
    refine le_antisymm hS'S fun s hs => ?_
    have hs' : s ∈ S' ⊔ T := by rw [hST.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨a, ha, t, ht, hat⟩ := Submodule.mem_sup.1 hs'
    have htS : t ∈ S := by
      have : t = s - a := by rw [← hat]; abel
      rw [this]
      exact S.sub_mem hs (hS'S ha)
    have ht0 : t = 0 := by
      have : t ∈ S ⊓ T := Submodule.mem_inf.2 ⟨htS, ht⟩
      rwa [hST0, Submodule.mem_bot] at this
    rw [← hat, ht0, add_zero]
    exact ha
  · have hv : V k v = V k (p v) + V k (v - p v) := by
      rw [← map_add]
      congr 1
      abel
    rw [hv, map_add, hpid _ (hSst k _ (hpS v)), hpU _ (hUst k _ (hdec v)), add_zero]

end UpperTheory.NonzeroTypeTheory
