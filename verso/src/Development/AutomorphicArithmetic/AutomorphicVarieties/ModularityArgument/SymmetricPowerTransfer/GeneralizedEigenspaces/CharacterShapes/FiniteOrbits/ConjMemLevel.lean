import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.FinOrbSub
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.DcBasic

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL Formalism.BasicNotions UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Introduce `Γ G V _ _ _ _ ι W S U hSn hcomm hΓ ψ hψΓ hψU`. Establish `wd : ∀ (γ γ' : Γ) (s s' : S) (u u' : G), u ∈ U → u' ∈ U → ι γ * s * u = ι γ' * s' * u' → W γ (ψ s) = W γ' (ψ s')`. Introduce `γ γ' s s' u u' hu hu' h`. Establish `hv : u * u'⁻¹ ∈ U` using `U.mul_mem hu (U.inv_mem hu')`. Establish `h1 : ι (γ'⁻¹ * γ) * s * (u * u'⁻¹) = s'`.

Rewrite using `[map_mul, map_inv]`. Rewrite using `[show (ι γ')⁻¹ * ι γ * ↑s * (u * u'⁻¹) = (ι γ')⁻¹ * (ι γ * ↑s * u) * u'⁻¹ by group, h]`. Use `group`. Establish `hδ : ι (γ'⁻¹ * γ) ∈ S`. Apply `hΓ (γ'⁻¹ * γ) (u * u'⁻¹) hv` to reduce the goal to its premises.

Establish `e : ι (γ'⁻¹ * γ) * (u * u'⁻¹) = ↑s' * ((u * u'⁻¹)⁻¹ * (↑s)⁻¹ * (u * u'⁻¹))`. Rewrite using `[← h1]`. Use `group`. Rewrite using `[e]`. Apply `S.mul_mem s'.2` to reduce the goal to its premises.

Establish `hc` using `hSn.conj_mem _ (S.inv_mem s.2) (u * u'⁻¹)⁻¹`. Rewrite `hc` using `[inv_inv]`. Conclude with `hc`. Establish `hvS : u * u'⁻¹ ∈ S`. Establish `e : u * u'⁻¹ = (ι (γ'⁻¹ * γ) * ↑s)⁻¹ * ↑s'`.

Rewrite using `[← h1]`. Use `group`. Rewrite using `[e]`. Conclude with `S.mul_mem (S.inv_mem (S.mul_mem hδ s.2)) s'.2`. Establish `e1 : s' = ⟨ι (γ'⁻¹ * γ) * s, S.mul_mem hδ s.2⟩ * ⟨u * u'⁻¹, hvS⟩`.

Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [Subgroup.coe_mul, Subgroup.coe_mk]`. Conclude with `h1.symm`. Rewrite using `[e1, hψU ⟨u * u'⁻¹, hvS⟩ hv, hψΓ (γ'⁻¹ * γ) s ⟨ι (γ'⁻¹ * γ) * s, S.mul_mem hδ s.2⟩ rfl, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]`. Take `⟨P, hP⟩ : ∃ P : G → Prop, ∀ g, P g ↔ ∃ γ : Γ, ∃ s : S, ∃ u ∈ U, g = ι γ * s * u` from `⟨_, fun _ => Iff.rfl⟩`.

Take `⟨Φ, hΦ⟩ : ∃ Φ : G → V, ∀ g, Φ g = if h : P g then W ((hP g).1 h).choose (ψ ((hP g).1 h).choose_spec.choose) else 0` from `⟨_, fun _ => rfl⟩`. Establish `Φ_spec : ∀ (γ : Γ) (s : S) (u : G), u ∈ U → Φ (ι γ * s * u) = W γ (ψ s)`. Introduce `γ s u hu`. Establish `h : P (ι γ * s * u)` using `(hP _).2 ⟨γ, s, u, hu, rfl⟩`. Rewrite using `[hΦ, dif_pos h]`.

Take `⟨u0, hu0, e⟩` from `((hP _).1 h).choose_spec.choose_spec`. Conclude with `wd _ _ _ _ _ _ hu0 hu e.symm`. Establish `Φ_neg : ∀ g, ¬ P g → Φ g = 0` using `fun g h => by rw [hΦ, dif_neg h]`. Establish `hUinv : ∀ u ∈ U, ∀ g : G, Φ (g * u) = Φ g`. Introduce `u hu g`.

Distinguish the cases in `hg : P g`. Take `⟨γ, s, u0, hu0, rfl⟩` from `(hP g).1 hg`. Rewrite using `[show ι γ * ↑s * u0 * u = ι γ * ↑s * (u0 * u) by group, Φ_spec _ _ _ (U.mul_mem hu0 hu), Φ_spec _ _ _ hu0]`. Rewrite using `[Φ_neg _ hg, Φ_neg]`. Introduce `h'`.

Apply `hg` to reduce the goal to its premises. Take `⟨γ, s, u1, hu1, e⟩` from `(hP _).1 h'`. Use `(hP g).2 ⟨γ, s, u1 * u⁻¹, U.mul_mem hu1 (U.inv_mem hu), ?_⟩` and prove the remaining obligations. Rewrite using `[← mul_assoc, ← e]`. Use `group`.

Use `⟨Φ, ?_, ?_, hUinv, ?_⟩` and prove the remaining obligations. Introduce `g`. Establish `h` using `Φ_spec 1 g 1 U.one_mem`. Simplify using `using h`. Introduce `γ g`.

Distinguish the cases in `hg : P g`. Take `⟨δ, s, u, hu, rfl⟩` from `(hP g).1 hg`. Rewrite using `[show ι γ * (ι δ * ↑s * u) = ι (γ * δ) * ↑s * u by rw [map_mul]; group, Φ_spec _ _ _ hu, Φ_spec _ _ _ hu, map_mul, Module.End.mul_apply]`. Rewrite using `[Φ_neg _ hg, map_zero, Φ_neg]`. Introduce `h'`.

Apply `hg` to reduce the goal to its premises. Take `⟨δ, s, u, hu, e⟩` from `(hP _).1 h'`. Use `(hP g).2 ⟨γ⁻¹ * δ, s, u, hu, ?_⟩` and prove the remaining obligations. Establish `e2 : g = (ι γ)⁻¹ * (ι γ * g)` using `by group`. Rewrite using `[e2, e, map_mul, map_inv]`.

Use `group`. Introduce `a c hfin hz heig`. Take `⟨hfinS, hmem, -, R, hR1, hR2, hR3⟩` from `dcSub G V S U a hfin hz hSn`. Establish `hψU' : ∀ u ∈ U.subgroupOf S, ∀ g : S, ψ (g * u) = ψ g` using `fun u hu g => hψU u (Subgroup.mem_subgroupOf.1 hu) g`. Establish `hval : ∀ x ∈ U, ∀ g : G, dcF U (↑a) Φ g = ∑ r ∈ R, Φ (g * (x⁻¹ * ↑r * x))`.

Introduce `x hx g`. Set `e : S ↪ G` to `⟨fun r => x⁻¹ * ↑r * x, fun r1 r2 h => Subtype.ext (by simpa using h)⟩`. Establish `h1 : ∀ y ∈ R.map e, y ∈ DC U (↑a)`. Introduce `y hy`. Take `⟨r, hr, rfl⟩` from `Finset.mem_map.1 hy`.

Take `⟨v, hv, w, hw, h⟩` from `(hmem r).1 (hR1 r hr)`. Use `⟨x⁻¹ * v, U.mul_mem (U.inv_mem hx) hv, w * x, U.mul_mem hw hx, ?_⟩` and prove the remaining obligations. Use `show x⁻¹ * ↑r * x = _`. Rewrite using `[h]`. Use `group`.

Establish `h2 : ∀ y ∈ DC U (↑a), ∃! r, r ∈ R.map e ∧ r⁻¹ * y ∈ U`. Introduce `y hy`. Establish `hxy : x * y ∈ DC U (↑a)`. Take `⟨v, hv, w, hw, rfl⟩` from `hy`. Conclude with `⟨x * v, U.mul_mem hx hv, w, hw, by group⟩`.

Take `⟨r, ⟨hr, hry⟩, huniq⟩` from `hR3 _ hxy`. Use `⟨x⁻¹ * ↑r * x, ⟨Finset.mem_map_of_mem e hr, ?_⟩, ?_⟩` and prove the remaining obligations. Establish `e3 : (x⁻¹ * ↑r * x)⁻¹ * y = x⁻¹ * ((↑r)⁻¹ * (x * y))` using `by group`. Rewrite using `[e3]`. Conclude with `U.mul_mem (U.inv_mem hx) hry`.

Introduce and unpack `y' ⟨hy', hy'y⟩`. Take `⟨r1, hr1, rfl⟩` from `Finset.mem_map.1 hy'`. Establish `hr1y : (↑r1 : G)⁻¹ * (x * y) ∈ U`. Establish `e4 : (↑r1 : G)⁻¹ * (x * y) = x * ((x⁻¹ * ↑r1 * x)⁻¹ * y)` using `by group`. Rewrite using `[e4]`.

Conclude with `U.mul_mem hx hy'y`. Rewrite using `[huniq r1 ⟨hr1, hr1y⟩]`. Both sides reduce to the same expression. Rewrite using `[(dcBasic G V U a hfin Φ hUinv).2.2.2.2 (R.map e) h1 h2 g, Finset.sum_map]`. Both sides reduce to the same expression.

Use function extensionality and compare the values at `g`. Rewrite using `[Pi.smul_apply]`. Distinguish the cases in `hg : P g`. Take `⟨γ, s, u, hu, rfl⟩` from `(hP g).1 hg`. Rewrite using `[hval u hu, Φ_spec γ s u hu]`.

Establish `e5 : ∀ r : S, Φ (ι γ * ↑s * u * (u⁻¹ * ↑r * u)) = W γ (ψ (s * r))`. Introduce `r`. Rewrite using `[show ι γ * ↑s * u * (u⁻¹ * ↑r * u) = ι γ * ↑(s * r) * u by`. Simplify using `only [Subgroup.coe_mul]`. Use the proof step `group, Φ_spec _ _ _ hu]`.

Rewrite using `[Finset.sum_congr rfl (fun r _ => e5 r), ← map_sum (W γ), ← (dcBasic S V (U.subgroupOf S) a hfinS ψ hψU').2.2.2.2 R hR1 hR2 s, heig, Pi.smul_apply, map_smul]`. Rewrite using `[hval 1 U.one_mem, Φ_neg _ hg, smul_zero]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `r _`. Apply `Φ_neg` to reduce the goal to its premises.

Introduce `h'`. Apply `hg` to reduce the goal to its premises. Take `⟨γ, s, u, hu, e⟩` from `(hP _).1 h'`. Use `(hP g).2 ⟨γ, s * ⟨u * (↑r)⁻¹ * u⁻¹, hSn.conj_mem _ (S.inv_mem r.2) u⟩, u, hu, ?_⟩` and prove the remaining obligations. Establish `e6 : g = g * (1⁻¹ * ↑r * 1) * (↑r)⁻¹` using `by group`.

Rewrite using `[e6, e]`. Simplify using `only [Subgroup.coe_mul, Subgroup.coe_mk]`. Use `group`.
-/
theorem UpperTheory.V.Z.Sym.So.extF :
    UpperTheory.V.Z.Sym.So.ExtF := by
  intro Γ G V _ _ _ _ ι W S U hSn hcomm hΓ ψ hψΓ hψU
  classical
  have wd : ∀ (γ γ' : Γ) (s s' : S) (u u' : G), u ∈ U → u' ∈ U →
      ι γ * s * u = ι γ' * s' * u' → W γ (ψ s) = W γ' (ψ s') := by
    intro γ γ' s s' u u' hu hu' h
    have hv : u * u'⁻¹ ∈ U := U.mul_mem hu (U.inv_mem hu')
    have h1 : ι (γ'⁻¹ * γ) * s * (u * u'⁻¹) = s' := by
      rw [map_mul, map_inv]
      rw [show (ι γ')⁻¹ * ι γ * ↑s * (u * u'⁻¹) = (ι γ')⁻¹ * (ι γ * ↑s * u) * u'⁻¹ by group, h]
      group
    have hδ : ι (γ'⁻¹ * γ) ∈ S := by
      apply hΓ (γ'⁻¹ * γ) (u * u'⁻¹) hv
      have e : ι (γ'⁻¹ * γ) * (u * u'⁻¹) =
          ↑s' * ((u * u'⁻¹)⁻¹ * (↑s)⁻¹ * (u * u'⁻¹)) := by
        rw [← h1]
        group
      rw [e]
      apply S.mul_mem s'.2
      have hc := hSn.conj_mem _ (S.inv_mem s.2) (u * u'⁻¹)⁻¹
      rw [inv_inv] at hc
      exact hc
    have hvS : u * u'⁻¹ ∈ S := by
      have e : u * u'⁻¹ = (ι (γ'⁻¹ * γ) * ↑s)⁻¹ * ↑s' := by
        rw [← h1]
        group
      rw [e]
      exact S.mul_mem (S.inv_mem (S.mul_mem hδ s.2)) s'.2
    have e1 : s' = ⟨ι (γ'⁻¹ * γ) * s, S.mul_mem hδ s.2⟩ * ⟨u * u'⁻¹, hvS⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_mk]
      exact h1.symm
    rw [e1, hψU ⟨u * u'⁻¹, hvS⟩ hv,
      hψΓ (γ'⁻¹ * γ) s ⟨ι (γ'⁻¹ * γ) * s, S.mul_mem hδ s.2⟩ rfl, ← Module.End.mul_apply, ← map_mul,
      mul_inv_cancel_left]
  obtain ⟨P, hP⟩ : ∃ P : G → Prop, ∀ g, P g ↔ ∃ γ : Γ, ∃ s : S, ∃ u ∈ U, g = ι γ * s * u :=
    ⟨_, fun _ => Iff.rfl⟩
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : G → V, ∀ g, Φ g = if h : P g then
      W ((hP g).1 h).choose (ψ ((hP g).1 h).choose_spec.choose) else 0 := ⟨_, fun _ => rfl⟩
  have Φ_spec : ∀ (γ : Γ) (s : S) (u : G), u ∈ U → Φ (ι γ * s * u) = W γ (ψ s) := by
    intro γ s u hu
    have h : P (ι γ * s * u) := (hP _).2 ⟨γ, s, u, hu, rfl⟩
    rw [hΦ, dif_pos h]
    obtain ⟨u0, hu0, e⟩ := ((hP _).1 h).choose_spec.choose_spec
    exact wd _ _ _ _ _ _ hu0 hu e.symm
  have Φ_neg : ∀ g, ¬ P g → Φ g = 0 := fun g h => by rw [hΦ, dif_neg h]
  have hUinv : ∀ u ∈ U, ∀ g : G, Φ (g * u) = Φ g := by
    intro u hu g
    by_cases hg : P g
    · obtain ⟨γ, s, u0, hu0, rfl⟩ := (hP g).1 hg
      rw [show ι γ * ↑s * u0 * u = ι γ * ↑s * (u0 * u) by group, Φ_spec _ _ _ (U.mul_mem hu0 hu),
        Φ_spec _ _ _ hu0]
    · rw [Φ_neg _ hg, Φ_neg]
      intro h'
      apply hg
      obtain ⟨γ, s, u1, hu1, e⟩ := (hP _).1 h'
      refine (hP g).2 ⟨γ, s, u1 * u⁻¹, U.mul_mem hu1 (U.inv_mem hu), ?_⟩
      rw [← mul_assoc, ← e]
      group
  refine ⟨Φ, ?_, ?_, hUinv, ?_⟩
  · intro g
    have h := Φ_spec 1 g 1 U.one_mem
    simpa using h
  · intro γ g
    by_cases hg : P g
    · obtain ⟨δ, s, u, hu, rfl⟩ := (hP g).1 hg
      rw [show ι γ * (ι δ * ↑s * u) = ι (γ * δ) * ↑s * u by rw [map_mul]; group,
        Φ_spec _ _ _ hu, Φ_spec _ _ _ hu, map_mul, Module.End.mul_apply]
    · rw [Φ_neg _ hg, map_zero, Φ_neg]
      intro h'
      apply hg
      obtain ⟨δ, s, u, hu, e⟩ := (hP _).1 h'
      refine (hP g).2 ⟨γ⁻¹ * δ, s, u, hu, ?_⟩
      have e2 : g = (ι γ)⁻¹ * (ι γ * g) := by group
      rw [e2, e, map_mul, map_inv]
      group
  · intro a c hfin hz heig
    obtain ⟨hfinS, hmem, -, R, hR1, hR2, hR3⟩ := dcSub G V S U a hfin hz hSn
    have hψU' : ∀ u ∈ U.subgroupOf S, ∀ g : S, ψ (g * u) = ψ g :=
      fun u hu g => hψU u (Subgroup.mem_subgroupOf.1 hu) g
    have hval : ∀ x ∈ U, ∀ g : G, dcF U (↑a) Φ g = ∑ r ∈ R, Φ (g * (x⁻¹ * ↑r * x)) := by
      intro x hx g
      let e : S ↪ G := ⟨fun r => x⁻¹ * ↑r * x, fun r1 r2 h => Subtype.ext (by simpa using h)⟩
      have h1 : ∀ y ∈ R.map e, y ∈ DC U (↑a) := by
        intro y hy
        obtain ⟨r, hr, rfl⟩ := Finset.mem_map.1 hy
        obtain ⟨v, hv, w, hw, h⟩ := (hmem r).1 (hR1 r hr)
        refine ⟨x⁻¹ * v, U.mul_mem (U.inv_mem hx) hv, w * x, U.mul_mem hw hx, ?_⟩
        show x⁻¹ * ↑r * x = _
        rw [h]
        group
      have h2 : ∀ y ∈ DC U (↑a), ∃! r, r ∈ R.map e ∧ r⁻¹ * y ∈ U := by
        intro y hy
        have hxy : x * y ∈ DC U (↑a) := by
          obtain ⟨v, hv, w, hw, rfl⟩ := hy
          exact ⟨x * v, U.mul_mem hx hv, w, hw, by group⟩
        obtain ⟨r, ⟨hr, hry⟩, huniq⟩ := hR3 _ hxy
        refine ⟨x⁻¹ * ↑r * x, ⟨Finset.mem_map_of_mem e hr, ?_⟩, ?_⟩
        · have e3 : (x⁻¹ * ↑r * x)⁻¹ * y = x⁻¹ * ((↑r)⁻¹ * (x * y)) := by group
          rw [e3]
          exact U.mul_mem (U.inv_mem hx) hry
        · rintro y' ⟨hy', hy'y⟩
          obtain ⟨r1, hr1, rfl⟩ := Finset.mem_map.1 hy'
          have hr1y : (↑r1 : G)⁻¹ * (x * y) ∈ U := by
            have e4 : (↑r1 : G)⁻¹ * (x * y) = x * ((x⁻¹ * ↑r1 * x)⁻¹ * y) := by group
            rw [e4]
            exact U.mul_mem hx hy'y
          rw [huniq r1 ⟨hr1, hr1y⟩]
          rfl
      rw [(dcBasic G V U a hfin Φ hUinv).2.2.2.2 (R.map e) h1 h2 g, Finset.sum_map]
      rfl
    funext g
    rw [Pi.smul_apply]
    by_cases hg : P g
    · obtain ⟨γ, s, u, hu, rfl⟩ := (hP g).1 hg
      rw [hval u hu, Φ_spec γ s u hu]
      have e5 : ∀ r : S, Φ (ι γ * ↑s * u * (u⁻¹ * ↑r * u)) = W γ (ψ (s * r)) := by
        intro r
        rw [show ι γ * ↑s * u * (u⁻¹ * ↑r * u) = ι γ * ↑(s * r) * u by
          simp only [Subgroup.coe_mul]; group, Φ_spec _ _ _ hu]
      rw [Finset.sum_congr rfl (fun r _ => e5 r), ← map_sum (W γ),
        ← (dcBasic S V (U.subgroupOf S) a hfinS ψ hψU').2.2.2.2 R hR1 hR2 s, heig, Pi.smul_apply,
        map_smul]
    · rw [hval 1 U.one_mem, Φ_neg _ hg, smul_zero]
      apply Finset.sum_eq_zero
      intro r _
      apply Φ_neg
      intro h'
      apply hg
      obtain ⟨γ, s, u, hu, e⟩ := (hP _).1 h'
      refine (hP g).2 ⟨γ, s * ⟨u * (↑r)⁻¹ * u⁻¹, hSn.conj_mem _ (S.inv_mem r.2) u⟩, u, hu, ?_⟩
      have e6 : g = g * (1⁻¹ * ↑r * 1) * (↑r)⁻¹ := by group
      rw [e6, e]
      simp only [Subgroup.coe_mul, Subgroup.coe_mk]
      group

end
