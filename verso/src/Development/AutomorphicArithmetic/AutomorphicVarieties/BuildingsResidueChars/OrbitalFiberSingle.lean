import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.FibAbs
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitalFiberOfBot
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceFibreCardinality.GqIndex

open MulAction in
/- English proof (translation)
Introduce `Γ G _ _ ι S U' Γ₁ Γ₀ x Φ hcomm hΓS hN htriv hΦl hΦr hTex hst hrel hcard`. Use `haveI hSn : S.Normal := ⟨fun n hn g => by`. Use `S.mul_mem (hcomm g n) hn using 1` and compare the differences between its conclusion and the goal. Use the proof step `group⟩`. Use `set C := Subgroup.comap ι (S ⊔ U') with hC`.

Use `set f := (orbit ↥S (x : G ⧸ U')).indicator fun y => Φ (Quotient.out y) with hf`. Establish `hΓC : Γ₁ ≤ C` using `fun a ha => Subgroup.mem_comap.mpr ((le_sup_left : S ≤ S ⊔ U') (Subgroup.mem_comap.mp (hΓS ha)))`. Set `j : C →* G` to `ι.comp C.subtype`. Set `φ : Γ₁ →* C` to `Subgroup.inclusion hΓC`. Establish `hclos : ∀ g ∈ S ⊔ U', ∀ y ∈ orbit ↥S (x : G ⧸ U'), g • y ∈ orbit ↥S (x : G ⧸ U')`.

Introduce `g hg y hy`. Take `⟨s, hs, u, hu, rfl⟩` from `Subgroup.mem_sup_of_normal_left.mp hg`. Take `⟨⟨s', hs'⟩, rfl⟩` from `hy`. Use `⟨⟨s * (u * (s' * x) * u⁻¹ * (s' * x)⁻¹) * s', S.mul_mem (S.mul_mem hs (hcomm _ _)) hs'⟩, ?_⟩` and prove the remaining obligations. Use `show ((s * (u * (s' * x) * u⁻¹ * (s' * x)⁻¹) * s' * x : G) : G ⧸ U') = ((s * u * (s' * x) : G) : G ⧸ U')`.

Rewrite using `[QuotientGroup.eq]`. Establish `he : (s * (u * (s' * x) * u⁻¹ * (s' * x)⁻¹) * s' * x)⁻¹ * (s * u * (s' * x)) = u` using `by group`. Rewrite using `[he]`. Conclude with `hu`. Establish `hinv : ∀ (h : C) (y : G ⧸ U'), f (j h • y) = f y`.

Introduce `h y`. Establish `hg : ι h.1 ∈ S ⊔ U'` using `h.2`. Express the relevant statement in the definitionally equal form `f (ι h.1 • y) = f y`. Distinguish the cases in `hy : y ∈ orbit ↥S (x : G ⧸ U')`. Establish `hy'` using `hclos _ hg y hy`.

Rewrite using `[hf, Set.indicator_of_mem hy', Set.indicator_of_mem hy]`. Take `⟨u, hu⟩` from `QuotientGroup.mk_out_eq_mul U' (ι h.1 * Quotient.out y)`. Establish `hyy : ι h.1 • y = ((ι h.1 * Quotient.out y : G) : G ⧸ U')` using `by conv_lhs => rw [← QuotientGroup.out_eq' y]`. Both sides reduce to the same expression. Rewrite using `[hyy, hu, hΦr _ u.2, hΦl]`.

Establish `hy' : ι h.1 • y ∉ orbit ↥S (x : G ⧸ U')` using `fun hm => hy (by`. Use `hclos _ (inv_mem hg) _ hm` as an intermediate fact. Rewrite using `[inv_smul_smul] at this)` and apply the resulting hypothesis. Rewrite using `[hf, Set.indicator_apply, if_neg hy', Set.indicator_apply, if_neg hy]`. Establish `hfin : ∃ T' : Finset (G ⧸ U'), ∀ y, f y ≠ 0 → ∃ h : C, ∃ x' ∈ T', y = j h • x'`.

Take `⟨T, hT⟩` from `hTex`. Use `⟨T.image (QuotientGroup.mk : G → G ⧸ U'), ?_⟩` and prove the remaining obligations. Introduce `y hy`. Take `⟨⟨s, hs⟩, rfl⟩` from `Set.mem_of_indicator_ne_zero hy`. Take `⟨h, hh, t, ht, u, hu, he⟩` from `hT s hs`.

Use `⟨⟨h, hΓC hh⟩, (t : G ⧸ U'), Finset.mem_image_of_mem QuotientGroup.mk ht, ?_⟩` and prove the remaining obligations. Use `show ((s * x : G) : G ⧸ U') = ((ι h * t : G) : G ⧸ U')`. Rewrite using `[he, QuotientGroup.eq]`. Rewrite using `[show (ι h * t * u)⁻¹ * (ι h * t) = u⁻¹ by group]`. Conclude with `inv_mem hu`.

Establish `hsup : φ.range ⊔ Γ₀.subgroupOf C = (Γ₁ ⊔ Γ₀).subgroupOf C`. Use extensionality with `z`. Rewrite using `[Subgroup.mem_sup_of_normal_right, Subgroup.mem_subgroupOf, Subgroup.mem_sup_of_normal_right]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ⟨a', rfl⟩, b, hb, rfl⟩`.

Conclude with `⟨a'.1, a'.2, b.1, Subgroup.mem_subgroupOf.mp hb, rfl⟩`. Introduce and unpack `⟨a, ha, b, hb, hab⟩`. Establish `hbC : b ∈ C`. Establish `hb' : b = a⁻¹ * (z : Γ)` using `by rw [← hab]; group`. Rewrite using `[hb']`.

Conclude with `C.mul_mem (C.inv_mem (hΓC ha)) z.2`. Conclude with `⟨φ ⟨a, ha⟩, ⟨⟨a, ha⟩, rfl⟩, ⟨b, hbC⟩, Subgroup.mem_subgroupOf.mpr hb, Subtype.ext hab⟩`. Establish `hidx : (φ.range ⊔ Γ₀.subgroupOf C).index = (Γ₁ ⊔ Γ₀).relIndex C`. Rewrite using `[hsup]`. Both sides reduce to the same expression.

Establish `key` using `UpperTheory.V.Z.Sym.Tf.gqIndex Γ₁ C G φ j (Γ₀.subgroupOf C) U' f inferInstance (fun z hz y => htriv z.1 (Subgroup.mem_subgroupOf.mp hz) y) (by rw [hidx]; exact hrel) hinv hfin (fun y _ => by`. Rewrite using `[← Subgroup.comap_comap]`. Conclude with `Subgroup.relIndex_comap_ne_zero _ (hst y))`. Establish `e1 : UpperTheory.V.Z.Sym.gqOn (ι.comp Γ₁.subtype) (Γ₀.subgroupOf Γ₁) U' f = UpperTheory.V.Z.Sym.gqOn (j.comp φ) (Subgroup.comap φ (Γ₀.subgroupOf C)) U' f` using `rfl`. Establish `hb : UpperTheory.V.Z.Sym.gqOn (ι.comp Γ₁.subtype) (Γ₀.subgroupOf Γ₁) U' f = ↑(Nat.card ↥(Γ₀.subgroupOf Γ₁)) * UpperTheory.V.Z.Sym.gqOn (ι.comp Γ₁.subtype) ⊥ U' f`.

Use `letI := MulAction.compHom (G ⧸ U') (ι.comp Γ₁.subtype)`. Conclude with `(UpperTheory.orbitalFiber_of_bot Γ₁ (G ⧸ U') (Γ₀.subgroupOf Γ₁) f).2 hcard (fun z hz y => htriv z.1 (Subgroup.mem_subgroupOf.mp hz) y)`. Rewrite using `[← hb, e1, key, hidx]`.
-/
theorem UpperTheory.orbitalFiber_single :
    UpperTheory.V.Z.Sym.Glob.Fib.OneFib := by
  intro Γ G _ _ ι S U' Γ₁ Γ₀ x Φ hcomm hΓS hN htriv hΦl hΦr hTex hst hrel hcard
  classical
  haveI hSn : S.Normal := ⟨fun n hn g => by
    convert S.mul_mem (hcomm g n) hn using 1
    group⟩
  set C := Subgroup.comap ι (S ⊔ U') with hC
  set f := (orbit ↥S (x : G ⧸ U')).indicator fun y => Φ (Quotient.out y) with hf
  have hΓC : Γ₁ ≤ C := fun a ha =>
    Subgroup.mem_comap.mpr ((le_sup_left : S ≤ S ⊔ U') (Subgroup.mem_comap.mp (hΓS ha)))
  let j : C →* G := ι.comp C.subtype
  let φ : Γ₁ →* C := Subgroup.inclusion hΓC
  have hclos : ∀ g ∈ S ⊔ U', ∀ y ∈ orbit ↥S (x : G ⧸ U'), g • y ∈ orbit ↥S (x : G ⧸ U') := by
    intro g hg y hy
    obtain ⟨s, hs, u, hu, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hg
    obtain ⟨⟨s', hs'⟩, rfl⟩ := hy
    refine ⟨⟨s * (u * (s' * x) * u⁻¹ * (s' * x)⁻¹) * s', S.mul_mem (S.mul_mem hs (hcomm _ _)) hs'⟩, ?_⟩
    show ((s * (u * (s' * x) * u⁻¹ * (s' * x)⁻¹) * s' * x : G) : G ⧸ U') = ((s * u * (s' * x) : G) : G ⧸ U')
    rw [QuotientGroup.eq]
    have he : (s * (u * (s' * x) * u⁻¹ * (s' * x)⁻¹) * s' * x)⁻¹ * (s * u * (s' * x)) = u := by group
    rw [he]
    exact hu
  have hinv : ∀ (h : C) (y : G ⧸ U'), f (j h • y) = f y := by
    intro h y
    have hg : ι h.1 ∈ S ⊔ U' := h.2
    change f (ι h.1 • y) = f y
    by_cases hy : y ∈ orbit ↥S (x : G ⧸ U')
    · have hy' := hclos _ hg y hy
      rw [hf, Set.indicator_of_mem hy', Set.indicator_of_mem hy]
      obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul U' (ι h.1 * Quotient.out y)
      have hyy : ι h.1 • y = ((ι h.1 * Quotient.out y : G) : G ⧸ U') := by
        conv_lhs => rw [← QuotientGroup.out_eq' y]
        rfl
      rw [hyy, hu, hΦr _ u.2, hΦl]
    · have hy' : ι h.1 • y ∉ orbit ↥S (x : G ⧸ U') := fun hm => hy (by
        have := hclos _ (inv_mem hg) _ hm
        rwa [inv_smul_smul] at this)
      rw [hf, Set.indicator_apply, if_neg hy', Set.indicator_apply, if_neg hy]
  have hfin : ∃ T' : Finset (G ⧸ U'), ∀ y, f y ≠ 0 → ∃ h : C, ∃ x' ∈ T', y = j h • x' := by
    obtain ⟨T, hT⟩ := hTex
    refine ⟨T.image (QuotientGroup.mk : G → G ⧸ U'), ?_⟩
    intro y hy
    obtain ⟨⟨s, hs⟩, rfl⟩ := Set.mem_of_indicator_ne_zero hy
    obtain ⟨h, hh, t, ht, u, hu, he⟩ := hT s hs
    refine ⟨⟨h, hΓC hh⟩, (t : G ⧸ U'), Finset.mem_image_of_mem QuotientGroup.mk ht, ?_⟩
    show ((s * x : G) : G ⧸ U') = ((ι h * t : G) : G ⧸ U')
    rw [he, QuotientGroup.eq]
    rw [show (ι h * t * u)⁻¹ * (ι h * t) = u⁻¹ by group]
    exact inv_mem hu
  have hsup : φ.range ⊔ Γ₀.subgroupOf C = (Γ₁ ⊔ Γ₀).subgroupOf C := by
    ext z
    rw [Subgroup.mem_sup_of_normal_right, Subgroup.mem_subgroupOf, Subgroup.mem_sup_of_normal_right]
    constructor
    · rintro ⟨a, ⟨a', rfl⟩, b, hb, rfl⟩
      exact ⟨a'.1, a'.2, b.1, Subgroup.mem_subgroupOf.mp hb, rfl⟩
    · rintro ⟨a, ha, b, hb, hab⟩
      have hbC : b ∈ C := by
        have hb' : b = a⁻¹ * (z : Γ) := by rw [← hab]; group
        rw [hb']
        exact C.mul_mem (C.inv_mem (hΓC ha)) z.2
      exact ⟨φ ⟨a, ha⟩, ⟨⟨a, ha⟩, rfl⟩, ⟨b, hbC⟩, Subgroup.mem_subgroupOf.mpr hb, Subtype.ext hab⟩
  have hidx : (φ.range ⊔ Γ₀.subgroupOf C).index = (Γ₁ ⊔ Γ₀).relIndex C := by
    rw [hsup]
    rfl
  have key := UpperTheory.V.Z.Sym.Tf.gqIndex Γ₁ C G φ j (Γ₀.subgroupOf C) U' f
    inferInstance (fun z hz y => htriv z.1 (Subgroup.mem_subgroupOf.mp hz) y)
    (by rw [hidx]; exact hrel) hinv hfin
    (fun y _ => by
      rw [← Subgroup.comap_comap]
      exact Subgroup.relIndex_comap_ne_zero _ (hst y))
  have e1 : UpperTheory.V.Z.Sym.gqOn (ι.comp Γ₁.subtype) (Γ₀.subgroupOf Γ₁) U' f =
      UpperTheory.V.Z.Sym.gqOn (j.comp φ) (Subgroup.comap φ (Γ₀.subgroupOf C)) U' f := rfl
  have hb : UpperTheory.V.Z.Sym.gqOn (ι.comp Γ₁.subtype) (Γ₀.subgroupOf Γ₁) U' f =
      ↑(Nat.card ↥(Γ₀.subgroupOf Γ₁)) * UpperTheory.V.Z.Sym.gqOn (ι.comp Γ₁.subtype) ⊥ U' f := by
    letI := MulAction.compHom (G ⧸ U') (ι.comp Γ₁.subtype)
    exact (UpperTheory.orbitalFiber_of_bot Γ₁ (G ⧸ U') (Γ₀.subgroupOf Γ₁) f).2 hcard
      (fun z hz y => htriv z.1 (Subgroup.mem_subgroupOf.mp hz) y)
  rw [← hb, e1, key, hidx]
