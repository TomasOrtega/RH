import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FrobeniusSplitPrimeDatum

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V
open scoped Pointwise

namespace UpperTheory.V.Fr.DescentValuationAlt

/- English proof (translation)
Establish `fix : ∀ y : Ω, g y = y → (y ∈ g • A ↔ y ∈ A)`. Introduce `y hy`. Establish `hy' : g • y = y` using `hy`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Take `⟨s, hs, hgs⟩` from `(ValuationSubring.mem_smul_pointwise_iff_exists g y A).mp h`. Establish `: s = y`. Rewrite using `[← inv_smul_smul g s, hgs, inv_smul_eq_iff, hy']`. Rewrite `hs` using `[this]`. Then use the resulting hypothesis. Introduce `h`.

Use `ValuationSubring.smul_mem_pointwise_smul g y A h` as an intermediate fact. Rewrite `this` using `[hy']`. Then use the resulting hypothesis. Establish `vlt : ∀ (C : ValuationSubring Ω) (x : Ω), x ≠ 0 → (C.valuation x < 1 ↔ x ∈ C ∧ x⁻¹ ∉ C)`. Introduce `C x hx`. Use `haveI : Nontrivial C.ValueGroup := GroupWithZero.toNontrivial`.

Rewrite using `[← ValuationSubring.valuation_le_one_iff, ← ValuationSubring.valuation_le_one_iff, map_inv₀, inv_le_one₀ ((Valuation.pos_iff _).mpr hx), lt_iff_le_not_ge]`. Distinguish the cases in `h0 : (n : Ω) = 0`. Rewrite using `[h0, map_zero] haveI : Nontrivial (g • A).ValueGroup := GroupWithZero.toNontrivial`. Conclude with `zero_lt_one`. Establish `hn : g (n : Ω) = n` using `map_natCast g n`.

Establish `hni : g ((n : Ω)⁻¹) = (n : Ω)⁻¹` using `by rw [map_inv₀, hn]`. Rewrite `hA`, the goal using `[vlt _ _ h0]`. Rewrite using `[fix _ hn, fix _ hni]`. Conclude with `hA`.
-/
private theorem smul_val_lt {Ω : Type} [Field Ω] [Algebra ℚ Ω] (g : G ℚ Ω) (A : ValuationSubring Ω) (n : ℕ)
    (hA : A.valuation (n : Ω) < 1) : (g • A).valuation (n : Ω) < 1 := by
  have fix : ∀ y : Ω, g y = y → (y ∈ g • A ↔ y ∈ A) := by
    intro y hy
    have hy' : g • y = y := hy
    constructor
    · intro h
      obtain ⟨s, hs, hgs⟩ := (ValuationSubring.mem_smul_pointwise_iff_exists g y A).mp h
      have : s = y := by
        rw [← inv_smul_smul g s, hgs, inv_smul_eq_iff, hy']
      rwa [this] at hs
    · intro h
      have := ValuationSubring.smul_mem_pointwise_smul g y A h
      rwa [hy'] at this
  have vlt : ∀ (C : ValuationSubring Ω) (x : Ω), x ≠ 0 → (C.valuation x < 1 ↔ x ∈ C ∧ x⁻¹ ∉ C) := by
    intro C x hx
    haveI : Nontrivial C.ValueGroup := GroupWithZero.toNontrivial
    rw [← ValuationSubring.valuation_le_one_iff, ← ValuationSubring.valuation_le_one_iff, map_inv₀,
      inv_le_one₀ ((Valuation.pos_iff _).mpr hx), lt_iff_le_not_ge]
  by_cases h0 : (n : Ω) = 0
  · rw [h0, map_zero]
    haveI : Nontrivial (g • A).ValueGroup := GroupWithZero.toNontrivial
    exact zero_lt_one
  · have hn : g (n : Ω) = n := map_natCast g n
    have hni : g ((n : Ω)⁻¹) = (n : Ω)⁻¹ := by rw [map_inv₀, hn]
    rw [vlt _ _ h0] at hA ⊢
    rw [fix _ hn, fix _ hni]
    exact hA

/- English proof (translation)
Establish `hy1 : y 1 = 0`. Establish `e` using `hy 1 1`. Rewrite `e` using `[mul_one, map_one, map_one, Units.val_one, one_mul]`. Take the linear combination `-e`. Set `H : Subgroup U` to `{ carrier := {t | p t = 1 ∧ y t = 0} one_mem' := ⟨map_one p, hy1⟩ mul_mem' := by`.

Introduce and unpack `a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩`. Use `show p (a * b) = 1 ∧ y (a * b) = 0`. Use `⟨by rw [map_mul, ha1, hb1, one_mul], ?_⟩` and prove the remaining obligations. Rewrite using `[hy, ha2, hb2, mul_zero, add_zero]`. Use the proof step `inv_mem' := by`.

Introduce and unpack `a ⟨ha1, ha2⟩`. Use `show p a⁻¹ = 1 ∧ y a⁻¹ = 0`. Use `⟨by rw [map_inv, ha1, inv_one], ?_⟩` and prove the remaining obligations. Establish `e` using `hy a a⁻¹`. Rewrite `e` using `[mul_inv_cancel, hy1, ha2, ha1, map_one, Units.val_one, one_mul, zero_add]`.

Conclude with `e.symm }`. Establish `hH : H.Normal` using `⟨fun t ht g => by`. Take `⟨ht1, ht2⟩` from `ht`. Use `show p (g * t * g⁻¹) = 1 ∧ y (g * t * g⁻¹) = 0`. Use `⟨by rw [map_mul, map_mul, map_inv, ht1, mul_one, mul_inv_cancel], ?_⟩` and prove the remaining obligations.

Establish `e1` using `hy (g * t) g⁻¹`. Establish `e2` using `hy g t`. Establish `e3` using `hy g g⁻¹`. Rewrite `e3` using `[mul_inv_cancel, hy1]`. Rewrite `e1` using `[map_mul, ht1, mul_one]`.

Rewrite `e2` using `[ht2, mul_zero, add_zero]`. Rewrite using `[e1, e2, ← e3]⟩`. Establish `hcl : IsClosed (H : Set U)` using `(isClosed_eq hc continuous_const).inter (hl.isClosed_fiber 0)`. Establish `hKH : p.ker ≤ H`. Rewrite using `[hk]`.

Apply `Subgroup.topologicalClosure_minimal _ _ hcl` to reduce the goal to its premises. Use `haveI := hH`. Apply `Subgroup.normalClosure_le_normal` to reduce the goal to its premises. Introduce `s hsS`. Establish `hps : p s = 1`.

Rewrite using `[← MonoidHom.mem_ker, hk]`. Conclude with `Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure hsS)`. Conclude with `⟨hps, hS s hsS⟩`. Establish `hfib : ∀ s t, p s = p t → y s = y t`. Introduce `s t hst`.

Establish `hk' : s⁻¹ * t ∈ p.ker` using `by rw [MonoidHom.mem_ker, map_mul, map_inv, hst, inv_mul_cancel]`. Take `⟨_, h2⟩` from `hKH hk'`. Establish `e` using `hy s (s⁻¹ * t)`. Rewrite `e` using `[mul_inv_cancel_left, h2, mul_zero, add_zero]`. Conclude with `e.symm`.

Establish `hq : Topology.IsQuotientMap p` using `(hc.isClosedMap).isQuotientMap hc hs`. Use `⟨fun γ => y (Function.surjInv hs γ), fun V => ?_, fun s => hfib _ _ (Function.surjInv_eq hs (p s))⟩` and prove the remaining obligations. Establish `e : p ⁻¹' ((fun γ => y (Function.surjInv hs γ)) ⁻¹' V) = y ⁻¹' V`. Use extensionality with `s`. Simplify using `only [Set.mem_preimage]`.

Rewrite using `[hfib _ _ (Function.surjInv_eq hs (p s))]`. Apply `hq.isOpen_preimage.mp` to reduce the goal to its premises. Rewrite using `[e]`. Conclude with `hl V`.
-/
private theorem descend {U Γ k : Type} [Group U] [TopologicalSpace U] [IsTopologicalGroup U] [CompactSpace U]
    [Group Γ] [TopologicalSpace Γ] [T2Space Γ] [CommRing k] (p : U →* Γ) (hc : Continuous p)
    (hs : Function.Surjective p) (S : Set U) (hk : p.ker = (Subgroup.normalClosure S).topologicalClosure)
    (χ : Γ →* kˣ) (y : U → k) (hl : IsLocallyConstant y) (hy : ∀ s t, y (s * t) = y s + χ (p s) * y t)
    (hS : ∀ s ∈ S, y s = 0) :
    ∃ φ : Γ → k, IsLocallyConstant φ ∧ ∀ s, φ (p s) = y s := by
  have hy1 : y 1 = 0 := by
    have e := hy 1 1
    rw [mul_one, map_one, map_one, Units.val_one, one_mul] at e
    linear_combination -e
  let H : Subgroup U :=
    { carrier := {t | p t = 1 ∧ y t = 0}
      one_mem' := ⟨map_one p, hy1⟩
      mul_mem' := by
        rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
        show p (a * b) = 1 ∧ y (a * b) = 0
        refine ⟨by rw [map_mul, ha1, hb1, one_mul], ?_⟩
        rw [hy, ha2, hb2, mul_zero, add_zero]
      inv_mem' := by
        rintro a ⟨ha1, ha2⟩
        show p a⁻¹ = 1 ∧ y a⁻¹ = 0
        refine ⟨by rw [map_inv, ha1, inv_one], ?_⟩
        have e := hy a a⁻¹
        rw [mul_inv_cancel, hy1, ha2, ha1, map_one, Units.val_one, one_mul, zero_add] at e
        exact e.symm }
  have hH : H.Normal := ⟨fun t ht g => by
    obtain ⟨ht1, ht2⟩ := ht
    show p (g * t * g⁻¹) = 1 ∧ y (g * t * g⁻¹) = 0
    refine ⟨by rw [map_mul, map_mul, map_inv, ht1, mul_one, mul_inv_cancel], ?_⟩
    have e1 := hy (g * t) g⁻¹
    have e2 := hy g t
    have e3 := hy g g⁻¹
    rw [mul_inv_cancel, hy1] at e3
    rw [map_mul, ht1, mul_one] at e1
    rw [ht2, mul_zero, add_zero] at e2
    rw [e1, e2, ← e3]⟩
  have hcl : IsClosed (H : Set U) :=
    (isClosed_eq hc continuous_const).inter (hl.isClosed_fiber 0)
  have hKH : p.ker ≤ H := by
    rw [hk]
    apply Subgroup.topologicalClosure_minimal _ _ hcl
    haveI := hH
    apply Subgroup.normalClosure_le_normal
    intro s hsS
    have hps : p s = 1 := by
      rw [← MonoidHom.mem_ker, hk]
      exact Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure hsS)
    exact ⟨hps, hS s hsS⟩
  have hfib : ∀ s t, p s = p t → y s = y t := by
    intro s t hst
    have hk' : s⁻¹ * t ∈ p.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, hst, inv_mul_cancel]
    obtain ⟨_, h2⟩ := hKH hk'
    have e := hy s (s⁻¹ * t)
    rw [mul_inv_cancel_left, h2, mul_zero, add_zero] at e
    exact e.symm
  have hq : Topology.IsQuotientMap p := (hc.isClosedMap).isQuotientMap hc hs
  refine ⟨fun γ => y (Function.surjInv hs γ), fun V => ?_, fun s => hfib _ _ (Function.surjInv_eq hs (p s))⟩
  have e : p ⁻¹' ((fun γ => y (Function.surjInv hs γ)) ⁻¹' V) = y ⁻¹' V := by
    ext s
    simp only [Set.mem_preimage]
    rw [hfib _ _ (Function.surjInv_eq hs (p s))]
  apply hq.isOpen_preimage.mp
  rw [e]
  exact hl V

end UpperTheory.V.Fr.DescentValuationAlt

open UpperTheory.V.Fr.DescentValuationAlt in
/- English proof (translation)
Introduce `Ω _ _ _ l _ O _ _ _ η Ψ σ B M Hb hG m L _ _ _ _ g₁ Φ hU hL a ha hS`. Take `⟨k, -⟩` from `hL`. Take `⟨y, hyl, hyc, hyn, hyd, hyi⟩` from `hS`. Establish `hχ : ∀ s : upl Ω L, (Φ.Ψ⁻¹ ^ a * Φ.delK (ResidueField O)) (k.p s) = ((barChar O Ψ)⁻¹ ^ a * etaO O η) s`. Introduce `s`.

Rewrite using `[MonoidHom.mul_apply, MonoidHom.mul_apply, MonoidHom.pow_apply, MonoidHom.pow_apply, MonoidHom.inv_apply, MonoidHom.inv_apply, k.psi]`. Use `congr 1`. Simplify using `only [Frame.delK, etaO, MonoidHom.comp_apply, k.del]`. Establish `hUc : IsClosed (upl Ω L : Set (G ℚ Ω))` using `Subgroup.isClosed_of_isOpen _ hU.isOpen`. Use `haveI : CompactSpace (upl Ω L) := isCompact_iff_compactSpace.mp hUc.isCompact`.

Take `⟨φ, hφl, hφ⟩` from `descend k.p k.p_cont k.p_surj _ k.p_ker (Φ.Ψ⁻¹ ^ a * Φ.delK (ResidueField O)) (fun s => y s) (hyl.comp_continuous continuous_subtype_val) (fun s t => by rw [hχ s]; exact hyc s t) (fun s hs => by`. Take `⟨B', hB', hI, hη, hb⟩` from `hs`. Conclude with `hyi B' hB' s (Subgroup.mem_inf.mpr ⟨hI, s.2⟩) hη hb)`. Establish `hρ : ∀ (γ : Φ.Γ) (w : ResidueField O), (chRep (Φ.Ψ⁻¹ ^ a * Φ.delK (ResidueField O)) γ) w = ((Φ.Ψ⁻¹ ^ a * Φ.delK (ResidueField O)) γ : ResidueField O) * w` using `fun γ w => rfl`. Establish `hcoc : ∀ γ δ : Φ.Γ, φ (γ * δ) = φ γ + ((Φ.Ψ⁻¹ ^ a * Φ.delK (ResidueField O)) γ : ResidueField O) * φ δ`.

Introduce `γ δ`. Take `⟨s, rfl⟩` from `k.p_surj γ`. Take `⟨t, rfl⟩` from `k.p_surj δ`. Rewrite using `[← map_mul, hφ, hφ, hφ, hχ]`. Conclude with `hyc s t`.

Establish `hloc : ∀ v : Φ.V, ∃ b : ResidueField O, ∀ g : Φ.Gv v, φ (Φ.loc v g) = ((Φ.Ψ⁻¹ ^ a * Φ.delK (ResidueField O)) (Φ.loc v g) : ResidueField O) * b - b`. Introduce `v`. Take `⟨γ, -, hγ⟩` from `k.pl_conj v`. Establish `hv : (k.pl v).valuation (l : Ω) < 1`. Rewrite using `[hγ]`.

Conclude with `smul_val_lt γ B l hG.over_l`. Take `⟨b, hb⟩` from `hyd _ hv`. Use `⟨b, fun g => ?_⟩` and prove the remaining obligations. Rewrite using `[k.j_loc, hφ, hχ]`. Conclude with `hb _ ((k.j_range v _).mp (MonoidHom.mem_range.mpr ⟨g, rfl⟩))`.

Use `choose b hb using hloc`. Set `z : Z1C Φ.loc (chRep (Φ.Ψ⁻¹ ^ a * Φ.delK (ResidueField O))) (fun _ => ⊥)` to `⟨(φ, b), ⟨hφl, fun γ δ => by rw [hρ]; exact hcoc γ δ, fun v g => by rw [Submodule.mem_bot, hρ, ← hb v g, sub_self]⟩⟩`. Use `⟨⟨Submodule.Quotient.mk z, 0, fun h => ?_⟩⟩` and prove the remaining obligations. Establish `hz` using `(Submodule.Quotient.mk_eq_zero _).mp h`. Rewrite `hz` using `[Submodule.mem_comap]`.

Take `⟨X, hX1, -⟩` from `hz`. Apply `hyn` to reduce the goal to its premises. Use `⟨X, fun s hs => ?_⟩` and prove the remaining obligations. Establish `e1` using `hφ ⟨s, hs⟩`. Establish `e2` using `hX1 (k.p ⟨s, hs⟩)`.

Rewrite `e2` using `[hρ, hχ]`. Rewrite using `[← e2]`. Conclude with `e1.symm`.
-/
theorem UpperTheory.V.Fr.frobenius_galoisField_four_compatibility :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [CharP (ResidueField O) l] (η : G ℚ Ω →* ℤˣ) (Ψ : G ℚ Ω →* Oˣ) (σ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ) (Hb : Subgroup (G ℚ Ω)), Gen l η Ψ σ B M Hb → ∀ (m : ℕ) (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] (g₁ : G ℚ Ω) (Φ : Frame l (ResidueField O)), UFacts l η Ψ M m (upl Ω L) → Linked l η Ψ σ g₁ B M L Φ → ∀ a : ℕ, a = 1 ∨ a = 2 → StrictCl l η Ψ ((barChar O Ψ)⁻¹ ^ a * etaO O η) (upl Ω L) → Nontrivial (H1C Φ.loc (chRep (Φ.Ψ⁻¹ ^ a * Φ.delK (ResidueField O))) fun _ => ⊥) := by
  intro Ω _ _ _ l _ O _ _ _ η Ψ σ B M Hb hG m L _ _ _ _ g₁ Φ hU hL a ha hS
  obtain ⟨k, -⟩ := hL
  obtain ⟨y, hyl, hyc, hyn, hyd, hyi⟩ := hS
  have hχ : ∀ s : upl Ω L, (Φ.Ψ⁻¹ ^ a * Φ.delK (ResidueField O)) (k.p s)
      = ((barChar O Ψ)⁻¹ ^ a * etaO O η) s := by
    intro s
    rw [MonoidHom.mul_apply, MonoidHom.mul_apply, MonoidHom.pow_apply, MonoidHom.pow_apply,
      MonoidHom.inv_apply, MonoidHom.inv_apply, k.psi]
    congr 1
    simp only [Frame.delK, etaO, MonoidHom.comp_apply, k.del]
  have hUc : IsClosed (upl Ω L : Set (G ℚ Ω)) := Subgroup.isClosed_of_isOpen _ hU.isOpen
  haveI : CompactSpace (upl Ω L) := isCompact_iff_compactSpace.mp hUc.isCompact
  obtain ⟨φ, hφl, hφ⟩ := descend k.p k.p_cont k.p_surj _ k.p_ker (Φ.Ψ⁻¹ ^ a * Φ.delK (ResidueField O))
    (fun s => y s) (hyl.comp_continuous continuous_subtype_val)
    (fun s t => by rw [hχ s]; exact hyc s t)
    (fun s hs => by
      obtain ⟨B', hB', hI, hη, hb⟩ := hs
      exact hyi B' hB' s (Subgroup.mem_inf.mpr ⟨hI, s.2⟩) hη hb)
  have hρ : ∀ (γ : Φ.Γ) (w : ResidueField O),
      (chRep (Φ.Ψ⁻¹ ^ a * Φ.delK (ResidueField O)) γ) w
        = ((Φ.Ψ⁻¹ ^ a * Φ.delK (ResidueField O)) γ : ResidueField O) * w := fun γ w => rfl
  have hcoc : ∀ γ δ : Φ.Γ, φ (γ * δ)
      = φ γ + ((Φ.Ψ⁻¹ ^ a * Φ.delK (ResidueField O)) γ : ResidueField O) * φ δ := by
    intro γ δ
    obtain ⟨s, rfl⟩ := k.p_surj γ
    obtain ⟨t, rfl⟩ := k.p_surj δ
    rw [← map_mul, hφ, hφ, hφ, hχ]
    exact hyc s t
  have hloc : ∀ v : Φ.V, ∃ b : ResidueField O, ∀ g : Φ.Gv v,
      φ (Φ.loc v g) = ((Φ.Ψ⁻¹ ^ a * Φ.delK (ResidueField O)) (Φ.loc v g) : ResidueField O) * b - b := by
    intro v
    obtain ⟨γ, -, hγ⟩ := k.pl_conj v
    have hv : (k.pl v).valuation (l : Ω) < 1 := by
      rw [hγ]
      exact smul_val_lt γ B l hG.over_l
    obtain ⟨b, hb⟩ := hyd _ hv
    refine ⟨b, fun g => ?_⟩
    rw [k.j_loc, hφ, hχ]
    exact hb _ ((k.j_range v _).mp (MonoidHom.mem_range.mpr ⟨g, rfl⟩))
  choose b hb using hloc
  let z : Z1C Φ.loc (chRep (Φ.Ψ⁻¹ ^ a * Φ.delK (ResidueField O))) (fun _ => ⊥) :=
    ⟨(φ, b), ⟨hφl, fun γ δ => by rw [hρ]; exact hcoc γ δ,
      fun v g => by rw [Submodule.mem_bot, hρ, ← hb v g, sub_self]⟩⟩
  refine ⟨⟨Submodule.Quotient.mk z, 0, fun h => ?_⟩⟩
  have hz := (Submodule.Quotient.mk_eq_zero _).mp h
  rw [Submodule.mem_comap] at hz
  obtain ⟨X, hX1, -⟩ := hz
  apply hyn
  refine ⟨X, fun s hs => ?_⟩
  have e1 := hφ ⟨s, hs⟩
  have e2 := hX1 (k.p ⟨s, hs⟩)
  rw [hρ, hχ] at e2
  rw [← e2]
  exact e1.symm
