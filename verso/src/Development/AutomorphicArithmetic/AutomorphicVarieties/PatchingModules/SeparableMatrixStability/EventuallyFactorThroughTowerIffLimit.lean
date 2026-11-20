import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.MapEta

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private def stabR {P Z : Type} [Group P] (c : P → Z) : Subgroup P where
  carrier := {k | ∀ g, c (g * k) = c g}
  one_mem' g := by rw [mul_one]
  mul_mem' {a b} ha hb g := by rw [← mul_assoc, hb, ha]
  inv_mem' {a} ha g := by
    have := ha (g * a⁻¹)
    rw [inv_mul_cancel_right] at this
    exact this.symm

/- English proof (translation)
Apply `Subgroup.isOpen_of_mem_nhds (g := 1)` to reduce the goal to its premises. Establish `key : ∀ z ∈ Set.range c, ∀ᶠ k in nhds (1 : P), ∀ g, c g = z → c (g * k) = z`. Introduce `z _`. Establish `hK : IsCompact (c ⁻¹' {z})` using `(hc.isClosed_fiber z).isCompact`. Take `⟨V, hV, hKV⟩` from `compact_open_separated_mul_right hK (hc.isOpen_fiber z) le_rfl`.

Use `filter_upwards [hV] with k hk g hg`. Conclude with `hKV (Set.mul_mem_mul hg hk)`. Establish `hall` using `(Filter.eventually_all_finite hc.range_finite).2 key`. Use `filter_upwards [hall] with k hk`. Conclude with `(show ∀ g, c (g * k) = c g from fun g => hk (c g) ⟨g, rfl⟩ g rfl)`.
-/
private theorem stabR_open {P Z : Type} [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P]
    (c : P → Z) (hc : IsLocallyConstant c) : IsOpen (stabR c : Set P) := by
  classical
  apply Subgroup.isOpen_of_mem_nhds (g := 1)
  have key : ∀ z ∈ Set.range c, ∀ᶠ k in nhds (1 : P), ∀ g, c g = z → c (g * k) = z := by
    intro z _
    have hK : IsCompact (c ⁻¹' {z}) := (hc.isClosed_fiber z).isCompact
    obtain ⟨V, hV, hKV⟩ := compact_open_separated_mul_right hK (hc.isOpen_fiber z) le_rfl
    filter_upwards [hV] with k hk g hg
    exact hKV (Set.mul_mem_mul hg hk)
  have hall := (Filter.eventually_all_finite hc.range_finite).2 key
  filter_upwards [hall] with k hk
  exact (show ∀ g, c (g * k) = c g from fun g => hk (c g) ⟨g, rfl⟩ g rfl)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz⟩ k hk show ∀ g, c (g * k) = c g`. Introduce `g`. Rewrite using `[← hz, ← hz, map_mul, MonoidHom.mem_ker.1 hk, mul_one]`. Introduce `hle`.

Use `⟨fun a => c (Classical.choose (hf a)), fun g => ?_⟩` and prove the remaining obligations. Use `show c (Classical.choose (hf (f g))) = c g`. Establish `hspec : f (Classical.choose (hf (f g))) = f g` using `Classical.choose_spec (hf (f g))`. Generalize the expression as in `Classical.choose (hf (f g)) = g' at hspec ⊢`. Establish `hk : g'⁻¹ * g ∈ f.ker`.

Rewrite using `[MonoidHom.mem_ker, map_mul, map_inv, hspec, inv_mul_cancel]`. Use `(show ∀ y, c (y * (g'⁻¹ * g)) = c y from hle hk) g'` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel_left]`. Conclude with `this.symm`.
-/
private theorem fac_iff {P A Z : Type} [Group P] [Group A] (f : P →* A) (hf : Function.Surjective f) (c : P → Z) :
    (∃ z : A → Z, ∀ g, z (f g) = c g) ↔ f.ker ≤ stabR c := by
  constructor
  · rintro ⟨z, hz⟩ k hk
    show ∀ g, c (g * k) = c g
    intro g
    rw [← hz, ← hz, map_mul, MonoidHom.mem_ker.1 hk, mul_one]
  · intro hle
    refine ⟨fun a => c (Classical.choose (hf a)), fun g => ?_⟩
    show c (Classical.choose (hf (f g))) = c g
    have hspec : f (Classical.choose (hf (f g))) = f g := Classical.choose_spec (hf (f g))
    generalize Classical.choose (hf (f g)) = g' at hspec ⊢
    have hk : g'⁻¹ * g ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hspec, inv_mul_cancel]
    have := (show ∀ y, c (y * (g'⁻¹ * g)) = c y from hle hk) g'
    rw [mul_inv_cancel_left] at this
    exact this.symm

/- English proof (translation)
Establish `hker : ∀ h : H, h ∈ f.ker ↔ (h : P) ∈ π.ker`. Introduce `h`. Rewrite using `[MonoidHom.mem_ker, MonoidHom.mem_ker, ← hf, OneMemClass.coe_eq_one]`. Prove the components needed by the constructor for the conclusion. Introduce `hle`.

Rewrite using `[Subgroup.normal_le_normalCore]`. Introduce `k hk`. Establish `hkH : k ∈ H` using `hH hk`. Conclude with `⟨⟨k, hkH⟩, hle ((hker ⟨k, hkH⟩).2 hk), rfl⟩`. Introduce `hle h hh`.

Take `⟨s, hs, hsh⟩` from `(Subgroup.normalCore_le _) (hle ((hker h).1 hh))`. Establish `: s = h` using `Subtype.ext hsh`. Rewrite using `[← this]`. Conclude with `hs`.
-/
private theorem ker_iff {P A : Type} [Group P] [Group A] (H : Subgroup P) (B : Subgroup A) (π : P →* A)
    (f : H →* B) (hf : ∀ g, (f g : A) = π g) (hH : π.ker ≤ H) (S : Subgroup H) :
    f.ker ≤ S ↔ π.ker ≤ (S.map H.subtype).normalCore := by
  have hker : ∀ h : H, h ∈ f.ker ↔ (h : P) ∈ π.ker := by
    intro h
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, ← hf, OneMemClass.coe_eq_one]
  constructor
  · intro hle
    rw [Subgroup.normal_le_normalCore]
    intro k hk
    have hkH : k ∈ H := hH hk
    exact ⟨⟨k, hkH⟩, hle ((hker ⟨k, hkH⟩).2 hk), rfl⟩
  · intro hle h hh
    obtain ⟨s, hs, hsh⟩ := (Subgroup.normalCore_le _) (hle ((hker h).1 hh))
    have : s = h := Subtype.ext hsh
    rw [← this]
    exact hs

/- English proof (translation)
Introduce `l _ L G0 T Λ Z c hc`. Use `set K0 : Subgroup Λ.Ph := (Λ.G.η.comp Λ.πo).ker with hK0def`. Establish `hK0 : IsOpen (K0 : Set Λ.Ph)` using `Λ.Ph0_open`. Use `haveI : CompactSpace Λ.Ph0 := isCompact_iff_compactSpace.mp (K0.isClosed_of_isOpen hK0).isCompact`. Establish `hS : IsOpen (stabR c : Set Λ.Ph0)` using `stabR_open c hc`.

Establish `hO : IsOpen (((stabR c).map K0.subtype : Subgroup Λ.Ph) : Set Λ.Ph)`. Rewrite using `[Subgroup.coe_map]`. Conclude with `hK0.isOpenMap_subtype_val _ hS`. Set `O : OpenSubgroup Λ.Ph` to `⟨(stabR c).map K0.subtype, hO⟩`. Use `haveI : Finite (Λ.Ph ⧸ O.toSubgroup) := Subgroup.quotient_finite_of_isOpen _ hO`.

Use `haveI : O.toSubgroup.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient`. Set `V : OpenNormalSubgroup Λ.Ph` to `{ toSubgroup := O.toSubgroup.normalCore isOpen' := Subgroup.isOpen_of_isClosed_of_finiteIndex _ (O.toSubgroup.normalCore_isClosed O.isClosed) }`. Establish `hHo : Λ.πo.ker ≤ K0`. Introduce `k hk`. Rewrite using `[hK0def, MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.mem_ker.1 hk, map_one]`.

Use `filter_upwards [Λ.ker_lim V] with N hN`. Establish `hHN : (Λ.π N).ker ≤ K0`. Introduce `k hk`. Rewrite using `[hK0def, MonoidHom.mem_ker, MonoidHom.comp_apply, ← Λ.η_π N, MonoidHom.mem_ker.1 hk, map_one]`. Rewrite using `[fac_iff _ (Λ.π0_surj N), fac_iff _ Λ.πo0_surj, ker_iff K0 _ (Λ.π N) (Λ.π0 N) (fun g => rfl) hHN, ker_iff K0 _ Λ.πo Λ.πo0 (fun g => rfl) hHo]`.

Establish `e : (Λ.π N).ker ⊔ ((stabR c).map K0.subtype).normalCore = Λ.πo.ker ⊔ ((stabR c).map K0.subtype).normalCore` using `hN`. Rewrite using `[← sup_eq_right, e, sup_eq_right]`.
-/
theorem UpperTheory.V.Pa.eventually_factor_through_tower_iff_limit :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (Z : Type) (c : Λ.Ph0 → Z), IsLocallyConstant c → ∀ᶠ N in (Λ.U : Filter ℕ), ((∃ zN : (T.GN N).G₀ → Z, ∀ g, zN (Λ.π0 N g) = c g) ↔ ∃ z : Λ.G.G₀ → Z, ∀ g, z (Λ.πo0 g) = c g) := by
  intro l _ L G0 T Λ Z c hc
  set K0 : Subgroup Λ.Ph := (Λ.G.η.comp Λ.πo).ker with hK0def
  have hK0 : IsOpen (K0 : Set Λ.Ph) := Λ.Ph0_open
  haveI : CompactSpace Λ.Ph0 := isCompact_iff_compactSpace.mp (K0.isClosed_of_isOpen hK0).isCompact
  have hS : IsOpen (stabR c : Set Λ.Ph0) := stabR_open c hc
  have hO : IsOpen (((stabR c).map K0.subtype : Subgroup Λ.Ph) : Set Λ.Ph) := by
    rw [Subgroup.coe_map]
    exact hK0.isOpenMap_subtype_val _ hS
  let O : OpenSubgroup Λ.Ph := ⟨(stabR c).map K0.subtype, hO⟩
  haveI : Finite (Λ.Ph ⧸ O.toSubgroup) := Subgroup.quotient_finite_of_isOpen _ hO
  haveI : O.toSubgroup.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  let V : OpenNormalSubgroup Λ.Ph :=
    { toSubgroup := O.toSubgroup.normalCore
      isOpen' := Subgroup.isOpen_of_isClosed_of_finiteIndex _ (O.toSubgroup.normalCore_isClosed O.isClosed) }
  have hHo : Λ.πo.ker ≤ K0 := by
    intro k hk
    rw [hK0def, MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.mem_ker.1 hk, map_one]
  filter_upwards [Λ.ker_lim V] with N hN
  have hHN : (Λ.π N).ker ≤ K0 := by
    intro k hk
    rw [hK0def, MonoidHom.mem_ker, MonoidHom.comp_apply, ← Λ.η_π N, MonoidHom.mem_ker.1 hk, map_one]
  rw [fac_iff _ (Λ.π0_surj N), fac_iff _ Λ.πo0_surj,
    ker_iff K0 _ (Λ.π N) (Λ.π0 N) (fun g => rfl) hHN, ker_iff K0 _ Λ.πo Λ.πo0 (fun g => rfl) hHo]
  have e : (Λ.π N).ker ⊔ ((stabR c).map K0.subtype).normalCore =
      Λ.πo.ker ⊔ ((stabR c).map K0.subtype).normalCore := hN
  rw [← sup_eq_right, e, sup_eq_right]
