import Formalism.SharpRestriction.LevelLetterCocycles.RealisedOfCoordArc
import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineMapLemmas

noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G TensorProduct Formalism.MainNotions.N.Ln03 Module

section Period

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

/- English proof (translation)
Take `⟨k, rfl⟩` from `Int.le.dest hab`. Use `clear hab`. Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`.

Rewrite using `[show a + ((k + 1 : ℕ) : ℤ) = a + k + 1 by push_cast; ring]`. Conclude with `(PD.Fil_anti (a + k)).trans ih`.
-/
theorem jb_Fil_anti {a b : ℤ} (hab : a ≤ b) : PD.Fil b ≤ PD.Fil a := by
  obtain ⟨k, rfl⟩ := Int.le.dest hab
  clear hab
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show a + ((k + 1 : ℕ) : ℤ) = a + k + 1 by push_cast; ring]
    exact (PD.Fil_anti (a + k)).trans ih

/- English proof (translation)
Introduce `a b hab`. Establish `h : (PD.Fil b).restrictScalars Qp ≤ (PD.Fil a).restrictScalars Qp` using `jb_Fil_anti PD hab`. Unfold `FilV`. Rewrite using `[← Submodule.subtype_comp_inclusion _ _ h]`. Establish `e : AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (((PD.Fil a).restrictScalars Qp).subtype ∘ₗ Submodule.inclusion h) = AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) ((PD.Fil a).restrictScalars Qp).subtype ∘ₗ AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (Submodu …`.

Rewrite using `[← AlgebraTensorModule.map_comp, LinearMap.id_comp]`. Rewrite using `[e]`. Conclude with `LinearMap.range_comp_le_range _ _`.
-/
theorem jb_FilV_anti : Antitone (FilV PD (LL := LL) (V := V)) := by
  intro a b hab
  have h : (PD.Fil b).restrictScalars Qp ≤ (PD.Fil a).restrictScalars Qp := jb_Fil_anti PD hab
  unfold FilV
  rw [← Submodule.subtype_comp_inclusion _ _ h]
  have e : AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V)
      (((PD.Fil a).restrictScalars Qp).subtype ∘ₗ Submodule.inclusion h) =
      AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) ((PD.Fil a).restrictScalars Qp).subtype ∘ₗ
        AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (Submodule.inclusion h) := by
    rw [← AlgebraTensorModule.map_comp, LinearMap.id_comp]
  rw [e]
  exact LinearMap.range_comp_le_range _ _

/- English proof (translation)
Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, zero_mem _⟩`. Consider the case `tmul v b`. Take `⟨a, ha⟩` from `PD.Fil_exh b`. Conclude with `⟨a, ⟨v ⊗ₜ ⟨b, ha⟩, by simp⟩⟩`.

Consider the case `add x y hx hy`. Take `⟨a, ha⟩` from `hx`. Take `⟨b, hb⟩` from `hy`. Conclude with `⟨min a b, add_mem (jb_FilV_anti PD (min_le_left a b) ha) (jb_FilV_anti PD (min_le_right a b) hb)⟩`.
-/
theorem jb_FilV_exh (y : V ⊗[Qp] BdR) : ∃ a, y ∈ FilV PD (LL := LL) (V := V) a := by
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, zero_mem _⟩
  | tmul v b =>
    obtain ⟨a, ha⟩ := PD.Fil_exh b
    exact ⟨a, ⟨v ⊗ₜ ⟨b, ha⟩, by simp⟩⟩
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨min a b, add_mem (jb_FilV_anti PD (min_le_left a b) ha)
      (jb_FilV_anti PD (min_le_right a b) hb)⟩

/- English proof (translation)
Set `bV` to `Module.Free.chooseBasis Qp V`. Set `e` to `TensorProduct.equivFinsuppOfBasisLeft (N := BdR) bV`. Establish `hc : ∀ a, ∀ z ∈ FilV PD (LL` using `LL) (V := V) a, ∀ i, e z i ∈ PD.Fil a := by`. Introduce `a z hz i`. Take `⟨t, rfl⟩` from `hz`.

Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul v f`. Simplify using `only [AlgebraTensorModule.map_tmul, LinearMap.id_apply, Submodule.subtype_apply, e, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]`. Conclude with `(PD.Fil a).smul_of_tower_mem _ f.2`.

Consider the case `add x y hx hy`. Rewrite using `[map_add, map_add, Finsupp.add_apply]`. Conclude with `add_mem hx hy`. Establish `h0 : e y = 0`. Use extensionality with `i`.

Conclude with `PD.Fil_sep _ (fun a => hc a y (hy a) i)`. Conclude with `e.injective (by rw [h0, map_zero])`.
-/
theorem jb_FilV_sep (y : V ⊗[Qp] BdR) (hy : ∀ a, y ∈ FilV PD (LL := LL) (V := V) a) : y = 0 := by
  classical
  let bV := Module.Free.chooseBasis Qp V
  let e := TensorProduct.equivFinsuppOfBasisLeft (N := BdR) bV
  have hc : ∀ a, ∀ z ∈ FilV PD (LL := LL) (V := V) a, ∀ i, e z i ∈ PD.Fil a := by
    intro a z hz i
    obtain ⟨t, rfl⟩ := hz
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul v f =>
      simp only [AlgebraTensorModule.map_tmul, LinearMap.id_apply, Submodule.subtype_apply, e,
        TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
      exact (PD.Fil a).smul_of_tower_mem _ f.2
    | add x y hx hy =>
      rw [map_add, map_add, Finsupp.add_apply]
      exact add_mem hx hy
  have h0 : e y = 0 := by
    ext i
    exact PD.Fil_sep _ (fun a => hc a y (hy a) i)
  exact e.injective (by rw [h0, map_zero])

/- English proof (translation)
Introduce `_ _ hab` and use `inf_le_inf_left _ (jb_FilV_anti PD hab)`.
-/
theorem jb_FildR_anti (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL) : Antitone (FildR PD ρ τ) :=
  fun _ _ hab => inf_le_inf_left _ (jb_FilV_anti PD hab)

/- English proof (translation)
Use `set D := DdRE PD ρ τ with hD`. Establish `hFD : ∀ a, FildR PD ρ τ a ≤ D` using `fun a => inf_le_left`. Set `bD` to `Module.finBasis LL ↥D`. Establish `hex : ∀ j, ∃ a, ((bD j : ↥D) : V ⊗[Qp] BdR) ∈ FilV PD (LL` using `LL) (V := V) a := fun j => jb_FilV_exh PD (LL := LL) (V := V) _`. Use `choose aj haj using hex`.

Use `set a₀ : ℤ := -(∑ j, |aj j|) with ha₀`. Establish `ha₀j : ∀ j, a₀ ≤ aj j`. Introduce `j`. Establish `h1 : |aj j| ≤ ∑ k, |aj k|` using `Finset.single_le_sum (f := fun k => |aj k|) (fun k _ => abs_nonneg _) (Finset.mem_univ j)`. Establish `h2` using `neg_abs_le (aj j)`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlow : ∀ a, a ≤ a₀ → FildR PD ρ τ a = D`. Introduce `a ha`. Use `le_antisymm (hFD a) (le_inf le_rfl ?_)` and prove the remaining obligations. Establish `hspan : (Submodule.span LL (Set.range bD)).map D.subtype = D`.

Rewrite using `[bD.span_eq, Submodule.map_top, Submodule.range_subtype]`. Rewrite using `[← hspan, Submodule.map_span, Submodule.span_le]`. Introduce and unpack `_ ⟨_, ⟨j, rfl⟩, rfl⟩`. Conclude with `jb_FilV_anti PD (ha.trans (ha₀j j)) (haj j)`. Set `f : ℕ → ℕ` to `fun k => finrank LL ↥(FildR PD ρ τ (k : ℤ))`.

Establish `hne : ∃ m, ∃ k, f k = m` using `⟨_, 0, rfl⟩`. Set `m` to `Nat.find hne`. Take `⟨k₀, hk₀⟩` from `Nat.find_spec hne`. Establish `hmin : ∀ k, m ≤ f k` using `fun k => Nat.find_min' hne ⟨k, rfl⟩`. Establish `hfinF : ∀ a, FiniteDimensional LL ↥(FildR PD ρ τ a)` using `fun a => Submodule.finiteDimensional_of_le (hFD a)`.

Establish `hstab : ∀ k : ℕ, k₀ ≤ k → FildR PD ρ τ (k : ℤ) = FildR PD ρ τ (k₀ : ℤ)`. Introduce `k hk`. Establish `hle : FildR PD ρ τ (k : ℤ) ≤ FildR PD ρ τ (k₀ : ℤ)` using `jb_FildR_anti PD ρ τ (by exact_mod_cast hk)`. Establish `hr1 : f k ≤ f k₀` using `Submodule.finrank_mono hle`. Establish `hr2` using `hmin k`.

Conclude with `Submodule.eq_of_le_of_finrank_eq hle (by show f k = f k₀; omega)`. Establish `hbot : FildR PD ρ τ (k₀ : ℤ) = ⊥`. Rewrite using `[eq_bot_iff]`. Introduce `x hx`. Rewrite using `[Submodule.mem_bot]`.

Apply `jb_FilV_sep PD (LL := LL) (V := V) x` to reduce the goal to its premises. Introduce `a`. Break down `le_total a (k₀ : ℤ) with h | h` into its components or cases. Conclude with `jb_FilV_anti PD (LL := LL) (V := V) h hx.2`. Take `⟨k, rfl⟩` from `Int.eq_ofNat_of_zero_le (le_trans (Int.natCast_nonneg k₀) h)`.

Establish `hk : k₀ ≤ k` using `by exact_mod_cast h`. Rewrite `hx` using `[← hstab k hk]`. Conclude with `hx.2`. Establish `hhigh : ∀ a, (k₀ : ℤ) ≤ a → FildR PD ρ τ a = ⊥` using `fun a ha => eq_bot_iff.mpr (hbot ▸ jb_FildR_anti PD ρ τ ha)`. Use `⟨a₀, (k₀ : ℤ) - 1, fun a ha => ⟨?_, ?_⟩⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hlt`. Conclude with `ha (by rw [hlow a (by omega), hlow (a + 1) (by omega)])`. Assume the negation of the conclusion as `hlt`. Conclude with `ha (by rw [hhigh a (by omega), hhigh (a + 1) (by omega)])`.
-/
theorem jb_bound (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL) (hfin : FiniteDimensional LL ↥(DdRE PD ρ τ)) :
    ∃ a₀ a₁ : ℤ, ∀ a, IsJumpV PD ρ τ a → a₀ ≤ a ∧ a ≤ a₁ := by
  classical
  set D := DdRE PD ρ τ with hD
  have hFD : ∀ a, FildR PD ρ τ a ≤ D := fun a => inf_le_left

  let bD := Module.finBasis LL ↥D
  have hex : ∀ j, ∃ a, ((bD j : ↥D) : V ⊗[Qp] BdR) ∈ FilV PD (LL := LL) (V := V) a :=
    fun j => jb_FilV_exh PD (LL := LL) (V := V) _
  choose aj haj using hex
  set a₀ : ℤ := -(∑ j, |aj j|) with ha₀
  have ha₀j : ∀ j, a₀ ≤ aj j := by
    intro j
    have h1 : |aj j| ≤ ∑ k, |aj k| :=
      Finset.single_le_sum (f := fun k => |aj k|) (fun k _ => abs_nonneg _) (Finset.mem_univ j)
    have h2 := neg_abs_le (aj j)
    linarith
  have hlow : ∀ a, a ≤ a₀ → FildR PD ρ τ a = D := by
    intro a ha
    refine le_antisymm (hFD a) (le_inf le_rfl ?_)
    have hspan : (Submodule.span LL (Set.range bD)).map D.subtype = D := by
      rw [bD.span_eq, Submodule.map_top, Submodule.range_subtype]
    rw [← hspan, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    exact jb_FilV_anti PD (ha.trans (ha₀j j)) (haj j)

  let f : ℕ → ℕ := fun k => finrank LL ↥(FildR PD ρ τ (k : ℤ))
  have hne : ∃ m, ∃ k, f k = m := ⟨_, 0, rfl⟩
  let m := Nat.find hne
  obtain ⟨k₀, hk₀⟩ := Nat.find_spec hne
  have hmin : ∀ k, m ≤ f k := fun k => Nat.find_min' hne ⟨k, rfl⟩
  have hfinF : ∀ a, FiniteDimensional LL ↥(FildR PD ρ τ a) :=
    fun a => Submodule.finiteDimensional_of_le (hFD a)
  have hstab : ∀ k : ℕ, k₀ ≤ k → FildR PD ρ τ (k : ℤ) = FildR PD ρ τ (k₀ : ℤ) := by
    intro k hk
    have hle : FildR PD ρ τ (k : ℤ) ≤ FildR PD ρ τ (k₀ : ℤ) := jb_FildR_anti PD ρ τ (by exact_mod_cast hk)
    have hr1 : f k ≤ f k₀ := Submodule.finrank_mono hle
    have hr2 := hmin k
    exact Submodule.eq_of_le_of_finrank_eq hle (by show f k = f k₀; omega)
  have hbot : FildR PD ρ τ (k₀ : ℤ) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_bot]
    apply jb_FilV_sep PD (LL := LL) (V := V) x
    intro a
    rcases le_total a (k₀ : ℤ) with h | h
    · exact jb_FilV_anti PD (LL := LL) (V := V) h hx.2
    · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le (le_trans (Int.natCast_nonneg k₀) h)
      have hk : k₀ ≤ k := by exact_mod_cast h
      rw [← hstab k hk] at hx
      exact hx.2
  have hhigh : ∀ a, (k₀ : ℤ) ≤ a → FildR PD ρ τ a = ⊥ := fun a ha =>
    eq_bot_iff.mpr (hbot ▸ jb_FildR_anti PD ρ τ ha)
  refine ⟨a₀, (k₀ : ℤ) - 1, fun a ha => ⟨?_, ?_⟩⟩
  · by_contra hlt
    exact ha (by rw [hlow a (by omega), hlow (a + 1) (by omega)])
  · by_contra hlt
    exact ha (by rw [hhigh a (by omega), hhigh (a + 1) (by omega)])

end Period

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    [Fintype (K →ₐ[Qp] LL)]

/- English proof (translation)
Introduce `T hT`. Establish `hfin : ∀ τ : K →ₐ[Qp] LL, FiniteDimensional LL ↥(DdRE PD T.ρ τ)` using `fun τ => ((hDR hK T.V T.ρ T.cont hT.2.2.2).2 τ).1`. Use `choose a₀ a₁ hab using fun τ => jb_bound PD T.ρ τ (hfin τ)`. Use `⟨fun _ => Finset.univ.sup (fun τ => (-a₀ τ).toNat), fun _ => Finset.univ.sup (fun τ => (a₁ τ).toNat), ?_⟩` and prove the remaining obligations. Introduce `i τ _ a ha`.

Take `⟨h0, h1⟩` from `hab τ a ha`. Establish `e0 : (-a₀ τ).toNat ≤ Finset.univ.sup (fun τ => (-a₀ τ).toNat)` using `Finset.le_sup (f := fun τ => (-a₀ τ).toNat) (Finset.mem_univ τ)`. Establish `e1 : (a₁ τ).toNat ≤ Finset.univ.sup (fun τ => (a₁ τ).toNat)` using `Finset.le_sup (f := fun τ => (a₁ τ).toNat) (Finset.mem_univ τ)`. Establish `f0` using `Int.self_le_toNat (-a₀ τ)`. Establish `f1` using `Int.self_le_toNat (a₁ τ)`.

Establish `g0 : (((-a₀ τ).toNat : ℕ) : ℤ) ≤ ((Finset.univ.sup (fun τ => (-a₀ τ).toNat) : ℕ) : ℤ)` using `by exact_mod_cast e0`. Establish `g1 : (((a₁ τ).toNat : ℕ) : ℤ) ≤ ((Finset.univ.sup (fun τ => (a₁ τ).toNat) : ℕ) : ℤ)` using `by exact_mod_cast e1`. Simplify using `only [Set.mem_Icc]`. Apply the tactic sequence `constructor <;> omega`.
-/
theorem jumpsBdd_holds (hDR : Formalism.MainNotions.TruncatedSeriesCountingBounds.DdREqDcris PD LL) (hK : Function.Bijective (algebraMap K₀ K)) :
    ∀ T : LocLat G Qp LL O, CrysLat PD T → ∃ M h : ZMod n → ℕ, Formalism.MainNotions.LiftingTheory.JumpsLet W T M h := by
  intro T hT
  have hfin : ∀ τ : K →ₐ[Qp] LL, FiniteDimensional LL ↥(DdRE PD T.ρ τ) :=
    fun τ => ((hDR hK T.V T.ρ T.cont hT.2.2.2).2 τ).1
  choose a₀ a₁ hab using fun τ => jb_bound PD T.ρ τ (hfin τ)
  refine ⟨fun _ => Finset.univ.sup (fun τ => (-a₀ τ).toNat),
    fun _ => Finset.univ.sup (fun τ => (a₁ τ).toNat), ?_⟩
  intro i τ _ a ha
  obtain ⟨h0, h1⟩ := hab τ a ha
  have e0 : (-a₀ τ).toNat ≤ Finset.univ.sup (fun τ => (-a₀ τ).toNat) :=
    Finset.le_sup (f := fun τ => (-a₀ τ).toNat) (Finset.mem_univ τ)
  have e1 : (a₁ τ).toNat ≤ Finset.univ.sup (fun τ => (a₁ τ).toNat) :=
    Finset.le_sup (f := fun τ => (a₁ τ).toNat) (Finset.mem_univ τ)
  have f0 := Int.self_le_toNat (-a₀ τ)
  have f1 := Int.self_le_toNat (a₁ τ)
  have g0 : (((-a₀ τ).toNat : ℕ) : ℤ) ≤ ((Finset.univ.sup (fun τ => (-a₀ τ).toNat) : ℕ) : ℤ) := by exact_mod_cast e0
  have g1 : (((a₁ τ).toNat : ℕ) : ℤ) ≤ ((Finset.univ.sup (fun τ => (a₁ τ).toNat) : ℕ) : ℤ) := by exact_mod_cast e1
  simp only [Set.mem_Icc]
  constructor <;> omega

end Formalism.MainNotions.N.Ln03.Pf
