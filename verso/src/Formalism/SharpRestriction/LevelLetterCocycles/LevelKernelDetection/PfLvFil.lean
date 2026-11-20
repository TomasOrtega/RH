import Formalism.SharpRestriction.LevelLetterCocycles.FinalLevelsOf

noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G TensorProduct Formalism.MainNotions.N.Ln03

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
theorem lvFil_Fil_anti {a b : ℤ} (hab : a ≤ b) : PD.Fil b ≤ PD.Fil a := by
  obtain ⟨k, rfl⟩ := Int.le.dest hab
  clear hab
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show a + ((k + 1 : ℕ) : ℤ) = a + k + 1 by push_cast; ring]
    exact (PD.Fil_anti (a + k)).trans ih

/- English proof (translation)
Introduce `a b hab`. Establish `h : (PD.Fil b).restrictScalars Qp ≤ (PD.Fil a).restrictScalars Qp` using `lvFil_Fil_anti PD hab`. Unfold `FilV`. Rewrite using `[← Submodule.subtype_comp_inclusion _ _ h]`. Establish `e : AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (((PD.Fil a).restrictScalars Qp).subtype ∘ₗ Submodule.inclusion h) = AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) ((PD.Fil a).restrictScalars Qp).subtype ∘ₗ AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (Submodu …`.

Rewrite using `[← AlgebraTensorModule.map_comp, LinearMap.id_comp]`. Rewrite using `[e]`. Conclude with `LinearMap.range_comp_le_range _ _`.
-/
theorem lvFil_FilV_anti : Antitone (FilV PD (LL := LL) (V := V)) := by
  intro a b hab
  have h : (PD.Fil b).restrictScalars Qp ≤ (PD.Fil a).restrictScalars Qp := lvFil_Fil_anti PD hab
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
Introduce `a b hab`. Conclude with `inf_le_inf_left _ (Submodule.comap_mono (lvFil_FilV_anti PD hab))`.
-/
theorem lvFil_FilCris_anti (ρ : Representation LL G V) : Antitone (FilCris PD ρ) := by
  intro a b hab
  exact inf_le_inf_left _ (Submodule.comap_mono (lvFil_FilV_anti PD hab))

/- English proof (translation)
Establish `e : ⇑(AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) g) = ⇑(g.lTensor V)`. Use function extensionality and compare the values at `x`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b => simp`.

Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Rewrite using `[e]`. Conclude with `Module.Flat.lTensor_preserves_injective_linearMap g hg`.
-/
theorem lvFil_tensor_injective {N₁ N₂ : Type} [AddCommGroup N₁] [Module Qp N₁] [AddCommGroup N₂] [Module Qp N₂]
    (g : N₁ →ₗ[Qp] N₂) (hg : Function.Injective g) :
    Function.Injective (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) g) := by
  have e : ⇑(AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) g) = ⇑(g.lTensor V) := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [e]
  exact Module.Flat.lTensor_preserves_injective_linearMap g hg

/- English proof (translation)
Unfold `ιV`. Conclude with `lvFil_tensor_injective (PD.ι.toLinearMap.restrictScalars Qp) PD.ι_inj`.
-/
theorem lvFil_ιV_injective : Function.Injective (ιV PD (LL := LL) (V := V)) := by
  unfold ιV
  exact lvFil_tensor_injective (PD.ι.toLinearMap.restrictScalars Qp) PD.ι_inj

/- English proof (translation)
Unfold `φVB`. Conclude with `lvFil_tensor_injective PD.φ.toLinearMap PD.φ_inj`.
-/
theorem lvFil_φVB_injective : Function.Injective (φVB PD (LL := LL) (V := V)) := by
  unfold φVB
  exact lvFil_tensor_injective PD.φ.toLinearMap PD.φ_inj

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b => simp [φVB, actVB, PD.φ_comm]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem lvFil_φ_act (ρ : Representation LL G V) (g : G) (x : V ⊗[Qp] B) :
    φVB PD (LL := LL) (V := V) (actVB PD ρ g x) = actVB PD ρ g (φVB PD (LL := LL) (V := V) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [φVB, actVB, PD.φ_comm]
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
Simplify using `only [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hx ⊢`. Introduce `g`. Rewrite using `[← lvFil_φ_act, hx g]`.
-/
theorem lvFil_φ_Dcris (ρ : Representation LL G V) {x : V ⊗[Qp] B} (hx : x ∈ Dcris PD ρ) :
    φVB PD (LL := LL) (V := V) x ∈ Dcris PD ρ := by
  simp only [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero] at hx ⊢
  intro g
  rw [← lvFil_φ_act, hx g]

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b => simp [φVB, mulVB, PD.φ_K₀]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem lvFil_φ_mul (c : K₀) (x : V ⊗[Qp] B) :
    φVB PD (LL := LL) (V := V) (mulVB (LL := LL) (V := V) (B := B) c x) = mulVB (LL := LL) (V := V) (B := B) (PD.σ c) (φVB PD (LL := LL) (V := V) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [φVB, mulVB, PD.φ_K₀]
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, zero_mem _⟩`. Consider the case `tmul v b`. Take `⟨a, ha⟩` from `PD.Fil_exh b`. Conclude with `⟨a, ⟨v ⊗ₜ ⟨b, ha⟩, by simp⟩⟩`.

Consider the case `add x y hx hy`. Take `⟨a, ha⟩` from `hx`. Take `⟨b, hb⟩` from `hy`. Conclude with `⟨min a b, add_mem (lvFil_FilV_anti PD (min_le_left a b) ha) (lvFil_FilV_anti PD (min_le_right a b) hb)⟩`.
-/
theorem lvFil_FilV_exh (y : V ⊗[Qp] BdR) : ∃ a, y ∈ FilV PD (LL := LL) (V := V) a := by
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, zero_mem _⟩
  | tmul v b =>
    obtain ⟨a, ha⟩ := PD.Fil_exh b
    exact ⟨a, ⟨v ⊗ₜ ⟨b, ha⟩, by simp⟩⟩
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨min a b, add_mem (lvFil_FilV_anti PD (min_le_left a b) ha)
      (lvFil_FilV_anti PD (min_le_right a b) hb)⟩

/- English proof (translation)
Set `bV` to `Module.Free.chooseBasis Qp V`. Set `e` to `TensorProduct.equivFinsuppOfBasisLeft (N := BdR) bV`. Establish `hc : ∀ a, ∀ z ∈ FilV PD (LL` using `LL) (V := V) a, ∀ i, e z i ∈ PD.Fil a := by`. Introduce `a z hz i`. Take `⟨t, rfl⟩` from `hz`.

Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul v f`. Simplify using `only [AlgebraTensorModule.map_tmul, LinearMap.id_apply, Submodule.subtype_apply, e, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]`. Conclude with `(PD.Fil a).smul_of_tower_mem _ f.2`.

Consider the case `add x y hx hy`. Rewrite using `[map_add, map_add, Finsupp.add_apply]`. Conclude with `add_mem hx hy`. Establish `h0 : e y = 0`. Use extensionality with `i`.

Conclude with `PD.Fil_sep _ (fun a => hc a y (hy a) i)`. Conclude with `e.injective (by rw [h0, map_zero])`.
-/
theorem lvFil_FilV_sep (y : V ⊗[Qp] BdR) (hy : ∀ a, y ∈ FilV PD (LL := LL) (V := V) a) : y = 0 := by
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
Set `S : ℤ → Submodule LL ℓ` to `fun a => (FilV PD (LL := LL) (V := V) a).comap ((ιV PD (LL := LL) (V := V)).comp ℓ.subtype)`. Establish `hS : Antitone S` using `fun a b h => Submodule.comap_mono (lvFil_FilV_anti PD h)`. Take `⟨k0, hk0⟩` from `(monotone_stabilizes_iff_noetherian.mpr inferInstance) (⟨fun k : ℕ => S (-(k : ℤ)), fun i j h => hS (by simp only [neg_le_neg_iff]; exact_mod_cast h)⟩ : ℕ →o Submodule LL ℓ)`. Use `⟨-(k0 : ℤ), fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨a, ha⟩` from `lvFil_FilV_exh PD (LL := LL) (ιV PD (LL := LL) (V := V) x)`.

Establish `h1 : (⟨x, hx⟩ : ℓ) ∈ S a` using `ha`. Establish `h2 : S a ≤ S (-((k0 + (-a).toNat : ℕ) : ℤ))` using `hS (by push_cast; omega)`. Establish `h3 : S (-(k0 : ℤ)) = S (-((k0 + (-a).toNat : ℕ) : ℤ))` using `hk0 (k0 + (-a).toNat) (by omega)`. Rewrite `h2` using `[← h3]`. Conclude with `h2 h1`.
-/
theorem lvFil_exh_sub (ℓ : Submodule LL (V ⊗[Qp] B)) [FiniteDimensional LL ℓ] :
    ∃ lo : ℤ, ∀ x ∈ ℓ, ιV PD (LL := LL) (V := V) x ∈ FilV PD (LL := LL) (V := V) lo := by
  let S : ℤ → Submodule LL ℓ := fun a => (FilV PD (LL := LL) (V := V) a).comap ((ιV PD (LL := LL) (V := V)).comp ℓ.subtype)
  have hS : Antitone S := fun a b h => Submodule.comap_mono (lvFil_FilV_anti PD h)
  obtain ⟨k0, hk0⟩ := (monotone_stabilizes_iff_noetherian.mpr inferInstance)
    (⟨fun k : ℕ => S (-(k : ℤ)), fun i j h => hS (by simp only [neg_le_neg_iff]; exact_mod_cast h)⟩ :
      ℕ →o Submodule LL ℓ)
  refine ⟨-(k0 : ℤ), fun x hx => ?_⟩
  obtain ⟨a, ha⟩ := lvFil_FilV_exh PD (LL := LL) (ιV PD (LL := LL) (V := V) x)
  have h1 : (⟨x, hx⟩ : ℓ) ∈ S a := ha
  have h2 : S a ≤ S (-((k0 + (-a).toNat : ℕ) : ℤ)) := hS (by push_cast; omega)
  have h3 : S (-(k0 : ℤ)) = S (-((k0 + (-a).toNat : ℕ) : ℤ)) := hk0 (k0 + (-a).toNat) (by omega)
  rw [← h3] at h2
  exact h2 h1

/- English proof (translation)
Set `S : ℤ → Submodule LL ℓ` to `fun a => (FilV PD (LL := LL) (V := V) a).comap ((ιV PD (LL := LL) (V := V)).comp ℓ.subtype)`. Establish `hS : Antitone S` using `fun a b h => Submodule.comap_mono (lvFil_FilV_anti PD h)`. Take `⟨k0, hk0⟩` from `IsArtinian.monotone_stabilizes (⟨fun k : ℕ => OrderDual.toDual (S k), fun i j h => OrderDual.toDual_le_toDual.mpr (hS (by exact_mod_cast h))⟩ : ℕ →o (Submodule LL ℓ)ᵒᵈ)`. Use `⟨k0, fun x hx hxk => ?_⟩` and prove the remaining obligations. Establish `hall : ∀ a, ιV PD (LL` using `LL) (V := V) x ∈ FilV PD (LL := LL) (V := V) a := by`.

Introduce `a`. Establish `h1 : (⟨x, hx⟩ : ℓ) ∈ S k0` using `hxk`. Establish `h3 : OrderDual.toDual (S k0) = OrderDual.toDual (S ((k0 + a.toNat : ℕ) : ℤ))` using `hk0 (k0 + a.toNat) (by omega)`. Establish `h4 : S k0 = S ((k0 + a.toNat : ℕ) : ℤ)` using `OrderDual.toDual.injective h3`. Establish `h5 : S ((k0 + a.toNat : ℕ) : ℤ) ≤ S a` using `hS (by push_cast; omega)`.

Conclude with `h5 (h4 ▸ h1)`. Conclude with `lvFil_ιV_injective PD (by rw [map_zero]; exact lvFil_FilV_sep PD _ hall)`.
-/
theorem lvFil_sep_sub (ℓ : Submodule LL (V ⊗[Qp] B)) [FiniteDimensional LL ℓ] :
    ∃ hi : ℤ, ∀ x ∈ ℓ, ιV PD (LL := LL) (V := V) x ∈ FilV PD (LL := LL) (V := V) hi → x = 0 := by
  let S : ℤ → Submodule LL ℓ := fun a => (FilV PD (LL := LL) (V := V) a).comap ((ιV PD (LL := LL) (V := V)).comp ℓ.subtype)
  have hS : Antitone S := fun a b h => Submodule.comap_mono (lvFil_FilV_anti PD h)
  obtain ⟨k0, hk0⟩ := IsArtinian.monotone_stabilizes
    (⟨fun k : ℕ => OrderDual.toDual (S k), fun i j h => OrderDual.toDual_le_toDual.mpr
      (hS (by exact_mod_cast h))⟩ : ℕ →o (Submodule LL ℓ)ᵒᵈ)
  refine ⟨k0, fun x hx hxk => ?_⟩
  have hall : ∀ a, ιV PD (LL := LL) (V := V) x ∈ FilV PD (LL := LL) (V := V) a := by
    intro a
    have h1 : (⟨x, hx⟩ : ℓ) ∈ S k0 := hxk
    have h3 : OrderDual.toDual (S k0) = OrderDual.toDual (S ((k0 + a.toNat : ℕ) : ℤ)) :=
      hk0 (k0 + a.toNat) (by omega)
    have h4 : S k0 = S ((k0 + a.toNat : ℕ) : ℤ) := OrderDual.toDual.injective h3
    have h5 : S ((k0 + a.toNat : ℕ) : ℤ) ≤ S a := hS (by push_cast; omega)
    exact h5 (h4 ▸ h1)
  exact lvFil_ιV_injective PD (by rw [map_zero]; exact lvFil_FilV_sep PD _ hall)

/- English proof (translation)
Use `PD.finK₀` as an intermediate fact. Distinguish the cases in `hV : Module.finrank LL V = 0`. Establish `: Subsingleton V` using `Module.finrank_zero_iff.mp hV`. Establish `hz : ∀ x : V ⊗[Qp] B, x = 0` using `fun x => by`. Proceed by induction on `x using TensorProduct.induction_on with`.

Consider the case `zero => rfl`. Consider the case `tmul a b => rw [Subsingleton.elim a 0, zero_tmul]`. Consider the case `add x y hx hy => rw [hx, hy, add_zero]`. Establish `: Subsingleton ↥(Dcris PD ρ)` using `⟨fun x y => Subtype.ext (by rw [hz x, hz y])⟩`. Use `infer_instance`.

Apply `Module.finite_of_finrank_pos` to reduce the goal to its premises. Rewrite using `[h]`. Conclude with `Nat.mul_pos Module.finrank_pos (Nat.pos_of_ne_zero hV)`.
-/
theorem lvFil_fin_of_isCrys (ρ : Representation LL G V) [FiniteDimensional LL V] (h : IsCrys PD ρ) :
    FiniteDimensional LL ↥(Dcris PD ρ) := by
  have := PD.finK₀
  by_cases hV : Module.finrank LL V = 0
  · have : Subsingleton V := Module.finrank_zero_iff.mp hV
    have hz : ∀ x : V ⊗[Qp] B, x = 0 := fun x => by
      induction x using TensorProduct.induction_on with
      | zero => rfl
      | tmul a b => rw [Subsingleton.elim a 0, zero_tmul]
      | add x y hx hy => rw [hx, hy, add_zero]
    have : Subsingleton ↥(Dcris PD ρ) := ⟨fun x y => Subtype.ext (by rw [hz x, hz y])⟩
    infer_instance
  · apply Module.finite_of_finrank_pos
    rw [h]
    exact Nat.mul_pos Module.finrank_pos (Nat.pos_of_ne_zero hV)

end Period

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n]
    {W : LocWach PD LL O v n} {T : LocLat G Qp LL O} {c : ZMod n}

/- English proof (translation)
Introduce `s a b hab`. Unfold `FilD FilLev`. Conclude with `Submodule.comap_mono (Submodule.map_mono (Submodule.map_mono (inf_le_inf_right _ (lvFil_FilCris_anti PD T.ρ hab))))`.
-/
theorem filAnti_holds : ∀ s, Antitone (FilD W T c s) := by
  intro s a b hab
  unfold FilD FilLev
  exact Submodule.comap_mono (Submodule.map_mono (Submodule.map_mono
    (inf_le_inf_right _ (lvFil_FilCris_anti PD T.ρ hab))))

/- English proof (translation)
Simplify using `only [DcrisL, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hx ⊢`. Use `⟨lvFil_φ_Dcris PD T.ρ hx.1, fun c' => ?_⟩` and prove the remaining obligations. Take `⟨c₀, rfl⟩` from `PD.σ_bij.2 c'`. Rewrite using `[← lvFil_φ_mul, hx.2 c₀, map_smul, ← DFunLike.congr_fun (W.emb_σ i) c₀]`. Both sides reduce to the same expression.
-/
theorem lvFil_φ_letter (i : ZMod n) {x : T.V ⊗[Qp] B} (hx : x ∈ DcrisL PD T.ρ (W.emb i)) :
    φVB PD (LL := LL) (V := T.V) x ∈ DcrisL PD T.ρ (W.emb (i + 1)) := by
  simp only [DcrisL, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hx ⊢
  refine ⟨lvFil_φ_Dcris PD T.ρ hx.1, fun c' => ?_⟩
  obtain ⟨c₀, rfl⟩ := PD.σ_bij.2 c'
  rw [← lvFil_φ_mul, hx.2 c₀, map_smul, ← DFunLike.congr_fun (W.emb_σ i) c₀]
  rfl

/- English proof (translation)
Proceed by induction on `s with`. Consider the case `zero => simpa using hx`. Consider the case `succ s ih`. Establish `h` using `lvFil_φ_letter (W := W) (T := T) _ ih`. Rewrite using `[show i + ((s + 1 : ℕ) : ZMod n) = i + s + 1 by push_cast; ring, pow_succ']`.

Conclude with `h`.
-/
theorem lvFil_φpow_letter (i : ZMod n) (s : ℕ) {x : T.V ⊗[Qp] B} (hx : x ∈ DcrisL PD T.ρ (W.emb i)) :
    ((φVB PD (LL := LL) (V := T.V) : Module.End LL (T.V ⊗[Qp] B)) ^ s) x ∈ DcrisL PD T.ρ (W.emb (i + s)) := by
  induction s with
  | zero => simpa using hx
  | succ s ih =>
    have h := lvFil_φ_letter (W := W) (T := T) _ ih
    rw [show i + ((s + 1 : ℕ) : ZMod n) = i + s + 1 by push_cast; ring, pow_succ']
    exact h

/- English proof (translation)
The claim follows from `Module.Finite.of_injective (Submodule.inclusion (inf_le_left : DcrisL PD T.ρ (W.emb i) ≤ Dcris PD T.ρ)) (Submodule.inclusion_injective _)`.
-/
theorem lvFil_letter_fin (hfin : FiniteDimensional LL ↥(Dcris PD T.ρ)) (i : ZMod n) :
    FiniteDimensional LL ↥(DcrisL PD T.ρ (W.emb i)) :=
  Module.Finite.of_injective (Submodule.inclusion (inf_le_left : DcrisL PD T.ρ (W.emb i) ≤ Dcris PD T.ρ))
    (Submodule.inclusion_injective _)

/- English proof (translation)
Use `lvFil_letter_fin (W := W) hfin (i + 1)` as an intermediate fact. Use `LinearMap.finrank_le_finrank_of_injective (f := (φVB PD (LL := LL) (V := T.V)).restrict (fun x hx => lvFil_φ_letter (W := W) (T := T) i hx)) ?_` and prove the remaining obligations. Introduce `x y hxy`. Conclude with `Subtype.ext (lvFil_φVB_injective PD (congrArg Subtype.val hxy))`.
-/
theorem lvFil_finrank_step (hfin : FiniteDimensional LL ↥(Dcris PD T.ρ)) (i : ZMod n) :
    Module.finrank LL ↥(DcrisL PD T.ρ (W.emb i)) ≤ Module.finrank LL ↥(DcrisL PD T.ρ (W.emb (i + 1))) := by
  have := lvFil_letter_fin (W := W) hfin (i + 1)
  refine LinearMap.finrank_le_finrank_of_injective
    (f := (φVB PD (LL := LL) (V := T.V)).restrict (fun x hx => lvFil_φ_letter (W := W) (T := T) i hx)) ?_
  intro x y hxy
  exact Subtype.ext (lvFil_φVB_injective PD (congrArg Subtype.val hxy))

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => rw [show i + ((0 : ℕ) : ZMod n) = i by simp]`. Consider the case `succ k ih`. Establish `h` using `lvFil_finrank_step (W := W) hfin (i + k)`. Rewrite `h` using `[show i + (k : ZMod n) + 1 = i + ((k + 1 : ℕ) : ZMod n) by push_cast; ring]`.

Conclude with `ih.trans h`.
-/
theorem lvFil_finrank_le (hfin : FiniteDimensional LL ↥(Dcris PD T.ρ)) (i : ZMod n) (k : ℕ) :
    Module.finrank LL ↥(DcrisL PD T.ρ (W.emb i)) ≤ Module.finrank LL ↥(DcrisL PD T.ρ (W.emb (i + k))) := by
  induction k with
  | zero => rw [show i + ((0 : ℕ) : ZMod n) = i by simp]
  | succ k ih =>
    have h := lvFil_finrank_step (W := W) hfin (i + k)
    rw [show i + (k : ZMod n) + 1 = i + ((k + 1 : ℕ) : ZMod n) by push_cast; ring] at h
    exact ih.trans h

/- English proof (translation)
Apply `le_antisymm _ (lvFil_finrank_le hfin i k)` to reduce the goal to its premises. Establish `h` using `lvFil_finrank_le (W := W) hfin (i + k) (n * k - k)`. Establish `hn : 1 ≤ n` using `NeZero.one_le`. Establish `e : i + (k : ZMod n) + ((n * k - k : ℕ) : ZMod n) = i`. Rewrite using `[Nat.cast_sub (Nat.le_mul_of_pos_left k hn), Nat.cast_mul, ZMod.natCast_self]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite `h` using `[e]`. Then use the resulting hypothesis.
-/
theorem lvFil_finrank_eq (hfin : FiniteDimensional LL ↥(Dcris PD T.ρ)) (i : ZMod n) (k : ℕ) :
    Module.finrank LL ↥(DcrisL PD T.ρ (W.emb (i + k))) = Module.finrank LL ↥(DcrisL PD T.ρ (W.emb i)) := by
  apply le_antisymm _ (lvFil_finrank_le hfin i k)
  have h := lvFil_finrank_le (W := W) hfin (i + k) (n * k - k)
  have hn : 1 ≤ n := NeZero.one_le
  have e : i + (k : ZMod n) + ((n * k - k : ℕ) : ZMod n) = i := by
    rw [Nat.cast_sub (Nat.le_mul_of_pos_left k hn), Nat.cast_mul, ZMod.natCast_self]
    ring
  rwa [e] at h

/- English proof (translation)
Establish `h1` using `lvFil_letter_fin (W := W) hfin (c - s)`. Establish `h2` using `lvFil_letter_fin (W := W) hfin c`. Establish `hmap : ∀ x ∈ DcrisL PD T.ρ (W.emb (c - s)), ((φVB PD (LL` using `LL) (V := T.V) : Module.End LL (T.V ⊗[Qp] B)) ^ s) x ∈ DcrisL PD T.ρ (W.emb c) := by`. Introduce `x hx`. Use `lvFil_φpow_letter (W := W) (T := T) (c - s) s hx` as an intermediate fact.

Rewrite `this` using `[sub_add_cancel]`. Then use the resulting hypothesis. Set `f` to `((φVB PD (LL := LL) (V := T.V) : Module.End LL (T.V ⊗[Qp] B)) ^ s).restrict hmap`. Establish `hinj : Function.Injective f`. Introduce `x x' hxx`. Apply `Subtype.ext` to reduce the goal to its premises.

Establish `hi : Function.Injective ⇑((φVB PD (LL` using `LL) (V := T.V) : Module.End LL (T.V ⊗[Qp] B)) ^ s) := by`. Rewrite using `[Module.End.coe_pow]`. Conclude with `(lvFil_φVB_injective PD).iterate s`. Conclude with `hi (congrArg Subtype.val hxx)`. Establish `hrk : Module.finrank LL ↥(DcrisL PD T.ρ (W.emb (c - s))) = Module.finrank LL ↥(DcrisL PD T.ρ (W.emb c))`.

Use `lvFil_finrank_eq (W := W) hfin (c - s) s` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Conclude with `this.symm`. Take `⟨x, hx⟩` from `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrk).mp hinj ⟨y, hy⟩`. Conclude with `⟨x, x.2, congrArg Subtype.val hx⟩`.
-/
theorem lvFil_φpow_surj (hfin : FiniteDimensional LL ↥(Dcris PD T.ρ)) (s : ℕ) (y : T.V ⊗[Qp] B)
    (hy : y ∈ DcrisL PD T.ρ (W.emb c)) :
    ∃ x ∈ DcrisL PD T.ρ (W.emb (c - s)), ((φVB PD (LL := LL) (V := T.V) : Module.End LL (T.V ⊗[Qp] B)) ^ s) x = y := by
  have h1 := lvFil_letter_fin (W := W) hfin (c - s)
  have h2 := lvFil_letter_fin (W := W) hfin c
  have hmap : ∀ x ∈ DcrisL PD T.ρ (W.emb (c - s)),
      ((φVB PD (LL := LL) (V := T.V) : Module.End LL (T.V ⊗[Qp] B)) ^ s) x ∈ DcrisL PD T.ρ (W.emb c) := by
    intro x hx
    have := lvFil_φpow_letter (W := W) (T := T) (c - s) s hx
    rwa [sub_add_cancel] at this
  let f := ((φVB PD (LL := LL) (V := T.V) : Module.End LL (T.V ⊗[Qp] B)) ^ s).restrict hmap
  have hinj : Function.Injective f := by
    intro x x' hxx
    apply Subtype.ext
    have hi : Function.Injective ⇑((φVB PD (LL := LL) (V := T.V) : Module.End LL (T.V ⊗[Qp] B)) ^ s) := by
      rw [Module.End.coe_pow]; exact (lvFil_φVB_injective PD).iterate s
    exact hi (congrArg Subtype.val hxx)
  have hrk : Module.finrank LL ↥(DcrisL PD T.ρ (W.emb (c - s))) = Module.finrank LL ↥(DcrisL PD T.ρ (W.emb c)) := by
    have := lvFil_finrank_eq (W := W) hfin (c - s) s
    rw [sub_add_cancel] at this
    exact this.symm
  obtain ⟨x, hx⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrk).mp hinj ⟨y, hy⟩
  exact ⟨x, x.2, congrArg Subtype.val hx⟩

/- English proof (translation)
Introduce `s _`. Establish `h1` using `lvFil_letter_fin (W := W) hfin (c - s)`. Take `⟨lo, hlo⟩` from `lvFil_exh_sub PD (DcrisL PD T.ρ (W.emb (c - s)))`. Take `⟨hi, hhi⟩` from `lvFil_sep_sub PD (DcrisL PD T.ρ (W.emb (c - s)))`. Use `⟨filAnti_holds s, ⟨lo, ?_⟩, ⟨hi, ?_⟩⟩` and prove the remaining obligations.

Rewrite using `[eq_top_iff]`. Introduce and unpack `⟨d, hd⟩ -`. Take `⟨y, hy, rfl⟩` from `lvFil_φpow_surj (W := W) hfin s d hd`. Simplify using `only [FilD, FilLev, Submodule.mem_comap, LinearMap.comp_apply, Submodule.subtype_apply]`. Conclude with `Submodule.mem_map_of_mem (Submodule.mem_map_of_mem (Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨(Submodule.mem_inf.mp hy).1, hlo y hy⟩, hy⟩))`.

Rewrite using `[eq_bot_iff]`. Introduce and unpack `⟨d, hd⟩ hdF`. Simplify using `only [FilD, FilLev, Submodule.mem_comap, LinearMap.comp_apply, Submodule.subtype_apply, Submodule.mem_map, Submodule.mem_inf, FilCris] at hdF`. Take `⟨w, ⟨y, ⟨⟨-, hyF⟩, hyl⟩, rfl⟩, hw⟩` from `hdF`. Establish `hy0 : y = 0` using `hhi y hyl hyF`.

Substitute `hy0` using the available equality. Establish `hd0 : d = 0` using `lvFil_ιV_injective PD (by rw [← hw]; simp)`. Substitute `hd0` using the available equality. Conclude with `(Submodule.mem_bot LL).mpr rfl`.
-/
theorem filt_holds (ell : ℕ) (hfin : FiniteDimensional LL ↥(Dcris PD T.ρ)) :
    ∀ s < ell, IsFilt (FilD W T c s) := by
  intro s _
  have h1 := lvFil_letter_fin (W := W) hfin (c - s)
  obtain ⟨lo, hlo⟩ := lvFil_exh_sub PD (DcrisL PD T.ρ (W.emb (c - s)))
  obtain ⟨hi, hhi⟩ := lvFil_sep_sub PD (DcrisL PD T.ρ (W.emb (c - s)))
  refine ⟨filAnti_holds s, ⟨lo, ?_⟩, ⟨hi, ?_⟩⟩
  · rw [eq_top_iff]
    rintro ⟨d, hd⟩ -
    obtain ⟨y, hy, rfl⟩ := lvFil_φpow_surj (W := W) hfin s d hd
    simp only [FilD, FilLev, Submodule.mem_comap, LinearMap.comp_apply, Submodule.subtype_apply]
    exact Submodule.mem_map_of_mem (Submodule.mem_map_of_mem
      (Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨(Submodule.mem_inf.mp hy).1, hlo y hy⟩, hy⟩))
  · rw [eq_bot_iff]
    rintro ⟨d, hd⟩ hdF
    simp only [FilD, FilLev, Submodule.mem_comap, LinearMap.comp_apply, Submodule.subtype_apply,
      Submodule.mem_map, Submodule.mem_inf, FilCris] at hdF
    obtain ⟨w, ⟨y, ⟨⟨-, hyF⟩, hyl⟩, rfl⟩, hw⟩ := hdF
    have hy0 : y = 0 := hhi y hyl hyF
    subst hy0
    have hd0 : d = 0 := lvFil_ιV_injective PD (by rw [← hw]; simp)
    subst hd0
    exact (Submodule.mem_bot LL).mpr rfl

end Formalism.MainNotions.N.Ln03.Pf
