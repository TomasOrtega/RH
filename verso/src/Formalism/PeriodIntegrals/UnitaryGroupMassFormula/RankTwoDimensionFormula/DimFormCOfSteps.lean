import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.GammaOneEqProd

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp
  Formalism.L2.SG.Full Formalism.MainNotions.S.Cnt

namespace PI.UnitaryDimensionFormula

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def latS {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (h : X.B.I.Gf) : Set (VS D).V :=
  {y | (X.B.I.fmat (h * X.xu u)⁻¹).mulVec (incl X.B.I (X.crd y)) ∈ X.B.I.Lf}

/- English proof (translation)
Use extensionality with `y`. Conclude with `cs.lat_eq ρ y`.
-/
theorem lamOf_eq_latS {D : D7} {X : HidaSetting D} {u : D.what₂.Word}
    {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (cs : ColSys X u what₂) (ρ : cs.Cl) :
    ((cs.lamOf ρ : Submodule (𝓞 D.host.E) (VS D).V) : Set (VS D).V) = latS X u (cs.h ρ : X.B.I.Gf) := by
  ext y
  exact cs.lat_eq ρ y

def OrbitCount : Prop :=
  ∀ (G : Type) [Group G] (Γ K : Subgroup G) (n : ℕ) (t : Fin n → G) (A : Set G) (N : ℕ),
    A.Finite → Nat.card A ≤ N →
    (∀ i j, (t i)⁻¹ * t j ∈ K → i = j) →
    (∀ i j, ∀ γ ∈ Γ, ∀ κ ∈ K, t j = γ * t i * κ → γ ∈ A) →
    n ≤ N * Nat.card (Set.range fun i => DoubleCoset.mk Γ K (t i))

def Transport : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (γ : Gam X u), ∃ g ∈ stabF D (X.Fu u),
    ∀ h : X.B.I.Gf, latS X u ((iotaF X u γ : X.B.I.Gf) * h) = g '' latS X u h

def KuStab : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter) (h : X.B.I.Gf) (κ : Ku X u hK),
    latS X u (h * ((κ : Hfin X u) : X.B.I.Gf)) = latS X u h

def StabBound : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Formalism.L2.SG.RowsConc.ConcTie X Y →
    ∀ Λ ∈ Y.what₂ u, (autLz D (X.Fu u) Λ).Finite →
      ∃ A : Set (Hfin X u), A.Finite ∧ Nat.card A ≤ Nat.card (autLz D (X.Fu u) Λ) ∧
        ∀ h h' : Hfin X u, latS X u (h : X.B.I.Gf) = (Λ : Set (VS D).V) →
          latS X u (h' : X.B.I.Gf) = (Λ : Set (VS D).V) →
          ∀ γ ∈ (iotaF X u).range, ∀ κ ∈ Ku X u Y.hK, h' = γ * h * κ → γ ∈ A

def IndexGe : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Formalism.L2.SG.RowsConc.ConcTie X Y →
    ∀ Λ ∈ Y.what₂ u, ∃ (n : ℕ) (t : Fin n → Hfin X u), Gam1 Y.TR ≤ (n : ℝ) ∧
      (∀ i, latS X u (t i : X.B.I.Gf) = (Λ : Set (VS D).V)) ∧
      ∀ i j, (t i)⁻¹ * t j ∈ Ku X u Y.hK → i = j

/- English proof (translation)
Take `⟨ρ, ⟨γ, κ, hρ⟩, -⟩` from `Y.colReps u h`. Use `⟨ρ, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [fib]`. Establish `h1 : latS X u (h : X.B.I.Gf) = latS X u ((iotaF X u γ : X.B.I.Gf) * ((Y.cs u).h ρ : X.B.I.Gf))`. Rewrite using `[hρ, Subgroup.coe_mul, hS D X u Y.hK _ κ, Subgroup.coe_mul]`.

Take `⟨g, hg, hgt⟩` from `hT D X u γ`. Establish `h2 : (Λ : Set (VS D).V) = g '' ((((Y.cs u).lamOf ρ) : Submodule (𝓞 D.host.E) (VS D).V) : Set (VS D).V)`. Rewrite using `[← hh, h1, hgt, lamOf_eq_latS]`. Establish `hR` using `Y.rowsOK u`. Unfold `IsRowReps at hR`.

Take `⟨hRl, hU⟩` from `hR`. Take `⟨Λ0, -, huniq⟩` from `hU Λ (hRl Λ hΛ)`. Establish `e1 : Λ = Λ0` using `huniq Λ ⟨hΛ, 1, by simp [stabF], by ext; simp [Formalism.HermitianLatticesTheory.gmap]⟩`. Establish `e2 : (Y.cs u).lamOf ρ = Λ0`. Use `huniq _ ⟨(Y.cs u).lam_mem ρ, g, hg, ?_⟩` and prove the remaining obligations.

Apply `SetLike.coe_injective` to reduce the goal to its premises. Rewrite using `[h2]`. Simplify using `[Formalism.HermitianLatticesTheory.gmap]`. Simplify using `using e2.trans e1.symm`. Conclude with `((DoubleCoset.eq _ _ _ _).mpr ⟨iotaF X u γ, MonoidHom.mem_range.mpr ⟨γ, rfl⟩, κ, κ.2, hρ⟩).symm`.
-/
theorem fibreCover (hT : Transport) (hS : KuStab) {D : D7} {X : HidaSetting D} (Y : Full X) (u : D.what₂.Word)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : Λ ∈ Y.what₂ u) (h : Hfin X u)
    (hh : latS X u (h : X.B.I.Gf) = (Λ : Set (VS D).V)) :
    ∃ ρ ∈ fib (Y.cs u) Λ, DoubleCoset.mk (iotaF X u).range (Ku X u Y.hK) h =
      DoubleCoset.mk (iotaF X u).range (Ku X u Y.hK) ((Y.cs u).h ρ) := by
  obtain ⟨ρ, ⟨γ, κ, hρ⟩, -⟩ := Y.colReps u h
  refine ⟨ρ, ?_, ?_⟩
  · simp only [fib]
    have h1 : latS X u (h : X.B.I.Gf) =
        latS X u ((iotaF X u γ : X.B.I.Gf) * ((Y.cs u).h ρ : X.B.I.Gf)) := by
      rw [hρ, Subgroup.coe_mul, hS D X u Y.hK _ κ, Subgroup.coe_mul]
    obtain ⟨g, hg, hgt⟩ := hT D X u γ
    have h2 : (Λ : Set (VS D).V) = g '' ((((Y.cs u).lamOf ρ) : Submodule (𝓞 D.host.E) (VS D).V) : Set (VS D).V) := by
      rw [← hh, h1, hgt, lamOf_eq_latS]
    have hR := Y.rowsOK u
    unfold IsRowReps at hR
    obtain ⟨hRl, hU⟩ := hR
    obtain ⟨Λ0, -, huniq⟩ := hU Λ (hRl Λ hΛ)
    have e1 : Λ = Λ0 := huniq Λ ⟨hΛ, 1, by simp [stabF], by ext; simp [Formalism.HermitianLatticesTheory.gmap]⟩
    have e2 : (Y.cs u).lamOf ρ = Λ0 := by
      refine huniq _ ⟨(Y.cs u).lam_mem ρ, g, hg, ?_⟩
      apply SetLike.coe_injective
      rw [h2]
      simp [Formalism.HermitianLatticesTheory.gmap]
    simpa using e2.trans e1.symm
  · exact ((DoubleCoset.eq _ _ _ _).mpr ⟨iotaF X u γ, MonoidHom.mem_range.mpr ⟨γ, rfl⟩, κ, κ.2, hρ⟩).symm

/- English proof (translation)
Introduce `D X Y u hC Λ hΛ`. Take `⟨n, t, hn, ht, hd⟩` from `hI D X Y u hC Λ hΛ`. Unfold `wRow`. Distinguish the cases in `hN0 : Nat.card (autLz D (X.Fu u) Λ) = 0`. Simplify using `[hN0]`.

Establish `hfin : (autLz D (X.Fu u) Λ).Finite` using `Set.finite_coe_iff.mp (Nat.finite_of_card_ne_zero hN0)`. Take `⟨A, hAf, hAc, hA⟩` from `hB D X Y u hC Λ hΛ hfin`. Establish `horb` using `hO (Hfin X u) (iotaF X u).range (Ku X u Y.hK) n t A _ hAf hAc hd (fun i j γ hγ κ hκ he => hA (t i) (t j) (ht i) (ht j) γ hγ κ hκ he)`. Establish `hsub : Set.range (fun i => DoubleCoset.mk (iotaF X u).range (Ku X u Y.hK) (t i)) ⊆ (((fib (Y.cs u) Λ).image (fun ρ => DoubleCoset.mk (iotaF X u).range (Ku X u Y.hK) ((Y.cs u).h ρ)) : Finset _) : Set _)`. Introduce and unpack `_ ⟨i, rfl⟩`.

Take `⟨ρ, hρ, he⟩` from `fibreCover hT hS Y u Λ hΛ (t i) (ht i)`. Conclude with `Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨ρ, hρ, he.symm⟩)`. Establish `hc : Nat.card (Set.range (fun i => DoubleCoset.mk (iotaF X u).range (Ku X u Y.hK) (t i))) ≤ (fib (Y.cs u) Λ).card`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Nat.card_coe_set_eq, Set.ncard_coe_finset]`.

Use `_ ≤ _ := Finset.card_image_le`. Establish `hNpos : (0 : ℝ) < (Nat.card (autLz D (X.Fu u) Λ) : ℝ)`. Conclude with `Nat.pos_of_ne_zero hN0` after adjusting the coercions. Establish `key : (n : ℝ) ≤ (Nat.card (autLz D (X.Fu u) Λ) : ℝ) * ((fib (Y.cs u) Λ).card : ℝ)`. Conclude with `horb.trans (Nat.mul_le_mul_left _ hc)` after adjusting the coercions.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← div_eq_mul_inv, div_le_iff₀ hNpos]`. Combine the linear relations using `[key]`.
-/
theorem fibreBound_of (hO : OrbitCount) (hT : Transport) (hS : KuStab) (hB : StabBound) (hI : IndexGe) :
    FibreBound := by
  intro D X Y u hC Λ hΛ
  obtain ⟨n, t, hn, ht, hd⟩ := hI D X Y u hC Λ hΛ
  unfold wRow
  by_cases hN0 : Nat.card (autLz D (X.Fu u) Λ) = 0
  · simp [hN0]
  have hfin : (autLz D (X.Fu u) Λ).Finite :=
    Set.finite_coe_iff.mp (Nat.finite_of_card_ne_zero hN0)
  obtain ⟨A, hAf, hAc, hA⟩ := hB D X Y u hC Λ hΛ hfin
  have horb := hO (Hfin X u) (iotaF X u).range (Ku X u Y.hK) n t A _ hAf hAc hd
    (fun i j γ hγ κ hκ he => hA (t i) (t j) (ht i) (ht j) γ hγ κ hκ he)
  have hsub : Set.range (fun i => DoubleCoset.mk (iotaF X u).range (Ku X u Y.hK) (t i)) ⊆
      (((fib (Y.cs u) Λ).image
        (fun ρ => DoubleCoset.mk (iotaF X u).range (Ku X u Y.hK) ((Y.cs u).h ρ)) : Finset _) : Set _) := by
    rintro _ ⟨i, rfl⟩
    obtain ⟨ρ, hρ, he⟩ := fibreCover hT hS Y u Λ hΛ (t i) (ht i)
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨ρ, hρ, he.symm⟩)
  have hc : Nat.card (Set.range (fun i => DoubleCoset.mk (iotaF X u).range (Ku X u Y.hK) (t i))) ≤
      (fib (Y.cs u) Λ).card := by
    calc _ ≤ Nat.card (((fib (Y.cs u) Λ).image
          (fun ρ => DoubleCoset.mk (iotaF X u).range (Ku X u Y.hK) ((Y.cs u).h ρ)) : Finset _) : Set _) :=
          Nat.card_mono (Finset.finite_toSet _) hsub
      _ = ((fib (Y.cs u) Λ).image
          (fun ρ => DoubleCoset.mk (iotaF X u).range (Ku X u Y.hK) ((Y.cs u).h ρ))).card := by
          rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]
      _ ≤ _ := Finset.card_image_le
  have hNpos : (0 : ℝ) < (Nat.card (autLz D (X.Fu u) Λ) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hN0
  have key : (n : ℝ) ≤ (Nat.card (autLz D (X.Fu u) Λ) : ℝ) * ((fib (Y.cs u) Λ).card : ℝ) := by
    exact_mod_cast horb.trans (Nat.mul_le_mul_left _ hc)
  calc Gam1 Y.TR * ((Nat.card (autLz D (X.Fu u) Λ) : ℝ))⁻¹
      ≤ (n : ℝ) * ((Nat.card (autLz D (X.Fu u) Λ) : ℝ))⁻¹ :=
        mul_le_mul_of_nonneg_right hn (inv_nonneg.mpr hNpos.le)
    _ ≤ ((fib (Y.cs u) Λ).card : ℝ) := by
        rw [← div_eq_mul_inv, div_le_iff₀ hNpos]
        linarith [key]

/- English proof (translation)
The claim follows from `dimFormC_of (fibreBound_of hO hT hS hB hI)`.
-/
theorem dimFormC_of_steps (hO : OrbitCount) (hT : Transport) (hS : KuStab) (hB : StabBound) (hI : IndexGe) :
    Formalism.L2.SG.KappaOffDiagonal.DimFormC :=
  dimFormC_of (fibreBound_of hO hT hS hB hI)

end PI.UnitaryDimensionFormula
