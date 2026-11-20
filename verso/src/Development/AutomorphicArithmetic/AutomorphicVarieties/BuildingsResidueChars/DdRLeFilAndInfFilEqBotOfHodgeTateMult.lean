import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteCohomology
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Formalism.SharpRestriction.LevelLetterCocycles.JsetEmb
import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfJumpsBdd
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain TensorProduct Module GlobalTheory.WeilDeligne GlobalTheory.Pst Polynomial

section Gen

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

/- English proof (translation)
Rewrite using `[JsetEmb.de_rham_filtration_eq_iSup_embeddings PD hcard ρ (c + 1), JsetEmb.de_rham_filtration_eq_iSup_embeddings PD hcard ρ c]`. Use `iSup_congr fun τ => ?_` and prove the remaining obligations. Establish `hle : FildR PD ρ τ c ≤ DdR PD ρ` using `fun x hx => hx.1.1`. Establish `: FiniteDimensional LL ↥(FildR PD ρ τ c)` using `Submodule.finiteDimensional_of_le hle`. Establish `h0` using `h τ`.

Unfold `multV at h0`. Use `Submodule.eq_of_le_of_finrank_eq (Ln03.Pf.jb_FildR_anti PD ρ τ (by omega)) ?_` and prove the remaining obligations. Use linear arithmetic over natural numbers and integers.
-/
private theorem step_of_mult [CharZero Qp] (PD : PeriodData G Qp K₀ K B BdR)
    [Fintype (K →ₐ[Qp] LL)] (hcard : Fintype.card (K →ₐ[Qp] LL) = finrank Qp K)
    (ρ : Representation LL G V) (hfin : FiniteDimensional LL ↥(DdR PD ρ)) (c : ℤ)
    (h : ∀ τ : K →ₐ[Qp] LL, multV PD ρ τ c = 0) :
    DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) (c + 1) = DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) c := by
  rw [JsetEmb.de_rham_filtration_eq_iSup_embeddings PD hcard ρ (c + 1), JsetEmb.de_rham_filtration_eq_iSup_embeddings PD hcard ρ c]
  refine iSup_congr fun τ => ?_
  have hle : FildR PD ρ τ c ≤ DdR PD ρ := fun x hx => hx.1.1
  have : FiniteDimensional LL ↥(FildR PD ρ τ c) := Submodule.finiteDimensional_of_le hle
  have h0 := h τ
  unfold multV at h0
  refine Submodule.eq_of_le_of_finrank_eq (Ln03.Pf.jb_FildR_anti PD ρ τ (by omega)) ?_
  omega

/- English proof (translation)
Use `⟨fun a ha x hx => ?_, fun b hb => ?_⟩` and prove the remaining obligations. Take `⟨c, hc⟩` from `Ln03.Pf.jb_FilV_exh PD (LL := LL) (V := V) x`. Break down `le_total a c with h | h` into its components or cases. Conclude with `Ln03.Pf.jb_FilV_anti PD (LL := LL) (V := V) h hc`. Establish `key : ∀ d, c ≤ d → d ≤ a → x ∈ FilV PD (LL` using `LL) (V := V) d := by`.

Introduce `d hd`. Proceed by induction on `d, hd using Int.le_induction with`. Consider the case `base => exact fun _ => hc`. Consider the case `succ d hd ih`. Introduce `hda`.

Establish `hm : x ∈ DdR PD ρ ⊓ FilV PD (LL` using `LL) (V := V) d := ⟨hx, ih (by omega)⟩`. Rewrite `hm` using `[← step_of_mult PD hcard ρ hfin d fun τ => ha τ d (by omega)]`. Conclude with `hm.2`. Conclude with `key a h le_rfl`. Rewrite using `[eq_bot_iff]`.

Introduce `x hx`. Rewrite using `[Submodule.mem_bot]`. Use `Ln03.Pf.jb_FilV_sep PD (LL := LL) (V := V) x fun d => ?_` and prove the remaining obligations. Break down `le_total d (b + 1) with h | h` into its components or cases. Conclude with `Ln03.Pf.jb_FilV_anti PD (LL := LL) (V := V) h hx.2`.

Proceed by induction on `d, h using Int.le_induction with`. Consider the case `base => exact hx.2`. Consider the case `succ d hd ih`. Establish `hm : x ∈ DdR PD ρ ⊓ FilV PD (LL` using `LL) (V := V) d := ⟨hx.1, ih⟩`. Rewrite `hm` using `[← step_of_mult PD hcard ρ hfin d fun τ => hb τ d (by omega)]`.

Conclude with `hm.2`.
-/
private theorem gen_fil [CharZero Qp] (PD : PeriodData G Qp K₀ K B BdR)
    [Fintype (K →ₐ[Qp] LL)] (hcard : Fintype.card (K →ₐ[Qp] LL) = finrank Qp K)
    (ρ : Representation LL G V) (hfin : FiniteDimensional LL ↥(DdR PD ρ)) :
    (∀ a : ℤ, (∀ (τ : K →ₐ[Qp] LL) (c : ℤ), c < a → multV PD ρ τ c = 0) →
      DdR PD ρ ≤ FilV PD (LL := LL) (V := V) a) ∧
    ∀ b : ℤ, (∀ (τ : K →ₐ[Qp] LL) (c : ℤ), b < c → multV PD ρ τ c = 0) →
      DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) (b + 1) = ⊥ := by
  refine ⟨fun a ha x hx => ?_, fun b hb => ?_⟩
  · obtain ⟨c, hc⟩ := Ln03.Pf.jb_FilV_exh PD (LL := LL) (V := V) x
    rcases le_total a c with h | h
    · exact Ln03.Pf.jb_FilV_anti PD (LL := LL) (V := V) h hc
    · have key : ∀ d, c ≤ d → d ≤ a → x ∈ FilV PD (LL := LL) (V := V) d := by
        intro d hd
        induction d, hd using Int.le_induction with
        | base => exact fun _ => hc
        | succ d hd ih =>
          intro hda
          have hm : x ∈ DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) d := ⟨hx, ih (by omega)⟩
          rw [← step_of_mult PD hcard ρ hfin d fun τ => ha τ d (by omega)] at hm
          exact hm.2
      exact key a h le_rfl
  · rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_bot]
    refine Ln03.Pf.jb_FilV_sep PD (LL := LL) (V := V) x fun d => ?_
    rcases le_total d (b + 1) with h | h
    · exact Ln03.Pf.jb_FilV_anti PD (LL := LL) (V := V) h hx.2
    · induction d, h using Int.le_induction with
      | base => exact hx.2
      | succ d hd ih =>
        have hm : x ∈ DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) d := ⟨hx.1, ih⟩
        rw [← step_of_mult PD hcard ρ hfin d fun τ => hb τ d (by omega)] at hm
        exact hm.2

end Gen

/- English proof (translation)
Introduce `l _ P K LL key V _ _ _ _ _ ρ hfin`. Establish `: FiniteDimensional ℚ_[l] ↥LL.1` using `LL.2`. Establish `: FiniteDimensional ℚ_[l] ↥K.1` using `K.2`. Establish `hc : Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) = finrank ℚ_[l] ↥K.1`. Set `e : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) ≃ (↥K.1 →ₐ[ℚ_[l]] Om l)` to `{ toFun := fun f => LL.1.val.comp f invFun := fun g => g.codRestrict LL.1.toSubalgebra (key g) left_inv := fun f => by ext; rfl right_inv := fun g => by ext; rfl }`.

Rewrite using `[Nat.card_congr e]`. Conclude with `AlgHom.natCard_of_splits _ _ _ (fun _ => IsAlgClosed.splits _)`. Establish `: Finite (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)` using `Nat.finite_of_card_ne_zero (by rw [hc]; exact Module.finrank_pos.ne')`. Use `letI := Fintype.ofFinite (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)`. Conclude with `gen_fil (P.PD K) (by rw [Fintype.card_eq_nat_card, hc]) ρ hfin`.
-/
theorem UpperTheory.ddR_le_fil_and_inf_fil_eq_bot_of_hodgeTate_mult :
    ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K LL : FinExt l}, (∀ (τ : ↥K.1 →ₐ[ℚ_[l]] Om l) (x : ↥K.1), τ x ∈ LL.1) → ∀ {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), FiniteDimensional ↥LL.1 ↥(DdR (P.PD K) ρ) → (∀ a : ℤ, (∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (c : ℤ), c < a → multV (P.PD K) ρ τ c = 0) → DdR (P.PD K) ρ ≤ FilV (P.PD K) (LL := ↥LL.1) (V := V) a) ∧ ∀ b : ℤ, (∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (c : ℤ), b < c → multV (P.PD K) ρ τ c = 0) → DdR (P.PD K) ρ ⊓ FilV (P.PD K) (LL := ↥LL.1) (V := V) (b + 1) = ⊥ := by
  intro l _ P K LL key V _ _ _ _ _ ρ hfin
  have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  have hc : Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) = finrank ℚ_[l] ↥K.1 := by
    let e : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) ≃ (↥K.1 →ₐ[ℚ_[l]] Om l) :=
      { toFun := fun f => LL.1.val.comp f
        invFun := fun g => g.codRestrict LL.1.toSubalgebra (key g)
        left_inv := fun f => by ext; rfl
        right_inv := fun g => by ext; rfl }
    rw [Nat.card_congr e]
    exact AlgHom.natCard_of_splits _ _ _ (fun _ => IsAlgClosed.splits _)
  have : Finite (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; exact Module.finrank_pos.ne')
  letI := Fintype.ofFinite (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)
  exact gen_fil (P.PD K) (by rw [Fintype.card_eq_nat_card, hc]) ρ hfin
