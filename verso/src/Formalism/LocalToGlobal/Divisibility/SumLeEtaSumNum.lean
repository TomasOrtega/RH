import Formalism.LocalToGlobal.Divisibility.TwistedPlaceEtaSumLeExtended

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.DIV

open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef

section N

open Formalism.BasicNotions Formalism.MainNotions

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}

/- English proof (translation)
Unfold `SizeData₂.lwP`. Rewrite using `[Equiv.apply_symm_apply]`. Both sides reduce to the same expression.
-/
theorem lw_eq_lwP (D : D7) (y : HeightOneSpectrum (𝓞 D.what₂.LL)) : Formalism.DivisionValues.lw y = SizeData₂.lwP (D.plEq.symm y) := by
  unfold SizeData₂.lwP
  rw [Equiv.apply_symm_apply]
  rfl

/- English proof (translation)
Rewrite using `[D.ram_eq, Equiv.apply_symm_apply, ← lf_eW_eq_ramw]`. Both sides reduce to the same expression.
-/
theorem ramw_eq_ramIdx (D : D7) (y : HeightOneSpectrum (𝓞 D.what₂.LL)) :
    ((ramw y : ℤ) : ℝ) = ((D.what₂.places.ramIdx (D.plEq.symm y) : ℕ) : ℝ) := by
  rw [D.ram_eq, Equiv.apply_symm_apply, ← lf_eW_eq_ramw]
  rfl

/- English proof (translation)
Take `⟨g, hg⟩ : ∃ g : D.what₂.places.Pl → ℝ, g = fun w => SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) * (D.what₂.etaJ ((i : ℕ) + 1) w : ℝ)` from `⟨_, rfl⟩`. Establish `hterm : ∀ y ∈ S0.Tw, Formalism.DivisionValues.lw y * (A.fam.etaJW P0 ψ0 Zs i (S0.μ y) y : ℝ) = g (D.plEq.symm y)`. Introduce `y hy`. Establish `h1 : Formalism.DivisionValues.lw y = SizeData₂.lwP (D.plEq.symm y)` using `lw_eq_lwP D y`. Establish `h2 : ((ramw y : ℤ) : ℝ) = ((D.what₂.places.ramIdx (D.plEq.symm y) : ℕ) : ℝ)` using `ramw_eq_ramIdx D y`.

Establish `h3 : D.what₂.etaJ ((i : ℕ) + 1) (D.plEq.symm y) = A.fam.etaJ P0 ψ0 Zs i (S0.μ y) y`. Rewrite using `[hnum.etaJ i (D.plEq.symm y), Equiv.apply_symm_apply, if_pos hy]`. Rewrite using `[hg]`. Simplify using `only`. Rewrite using `[← A.fam.etaJ_ramw P0 ψ0 Zs i (S0.μ y) y, h1, h2, h3]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hsi : ∑ w ∈ S0.Tw.image D.plEq.symm, g w = ∑ y ∈ S0.Tw, g (D.plEq.symm y)` using `Finset.sum_image (fun x _ y _ hxy => D.plEq.symm.injective hxy)`. Establish `hE : Formalism.MainNotions.etaSum L ((i : ℕ) + 1) = ∑ w ∈ L.supp.filter (fun w => D.what₂.muAt w ≠ D.what₂.mu0), g w`. Rewrite using `[hg]`. Unfold `Formalism.MainNotions.etaSum`.

Both sides reduce to the same expression. Rewrite using `[Finset.sum_congr rfl hterm, ← hsi, hE]`. Apply `Finset.sum_le_sum_of_subset_of_nonneg` to reduce the goal to its premises. Introduce `w hw`. Take `⟨y, hy, rfl⟩` from `Finset.mem_image.1 hw`.

Conclude with `Finset.mem_filter.2 (hTw y hy)`. Introduce `w _ _`. Rewrite using `[hg]`. Conclude with `mul_nonneg (mul_nonneg (zero_le_logWeight w) (Nat.cast_nonneg _)) (by exact_mod_cast D.what₂.etaJ_nonneg _ w)`.
-/
theorem sum_le_etaSum_num (L : SizeData₂ D) (A : FamIn D.what₂.LL G Pl0 T m) {P0 : Subgroup G} {ψ0 : P0 →* D.what₂.LLˣ}
    {Zs : DefSub A.fam.amb} {S0 : IndefData (A.side P0 ψ0 Zs)} {tup : T → D.what₂.Tup} (hnum : NumTie D A S0 tup)
    (hTw : TieTwRec L S0.Tw) (i : Fin m) :
    ∑ y ∈ S0.Tw, Formalism.DivisionValues.lw y * (A.fam.etaJW P0 ψ0 Zs i (S0.μ y) y : ℝ) ≤ Formalism.MainNotions.etaSum L ((i : ℕ) + 1) := by
  classical
  obtain ⟨g, hg⟩ : ∃ g : D.what₂.places.Pl → ℝ,
      g = fun w => SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) * (D.what₂.etaJ ((i : ℕ) + 1) w : ℝ) := ⟨_, rfl⟩
  have hterm : ∀ y ∈ S0.Tw, Formalism.DivisionValues.lw y * (A.fam.etaJW P0 ψ0 Zs i (S0.μ y) y : ℝ) = g (D.plEq.symm y) := by
    intro y hy
    have h1 : Formalism.DivisionValues.lw y = SizeData₂.lwP (D.plEq.symm y) := lw_eq_lwP D y
    have h2 : ((ramw y : ℤ) : ℝ) = ((D.what₂.places.ramIdx (D.plEq.symm y) : ℕ) : ℝ) := ramw_eq_ramIdx D y
    have h3 : D.what₂.etaJ ((i : ℕ) + 1) (D.plEq.symm y) = A.fam.etaJ P0 ψ0 Zs i (S0.μ y) y := by
      rw [hnum.etaJ i (D.plEq.symm y), Equiv.apply_symm_apply, if_pos hy]
    rw [hg]
    dsimp only
    rw [← A.fam.etaJ_ramw P0 ψ0 Zs i (S0.μ y) y, h1, h2, h3]
    ring
  have hsi : ∑ w ∈ S0.Tw.image D.plEq.symm, g w = ∑ y ∈ S0.Tw, g (D.plEq.symm y) :=
    Finset.sum_image (fun x _ y _ hxy => D.plEq.symm.injective hxy)
  have hE : Formalism.MainNotions.etaSum L ((i : ℕ) + 1) = ∑ w ∈ L.supp.filter (fun w => D.what₂.muAt w ≠ D.what₂.mu0), g w := by
    rw [hg]
    unfold Formalism.MainNotions.etaSum
    rfl
  rw [Finset.sum_congr rfl hterm, ← hsi, hE]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro w hw
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hw
    exact Finset.mem_filter.2 (hTw y hy)
  · intro w _ _
    rw [hg]
    exact mul_nonneg (mul_nonneg (zero_le_logWeight w) (Nat.cast_nonneg _)) (by exact_mod_cast D.what₂.etaJ_nonneg _ w)

/- English proof (translation)
Introduce `i`. Establish `h1` using `sum_le_etaSum_num L A hnum hTw i`. Establish `hi : (i : ℕ) + 1 ∈ SizeData₂.lifts D`. Unfold `SizeData₂.lifts`. Conclude with `Finset.mem_Icc.2 ⟨by omega, by have := i.isLt; omega⟩`.

Establish `h2` using `hN ((i : ℕ) + 1) hi`. Unfold `Formalism.MainNotions.DIVinN_at at h2`. Rewrite `h2` using `[hD]`. Unfold `divSize`. Conclude with `h1.trans (h2.trans_eq (mul_comm _ _))`.
-/
theorem inEta_num (L : SizeData₂ D) (A : FamIn D.what₂.LL G Pl0 T m) {P0 : Subgroup G} {ψ0 : P0 →* D.what₂.LLˣ}
    {Zs : DefSub A.fam.amb} {S0 : IndefData (A.side P0 ψ0 Zs)} {tup : T → D.what₂.Tup} (Ce : ℝ)
    (hN : ∀ j ∈ SizeData₂.lifts D, Formalism.MainNotions.DIVinN_at L j Ce) (hm : m = D.R.m) (hnum : NumTie D A S0 tup)
    (hTw : TieTwRec L S0.Tw) (hD : D.what₂.D0 = (A.fam.R A.fam.μ0).dZ (A.fam.lvl P0 ψ0) (Zs.Z A.fam.μ0)) :
    InEta A.fam P0 ψ0 Zs S0.μ S0.Tw (fun _ => divSize L Ce) := by
  intro i
  have h1 := sum_le_etaSum_num L A hnum hTw i
  have hi : (i : ℕ) + 1 ∈ SizeData₂.lifts D := by
    unfold SizeData₂.lifts
    exact Finset.mem_Icc.2 ⟨by omega, by have := i.isLt; omega⟩
  have h2 := hN ((i : ℕ) + 1) hi
  unfold Formalism.MainNotions.DIVinN_at at h2
  rw [hD] at h2
  unfold divSize
  exact h1.trans (h2.trans_eq (mul_comm _ _))

variable {I0 Ty : Type}

/- English proof (translation)
The claim follows from `inEta_num L A3.A (Zs := A3.fam3.toSub2 Zs) (S0 := A3.indefDown S0) Ce hN hm hnum hTw hD`.
-/
theorem inEta3_num (L : SizeData₂ D) (A3 : FamIn3 D.what₂.LL G Pl0 I0 Ty T m) {P0 : Subgroup G} {ψ0 : P0 →* D.what₂.LLˣ}
    {Zs : DefSub A3.fam3.amb3} {S0 : IndefData (A3.side3 P0 ψ0 Zs)} {tup : T → D.what₂.Tup} (Ce : ℝ)
    (hN : ∀ j ∈ SizeData₂.lifts D, Formalism.MainNotions.DIVinN_at L j Ce) (hm : m = D.R.m)
    (hnum : NumTie D A3.A (A3.indefDown S0) tup) (hTw : TieTwRec L S0.Tw)
    (hD : D.what₂.D0 = (A3.A.fam.R A3.A.fam.μ0).dZ (A3.A.fam.lvl P0 ψ0) (Zs.Z A3.A.fam.μ0)) :
    InEta A3.A.fam P0 ψ0 (A3.fam3.toSub2 Zs) S0.μ S0.Tw (fun _ => divSize L Ce) :=
  inEta_num L A3.A (Zs := A3.fam3.toSub2 Zs) (S0 := A3.indefDown S0) Ce hN hm hnum hTw hD

end N

end Formalism.L2.DIV

end
