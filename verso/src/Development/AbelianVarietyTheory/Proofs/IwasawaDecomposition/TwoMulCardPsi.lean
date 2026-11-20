import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FormsOver
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair
import Formalism.LocalToGlobal.ProjectiveLattices.HostRank

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.TrueGeo GlobalTheory.ShFam

namespace GlobalTheory.ShFam.CmDim

/- English proof (translation)
Establish `hb` using `(factEmb D.R D.host).1`. Establish `h1 : Nat.card (D.R.GG) = Nat.card (D.host.E →+* ℂ)` using `Nat.card_congr (Equiv.ofBijective _ hb)`. Establish `h2 : Nat.card (D.host.E →+* ℂ) = Module.finrank ℚ D.host.E`. Rewrite using `[Nat.card_eq_fintype_card]`. Conclude with `NumberField.Embeddings.card D.host.E ℂ`.

Establish `h4 : Nat.card (D.R.GG) = 4 * D.R.ord` using `D.R.toFrame.natCard_GG`. Rewrite using `[← h2, ← h1, h4]`.
-/
theorem finrank_host (D : D7) : Module.finrank ℚ D.host.E = 4 * D.R.ord := by
  have hb := (factEmb D.R D.host).1
  have h1 : Nat.card (D.R.GG) = Nat.card (D.host.E →+* ℂ) := Nat.card_congr (Equiv.ofBijective _ hb)
  have h2 : Nat.card (D.host.E →+* ℂ) = Module.finrank ℚ D.host.E := by
    rw [Nat.card_eq_fintype_card]; exact NumberField.Embeddings.card D.host.E ℂ
  have h4 : Nat.card (D.R.GG) = 4 * D.R.ord := D.R.toFrame.natCard_GG
  rw [← h2, ← h1, h4]

/- English proof (translation)
Establish `h4 : Nat.card φ.GG = 4 * φ.ord` using `φ.natCard_GG`. Establish `hfin : Finite φ.GG` using `Nat.finite_of_card_ne_zero (by rw [h4]; have := φ.ord_pos; omega)`. Establish `e1 : {g : φ.GG // g ∈ φ.Psi} ≃ {g : φ.GG // ¬ g ∈ φ.Psi}` using `(Equiv.mulRight φ.cc).subtypeEquiv fun g => mem_Psi_iff_mul_cc_notMem g`. Establish `h1` using `Nat.card_congr (Equiv.sumCompl fun g : φ.GG => g ∈ φ.Psi)`. Rewrite `h1` using `[Nat.card_sum, ← Nat.card_congr e1, h4]`.

Conclude with `(two_mul _).trans h1`.
-/
theorem two_mul_card_psi (φ : Formalism.HC.Frame) : 2 * Nat.card φ.Psi = 4 * φ.ord := by
  classical
  have h4 : Nat.card φ.GG = 4 * φ.ord := φ.natCard_GG
  have hfin : Finite φ.GG := Nat.finite_of_card_ne_zero (by rw [h4]; have := φ.ord_pos; omega)
  have e1 : {g : φ.GG // g ∈ φ.Psi} ≃ {g : φ.GG // ¬ g ∈ φ.Psi} :=
    (Equiv.mulRight φ.cc).subtypeEquiv fun g => mem_Psi_iff_mul_cc_notMem g
  have h1 := Nat.card_congr (Equiv.sumCompl fun g : φ.GG => g ∈ φ.Psi)
  rw [Nat.card_sum, ← Nat.card_congr e1, h4] at h1
  exact (two_mul _).trans h1

/- English proof (translation)
Establish `h1` using `two_mul_card_psi D.R.toFrame`. Establish `h2` using `Nat.card_congr D.eTau`. Rewrite `h2` using `[Nat.card_eq_fintype_card]`. Establish `h3` using `finrank_host D`. Use linear arithmetic over natural numbers and integers.
-/
theorem card_tau (D : D7) : Fintype.card D.what₂.Tau = Module.finrank ℚ D.host.E / 2 := by
  have h1 := two_mul_card_psi D.R.toFrame
  have h2 := Nat.card_congr D.eTau
  rw [Nat.card_eq_fintype_card] at h2
  have h3 := finrank_host D
  omega

/- English proof (translation)
Set `ψ : D.what₂.Tau → GlobalTheory.AllWt.Psi A.H` to `fun t => ⟨DV.tauEmb D t, A.cm t⟩`. Establish `hb : Function.Bijective ψ`. Prove the components needed by the constructor for the conclusion. Introduce `a b h`. Conclude with `D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 (congrArg Subtype.val h)))`.

Introduce and unpack `⟨τ, hτ⟩`. Take `⟨g, rfl⟩` from `(factEmb D.R D.host).1.2 τ`. Establish `h3 : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ)` using `D.host.φ₀_mem`. Rewrite `hτ` using `[A.rt_eq, A.cmHost_rootComplex_eq_pm_sqrt, h3]`. Take `⟨t, ht⟩` from `(exists_tauEmb_iff D g).2 (((factEmb D.R D.host).2 g).1 hτ)`.

Conclude with `⟨t, Subtype.ext ht.symm⟩`. Conclude with `⟨⟨Equiv.ofBijective ψ hb, fun _ => rfl⟩⟩`.
-/
theorem cmList_nonempty {D : D7} (A : Amb D) : Nonempty (CmList A) := by
  let ψ : D.what₂.Tau → GlobalTheory.AllWt.Psi A.H := fun t => ⟨DV.tauEmb D t, A.cm t⟩
  have hb : Function.Bijective ψ := by
    constructor
    · intro a b h
      exact D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 (congrArg Subtype.val h)))
    · rintro ⟨τ, hτ⟩
      obtain ⟨g, rfl⟩ := (factEmb D.R D.host).1.2 τ
      have h3 : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
      rw [A.rt_eq, A.cmHost_rootComplex_eq_pm_sqrt, h3] at hτ
      obtain ⟨t, ht⟩ := (exists_tauEmb_iff D g).2 (((factEmb D.R D.host).2 g).1 hτ)
      exact ⟨t, Subtype.ext ht.symm⟩
  exact ⟨⟨Equiv.ofBijective ψ hb, fun _ => rfl⟩⟩

/- English proof (translation)
Introduce `D A`. Use `⟨cmList_nonempty A, ?_, fun N j S κ s Φ i => ?_⟩` and prove the remaining obligations. Rewrite using `[finrank_host]`. Establish `h : 2 ^ 2 ≤ 2 ^ D.R.e` using `Nat.pow_le_pow_right two_pos D.host.two_le_e`. Establish `h' : 2 ^ D.R.e ≤ D.R.ord`.

Conclude with `D.R.toFrame.two_pow_le_ord`. Use linear arithmetic over natural numbers and integers. Rewrite using `[Φ.dim_eq i, Formalism.DegreeFormula.dimFl, card_tau]`.
-/
theorem cm_dim : ∀ (D : D7) (A : Amb D), Nonempty (CmList A) ∧ 2 < Module.finrank ℚ D.host.E / 2 ∧
    ∀ (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (i : s.Comp),
      (Φ.C i).Y.dim = Formalism.DegreeFormula.dimFl D.what₂.Tau N := by
  intro D A
  refine ⟨cmList_nonempty A, ?_, fun N j S κ s Φ i => ?_⟩
  · rw [finrank_host]
    have h : 2 ^ 2 ≤ 2 ^ D.R.e := Nat.pow_le_pow_right two_pos D.host.two_le_e
    have h' : 2 ^ D.R.e ≤ D.R.ord := by
      exact D.R.toFrame.two_pow_le_ord
    omega
  · rw [Φ.dim_eq i, Formalism.DegreeFormula.dimFl, card_tau]

end GlobalTheory.ShFam.CmDim
