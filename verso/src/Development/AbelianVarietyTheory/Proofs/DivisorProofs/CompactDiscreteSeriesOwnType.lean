import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumEquiv
import Development.AbelianVarietyTheory.Definitions.Divisors.VdmSplit

noncomputable section

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.TRGap

namespace GlobalTheory.PsCo.PcEF

open GlobalTheory.PsCo.PcEG

variable {n : ℕ}

/- English proof (translation)
Break down `h with hp | hq` into its components or cases. Establish `h1 : ∀ c, ε c = false` using `fun c => by`. Use `Finset.filter_eq_empty_iff.1 (Finset.card_eq_zero.1 hp) (Finset.mem_univ c)` as an intermediate fact. Simplify using `using this`. Rewrite using `[h1 a, h1 b]`.

Establish `h1 : ∀ c, ε c = true` using `fun c => by`. Use `Finset.filter_eq_empty_iff.1 (Finset.card_eq_zero.1 hq) (Finset.mem_univ c)` as an intermediate fact. Simplify using `using this`. Rewrite using `[h1 a, h1 b]`.
-/
theorem cpt_const {ε : Fin n → Bool} (h : pOf ε = 0 ∨ qOf ε = 0) (a b : Fin n) : ε a = ε b := by
  rcases h with hp | hq
  · have h1 : ∀ c, ε c = false := fun c => by
      have := Finset.filter_eq_empty_iff.1 (Finset.card_eq_zero.1 hp) (Finset.mem_univ c)
      simpa using this
    rw [h1 a, h1 b]
  · have h1 : ∀ c, ε c = true := fun c => by
      have := Finset.filter_eq_empty_iff.1 (Finset.card_eq_zero.1 hq) (Finset.mem_univ c)
      simpa using this
    rw [h1 a, h1 b]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Formalism.REAL.Jm, Matrix.diagonal_mul, Matrix.mul_diagonal, hc i j]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cpt_Jm_comm {ε : Fin n → Bool} (hc : ∀ a b, ε a = ε b) (M : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.Jm ε * M = M * Formalism.REAL.Jm ε := by
  ext i j
  simp only [Formalism.REAL.Jm, Matrix.diagonal_mul, Matrix.mul_diagonal, hc i j]
  ring

/- English proof (translation)
Use extensionality with `g`. Simplify using `only [Formalism.REAL.Kset, Formalism.MainNotions.S.UJset, Formalism.REAL.inUJ, Set.mem_ofPred_eq, Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hu, -⟩`. Rewrite using `[Matrix.mul_assoc, cpt_Jm_comm hc g, ← Matrix.mul_assoc, hu, Matrix.one_mul]`.

Introduce `h`. Use `⟨?_, (cpt_Jm_comm hc g).symm⟩` and prove the remaining obligations. Establish `h2 : g.conjTranspose * g * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε`. Rewrite using `[Matrix.mul_assoc, ← cpt_Jm_comm hc g, ← Matrix.mul_assoc]`. Conclude with `h`.

Establish `h3` using `congrArg (· * Formalism.REAL.Jm ε) h2`. Simplify using `only [Matrix.mul_assoc, Formalism.REAL.Jm_mul_self, Matrix.mul_one] at h3`. Conclude with `h3`.
-/
theorem cpt_Kset_eq {ε : Fin n → Bool} (hc : ∀ a b, ε a = ε b) :
    Formalism.REAL.Kset ε = Formalism.MainNotions.S.UJset ε := by
  ext g
  simp only [Formalism.REAL.Kset, Formalism.MainNotions.S.UJset, Formalism.REAL.inUJ, Set.mem_ofPred_eq, Matrix.mem_unitaryGroup_iff',
    Matrix.star_eq_conjTranspose]
  constructor
  · rintro ⟨hu, -⟩
    rw [Matrix.mul_assoc, cpt_Jm_comm hc g, ← Matrix.mul_assoc, hu, Matrix.one_mul]
  · intro h
    refine ⟨?_, (cpt_Jm_comm hc g).symm⟩
    have h2 : g.conjTranspose * g * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε := by
      rw [Matrix.mul_assoc, ← cpt_Jm_comm hc g, ← Matrix.mul_assoc]
      exact h
    have h3 := congrArg (· * Formalism.REAL.Jm ε) h2
    simp only [Matrix.mul_assoc, Formalism.REAL.Jm_mul_self, Matrix.mul_one] at h3
    exact h3

/- English proof (translation)
Introduce `n ε lam h`. Establish `hc` using `cpt_const h`. Use `⟨fun k => ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `: IsEmpty {x : Fin n × Fin n // IsPhys ε x}` using `⟨fun x => by`. Establish `h1` using `x.2.1`.

Establish `h2` using `x.2.2`. Rewrite `h1` using `[hc x.1.1 x.1.2]`. Rewrite `h2` using `[h1]`. Conclude with `Bool.noConfusion h2⟩`. Unfold `physDet`.

Conclude with `Matrix.det_isEmpty`. Unfold `sDeg sModes`. Rewrite using `[Finset.card_eq_zero, Finset.filter_eq_empty_iff]`. Introduce and unpack `x - ⟨h1, h2, -⟩`. Rewrite `h1` using `[hc x.1 x.2]`.

Rewrite `h2` using `[h1]`. Conclude with `Bool.noConfusion h2`. Introduce `X _ _ D hD`. Take `⟨hcs, hnt, hU, hirr, -, ⟨S, hS⟩, -⟩` from `hD`. Use `hcs` as an intermediate fact.

Establish `hKU` using `cpt_Kset_eq hc`. Establish `: FiniteDimensional ℂ S` using `hS.1`. Establish `hclosed : IsClosed (S : Set X)` using `Submodule.closed_of_finiteDimensional S`. Establish `hstab : ∀ g ∈ Formalism.MainNotions.S.UJset ε, ∀ v ∈ S, D g v ∈ S` using `fun g hg v hv => hS.2.1 g (hKU ▸ hg) v hv`. Establish `htop : S = ⊤`.

Break down `hirr S hclosed hstab with h0 | h0` into its components or cases. It suffices to derive a contradiction. Take `⟨v, hv, hv0, -⟩` from `hS.2.2.2.1`. Rewrite `hv` using `[h0]`. Conclude with `hv0 ((Submodule.mem_bot ℂ).1 hv)`.

Conclude with `h0`. Substitute `htop` using the available equality. Establish `hga : gaW ε lam = Formalism.QuantumDeterminants.lowK ε lam`. Use function extensionality and compare the values at `a`. Establish `hN : Formalism.REAL.rhoN ε a = 0`.

Unfold `Formalism.REAL.rhoN`. Establish `e1 : (Finset.univ.filter fun b => a < b ∧ ε b ≠ ε a) = ∅` using `Finset.filter_eq_empty_iff.2 fun b _ hb => hb.2 (hc b a)`. Establish `e2 : (Finset.univ.filter fun b => b < a ∧ ε b ≠ ε a) = ∅` using `Finset.filter_eq_empty_iff.2 fun b _ hb => hb.2 (hc b a)`. Rewrite using `[e1, e2]`. Simplify using the standard rewrite rules.

Establish `hH : rhoHol ε a = 0`. Unfold `rhoHol`. Break down `h with hp | hq` into its components or cases. Establish `ha : ε a = false`. Use `Finset.filter_eq_empty_iff.1 (Finset.card_eq_zero.1 hp) (Finset.mem_univ a)` as an intermediate fact.

Simplify using `using this`. Simplify using `[ha, hp]`. Establish `ha : ε a = true`. Use `Finset.filter_eq_empty_iff.1 (Finset.card_eq_zero.1 hq) (Finset.mem_univ a)` as an intermediate fact. Simplify using `using this`.

Simplify using `[ha, hq]`. Simplify using `only [gaW, Formalism.QuantumDeterminants.lowK, Pi.add_apply, Pi.sub_apply, hN, hH, add_zero]`. Both sides reduce to the same expression. Use `⟨LinearEquiv.finiteDimensional Submodule.topEquiv, hnt, hKU ▸ hU, ?_⟩` and prove the remaining obligations. Rewrite using `[hga]`.

Conclude with `hS`.
-/
theorem compactDiscreteSeries_ownType : CptCase := by
  intro n ε lam h
  have hc := cpt_const h
  refine ⟨fun k => ?_, ?_, ?_⟩
  · have : IsEmpty {x : Fin n × Fin n // IsPhys ε x} :=
      ⟨fun x => by
        have h1 := x.2.1
        have h2 := x.2.2
        rw [hc x.1.1 x.1.2] at h1
        rw [h1] at h2
        exact Bool.noConfusion h2⟩
    unfold physDet
    exact Matrix.det_isEmpty
  · unfold sDeg sModes
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro x - ⟨h1, h2, -⟩
    rw [hc x.1 x.2] at h1
    rw [h1] at h2
    exact Bool.noConfusion h2
  · intro X _ _ D hD
    obtain ⟨hcs, hnt, hU, hirr, -, ⟨S, hS⟩, -⟩ := hD
    have := hcs
    have hKU := cpt_Kset_eq hc
    have : FiniteDimensional ℂ S := hS.1
    have hclosed : IsClosed (S : Set X) := Submodule.closed_of_finiteDimensional S
    have hstab : ∀ g ∈ Formalism.MainNotions.S.UJset ε, ∀ v ∈ S, D g v ∈ S := fun g hg v hv =>
      hS.2.1 g (hKU ▸ hg) v hv
    have htop : S = ⊤ := by
      rcases hirr S hclosed hstab with h0 | h0
      · exfalso
        obtain ⟨v, hv, hv0, -⟩ := hS.2.2.2.1
        rw [h0] at hv
        exact hv0 ((Submodule.mem_bot ℂ).1 hv)
      · exact h0
    subst htop
    have hga : gaW ε lam = Formalism.QuantumDeterminants.lowK ε lam := by
      funext a
      have hN : Formalism.REAL.rhoN ε a = 0 := by
        unfold Formalism.REAL.rhoN
        have e1 : (Finset.univ.filter fun b => a < b ∧ ε b ≠ ε a) = ∅ :=
          Finset.filter_eq_empty_iff.2 fun b _ hb => hb.2 (hc b a)
        have e2 : (Finset.univ.filter fun b => b < a ∧ ε b ≠ ε a) = ∅ :=
          Finset.filter_eq_empty_iff.2 fun b _ hb => hb.2 (hc b a)
        rw [e1, e2]
        simp
      have hH : rhoHol ε a = 0 := by
        unfold rhoHol
        rcases h with hp | hq
        · have ha : ε a = false := by
            have := Finset.filter_eq_empty_iff.1 (Finset.card_eq_zero.1 hp) (Finset.mem_univ a)
            simpa using this
          simp [ha, hp]
        · have ha : ε a = true := by
            have := Finset.filter_eq_empty_iff.1 (Finset.card_eq_zero.1 hq) (Finset.mem_univ a)
            simpa using this
          simp [ha, hq]
      simp only [gaW, Formalism.QuantumDeterminants.lowK, Pi.add_apply, Pi.sub_apply, hN, hH, add_zero]
      rfl
    refine ⟨LinearEquiv.finiteDimensional Submodule.topEquiv, hnt, hKU ▸ hU, ?_⟩
    rw [hga]
    exact hS

end GlobalTheory.PsCo.PcEF
