import Mathlib
import Formalism.LocalToGlobal.Columns.AtTLemmas

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Moves

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

open Classical in

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact.

Simplify using the standard rewrite rules. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem Deco.IsDnA.dia1 {P : ST} {q : 𝓞 E} {a : 𝓞 E ⧸ P.1.asIdeal} {d d' : Deco E n ST SG}
    (h : Deco.IsDnA P q a d d') (c : (𝓞 E ⧸ P.1.asIdeal)ˣ) :
    Deco.IsDnA P q (c.1 * a) d (d'.dia (Pi.mulSingle P c)) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · ext1
    · have h5 := congrArg Deco.N h1
      exact h5
    · funext Q y
      have h3 : d'.f Q = (d.dn P (d'.f P)).f Q := by rw [← h1]
      simp only [Deco.dia, Deco.dn] at h3 ⊢
      rcases eq_or_ne Q P with rfl | hQ
      · rw [Function.update_self]
      · rw [Function.update_of_ne hQ]
        rw [Function.update_of_ne hQ] at h3
        rw [h3, Pi.mulSingle_eq_of_ne hQ, Units.val_one, one_mul]
    · have h6 := congrArg Deco.be h1
      exact h6
  · intro e he hfe
    show ((Pi.mulSingle P c : DiaG E ST) P).1 * d'.f P (q • e) = c.1 * a
    rw [Pi.mulSingle_eq_same, h2 e he hfe]

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem Deco.L_dia (d : Deco E n ST SG) (c : DiaG E ST) : (d.dia c).L = d.L := by
  unfold Deco.L
  congr 1
  ext x
  show (x ∈ d.N ∧ ∀ P : ST, (c P).1 * d.f P x = 0) ↔ (x ∈ d.N ∧ ∀ P : ST, d.f P x = 0)
  simp only [Units.mul_right_eq_zero]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem Deco.Lsh_dia (d : Deco E n ST SG) (c : DiaG E ST) : (d.dia c).Lsh = d.Lsh := by
  unfold Deco.Lsh
  rw [Deco.L_dia]

end Moves

section Ops

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}
  (C : CoefPk X n (DecoSet X.E n ST SG)) (Λ : LevFam X.E X.K n SG)

end Ops

section Cols

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (Ps : CharT X Pr)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem colDel_dia (u : Pr.Word) (j : ℕ) (c : DiaG X.E (Pr.vT u)) (d : (colGSD W Ch u j).D) :
    (colGSD W Ch u j).Del (c • d) = (colGSD W Ch u j).Del d := by
  show delAtr X.emb (W.lamTrue u j) (d.1.dia c).Lsh = delAtr X.emb (W.lamTrue u j) d.1.Lsh
  rw [Deco.Lsh_dia]

end Cols

section Adj

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end Adj

section AtW

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem TUmC_of_seenBarC (hPr : Pr.Ok) (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) (h : seenBarC Pr u w) :
    TUmC W Ch u w = 1 := by
  unfold TUmC UprodC expTc
  rw [VVTc_of_seenBarC W hPr u w h, topsP_of_seenBarC W hPr u w h]
  simp

/- English proof (translation)
By extensionality, compare the relevant components. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem NlamG_of_seenBarC (hPr : Pr.Ok) (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) (h : seenBarC Pr u w) :
    NlamG W Ch u w = MramL W Ch u := by
  ext φ
  show (φ : MfV W Ch u) ∈ scaledRamifiedLattice W Ch u w ↔ (φ : MfV W Ch u) ∈ MfL W Ch u
  unfold scaledRamifiedLattice
  rw [TUmC_of_seenBarC W Ch hPr u w h]
  constructor
  · rintro ⟨ψ, hψ, e⟩
    have e' : ψ = (φ : MfV W Ch u) := e
    rw [← e']
    exact hψ.1
  · intro hφ
    exact ⟨φ, ⟨hφ, φ.2⟩, rfl⟩

end AtW

end Formalism.L2.Col
