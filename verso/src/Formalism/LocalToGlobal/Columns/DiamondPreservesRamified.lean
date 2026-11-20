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
Take `⟨h1, h2⟩` from `h`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `ext1`. Establish `h5` using `congrArg Deco.N h1`. Conclude with `h5`.

Use function extensionality and compare the values at `Q y`. Establish `h3 : d'.f Q = (d.dn P (d'.f P)).f Q` using `by rw [← h1]`. Simplify using `only [Deco.dia, Deco.dn] at h3 ⊢`. Break down `eq_or_ne Q P with rfl | hQ` into its components or cases. Rewrite using `[Function.update_self]`.

Rewrite using `[Function.update_of_ne hQ]`. Rewrite `h3` using `[Function.update_of_ne hQ]`. Rewrite using `[h3, Pi.mulSingle_eq_of_ne hQ, Units.val_one, one_mul]`. Establish `h6` using `congrArg Deco.be h1`. Conclude with `h6`.

Introduce `e he hfe show ((Pi.mulSingle P c : DiaG E ST) P).1 * d'.f P (q • e) = c.1 * a`. Rewrite using `[Pi.mulSingle_eq_same, h2 e he hfe]`.
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
Unfold `Deco.L`. Use `congr 1`. Use extensionality with `x`. Use `show (x ∈ d.N ∧ ∀ P : ST, (c P).1 * d.f P x = 0) ↔ (x ∈ d.N ∧ ∀ P : ST, d.f P x = 0)`. Simplify using `only [Units.mul_right_eq_zero]`.
-/
theorem Deco.L_dia (d : Deco E n ST SG) (c : DiaG E ST) : (d.dia c).L = d.L := by
  unfold Deco.L
  congr 1
  ext x
  show (x ∈ d.N ∧ ∀ P : ST, (c P).1 * d.f P x = 0) ↔ (x ∈ d.N ∧ ∀ P : ST, d.f P x = 0)
  simp only [Units.mul_right_eq_zero]

/- English proof (translation)
Unfold `Deco.Lsh`. Rewrite using `[Deco.L_dia]`.
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
Use `show delAtr X.emb (W.lamTrue u j) (d.1.dia c).Lsh = delAtr X.emb (W.lamTrue u j) d.1.Lsh`. Rewrite using `[Deco.Lsh_dia]`.
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
Unfold `TUmC UprodC expTc`. Rewrite using `[VVTc_of_seenBarC W hPr u w h, topsP_of_seenBarC W hPr u w h]`. Simplify using the standard rewrite rules.
-/
theorem TUmC_of_seenBarC (hPr : Pr.Ok) (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) (h : seenBarC Pr u w) :
    TUmC W Ch u w = 1 := by
  unfold TUmC UprodC expTc
  rw [VVTc_of_seenBarC W hPr u w h, topsP_of_seenBarC W hPr u w h]
  simp

/- English proof (translation)
Use extensionality with `φ`. Use `show (φ : MfV W Ch u) ∈ scaledRamifiedLattice W Ch u w ↔ (φ : MfV W Ch u) ∈ MfL W Ch u`. Unfold `scaledRamifiedLattice`. Rewrite using `[TUmC_of_seenBarC W Ch hPr u w h]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨ψ, hψ, e⟩`. Establish `e' : ψ = (φ : MfV W Ch u)` using `e`. Rewrite using `[← e']`. Conclude with `hψ.1`. Introduce `hφ`.

Conclude with `⟨φ, ⟨hφ, φ.2⟩, rfl⟩`.
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
