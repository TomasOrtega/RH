import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.Counterexamples.TwistSurvey.ConjModelCast
import Formalism.FormalDegreeBessel.FormalDegreeRatio.DSLowK

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict

open Formalism.L2.NTheta in

/- English proof (translation)
Introduce `a b hab`. Establish `h1 : (a : ℕ) < b` using `hab`. Establish `h2` using `b.2`. Establish `h3` using `lamAt_add_add_le h (b - a) a (by omega)`. Rewrite `h3` using `[show (a : ℕ) + (b - a) = b by omega]`.

Establish `h4 : (1 : ℚ) ≤ (((b : ℕ) - a : ℕ) : ℚ)`. Establish `: 1 ≤ (b : ℕ) - a` using `by omega`. Conclude with `this` after adjusting the coercions. Use `show lamAt h b < lamAt h a`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem lamAt_strictAnti {R : Ranks} (h : HCParam R) {n : ℕ} (hn : n = R.r) :
    StrictAnti fun a : Fin n => lamAt h a := by
  intro a b hab
  have h1 : (a : ℕ) < b := hab
  have h2 := b.2
  have h3 := lamAt_add_add_le h (b - a) a (by omega)
  rw [show (a : ℕ) + (b - a) = b by omega] at h3
  have h4 : (1 : ℚ) ≤ (((b : ℕ) - a : ℕ) : ℚ) := by
    have : 1 ≤ (b : ℕ) - a := by omega
    exact_mod_cast this
  show lamAt h b < lamAt h a
  linarith

open Formalism.L2.NTheta in

/- English proof (translation)
Establish `ho : Odd (p + q)` using `by rw [hpq, hn]; exact odd_r R`. Use extensionality with `x`. Simplify using `only [holPar, Finset.mem_image, Finset.mem_univ, true_and, holEnt_kapW h p q ho]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a | a, rfl⟩`.

Conclude with `⟨⟨a, by have := a.2; omega⟩, by simp⟩`. Conclude with `⟨⟨p + a, by have := a.2; omega⟩, by simp⟩`. Introduce and unpack `⟨a, rfl⟩`. Distinguish the cases in `ha : (a : ℕ) < p`. Conclude with `⟨Sum.inl ⟨a, ha⟩, by simp [ha]⟩`.

Use `⟨Sum.inr ⟨a - p, by have := a.2; omega⟩, ?_⟩` and prove the remaining obligations. Simplify using `[ha, show p + ((a : ℕ) - p) = a by omega]`.
-/
theorem holPar_kapW_eq {R : Ranks} (h : HCParam R) {n p q : ℕ} (hn : n = R.r) (hpq : p + q = n) :
    holPar p q (kapW h p q) = Finset.univ.image fun a : Fin n => (lamAt h a, decide ((a : ℕ) < p)) := by
  have ho : Odd (p + q) := by rw [hpq, hn]; exact odd_r R
  ext x
  simp only [holPar, Finset.mem_image, Finset.mem_univ, true_and, holEnt_kapW h p q ho]
  constructor
  · rintro ⟨a | a, rfl⟩
    · exact ⟨⟨a, by have := a.2; omega⟩, by simp⟩
    · exact ⟨⟨p + a, by have := a.2; omega⟩, by simp⟩
  · rintro ⟨a, rfl⟩
    by_cases ha : (a : ℕ) < p
    · exact ⟨Sum.inl ⟨a, ha⟩, by simp [ha]⟩
    · refine ⟨Sum.inr ⟨a - p, by have := a.2; omega⟩, ?_⟩
      simp [ha, show p + ((a : ℕ) - p) = a by omega]

open Formalism.L2.NTheta in

/- English proof (translation)
Take `⟨hs, f, hf, hS⟩` from `he`. Rewrite `hS` using `[holPar_kapW_eq h hn hpq]`. Establish `hg` using `lamAt_strictAnti h hn`. Establish `hfs : StrictAnti f` using `fun a b hab => by`. Use `hs hab` as an intermediate fact.

Rewrite `this` using `[hf, hf]`. Conclude with `this` after adjusting the coercions. Establish `m1 : ∀ a, ∃ b : Fin n, (lamAt h b, decide ((b : ℕ) < p)) = (f a, ε a)` using `fun a => by`. Establish `: (f a, ε a) ∈ Finset.univ.image fun a : Fin n => (lamAt h a, decide ((a : ℕ) < p))`. Rewrite using `[hS]`.

Conclude with `Finset.mem_image_of_mem _ (Finset.mem_univ a)`. Take `⟨b, -, hb⟩` from `Finset.mem_image.1 this`. Conclude with `⟨b, hb⟩`. Establish `m2 : ∀ a : Fin n, ∃ b, (f b, ε b) = (lamAt h a, decide ((a : ℕ) < p))` using `fun a => by`. Establish `: (lamAt h a, decide ((a : ℕ) < p)) ∈ Finset.univ.image fun a : Fin n => (f a, ε a)`.

Rewrite using `[← hS]`. Conclude with `Finset.mem_image_of_mem (fun a : Fin n => (lamAt h a, decide ((a : ℕ) < p))) (Finset.mem_univ a)`. Take `⟨b, -, hb⟩` from `Finset.mem_image.1 this`. Conclude with `⟨b, hb⟩`. Establish `e : f = fun a : Fin n => lamAt h a`.

Use `(StrictMono.range_inj hfs.dual_right hg.dual_right).1 ?_ |> fun e => funext fun a => congrFun e a` and prove the remaining obligations. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, rfl⟩`. Take `⟨b, hb⟩` from `m1 a`.

Conclude with `⟨b, congrArg Prod.fst hb⟩`. Introduce and unpack `⟨a, rfl⟩`. Take `⟨b, hb⟩` from `m2 a`. Conclude with `⟨b, congrArg Prod.fst hb⟩`. Substitute `e` using the available equality.

Use `⟨hf a, ?_⟩` and prove the remaining obligations. Take `⟨b, hb⟩` from `m1 a`. Take `rfl : b = a` from `hg.injective (congrArg Prod.fst hb)`. Conclude with `(congrArg Prod.snd hb).symm`.
-/
theorem isEnum_holPar_kapW {R : Ranks} (h : HCParam R) {n p q : ℕ} (hn : n = R.r) (hpq : p + q = n)
    {lam : Fin n → ℝ} {ε : Fin n → Bool} (he : IsEnum (holPar p q (kapW h p q)) lam ε) (a : Fin n) :
    lam a = (lamAt h a : ℝ) ∧ ε a = decide ((a : ℕ) < p) := by
  obtain ⟨hs, f, hf, hS⟩ := he
  rw [holPar_kapW_eq h hn hpq] at hS
  have hg := lamAt_strictAnti h hn
  have hfs : StrictAnti f := fun a b hab => by
    have := hs hab
    rw [hf, hf] at this
    exact_mod_cast this
  have m1 : ∀ a, ∃ b : Fin n, (lamAt h b, decide ((b : ℕ) < p)) = (f a, ε a) := fun a => by
    have : (f a, ε a) ∈ Finset.univ.image fun a : Fin n => (lamAt h a, decide ((a : ℕ) < p)) := by
      rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
    obtain ⟨b, -, hb⟩ := Finset.mem_image.1 this
    exact ⟨b, hb⟩
  have m2 : ∀ a : Fin n, ∃ b, (f b, ε b) = (lamAt h a, decide ((a : ℕ) < p)) := fun a => by
    have : (lamAt h a, decide ((a : ℕ) < p)) ∈ Finset.univ.image fun a : Fin n => (f a, ε a) := by
      rw [← hS]; exact Finset.mem_image_of_mem (fun a : Fin n => (lamAt h a, decide ((a : ℕ) < p))) (Finset.mem_univ a)
    obtain ⟨b, -, hb⟩ := Finset.mem_image.1 this
    exact ⟨b, hb⟩
  have e : f = fun a : Fin n => lamAt h a := by
    refine (StrictMono.range_inj hfs.dual_right hg.dual_right).1 ?_ |> fun e => funext fun a => congrFun e a
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      obtain ⟨b, hb⟩ := m1 a
      exact ⟨b, congrArg Prod.fst hb⟩
    · rintro ⟨a, rfl⟩
      obtain ⟨b, hb⟩ := m2 a
      exact ⟨b, congrArg Prod.fst hb⟩
  subst e
  refine ⟨hf a, ?_⟩
  obtain ⟨b, hb⟩ := m1 a
  obtain rfl : b = a := hg.injective (congrArg Prod.fst hb)
  exact (congrArg Prod.snd hb).symm

/- English proof (translation)
Introduce `D G _ _ Pl0 T0 A T _ R κ v₀ ht i σ hσ`. Establish `hs : ∀ ρ, (Wc D i).sig (tauE D ρ) = D.R.sigW ((i : ℕ) + 1)` using `fun ρ => D.sp.W_sigval _ (inR i).1 (inR i).2 _`. Establish `hr : (D.R.sigW ((i : ℕ) + 1)).1 + (D.R.sigW ((i : ℕ) + 1)).2 = (Wc D i).rank`. Use `D.R.m_add_three_le_k` as an intermediate fact. Establish `hi` using `i.2`.

Rewrite using `[rank_Wc i]`. Simplify using `only [Ranks.sigW, Ranks.r]`. Use linear arithmetic over natural numbers and integers. Establish `key : ∀ ρ a, (R.MW i σ).lam ρ a = (Formalism.L2.NTheta.lamAt (D.hc (lab σ ρ)) a : ℝ) ∧ (R.MW i σ).ε ρ a = decide ((a : ℕ) < (D.R.sigW ((i : ℕ) + 1)).1)` using `fun ρ a => by`. Establish `he` using `(R.MW i σ).enum ρ`.

Unfold `Links.parAt at he`. Rewrite `he` using `[if_pos ((GlobalTheory.ConjReading.branch_of_pins T ht.alg ht.laws.pins σ ρ).1 hσ)]`. Rewrite using `[← hs ρ]`. Conclude with `isEnum_holPar_kapW _ (rank_Wc i) (by rw [hs ρ]; exact hr) he a`. Establish `hc : ∀ ρ, Formalism.QuantumDeterminants.IsHCParam ((R.MW i σ).lam ρ)` using `fun ρ => by`.

Use `⟨((R.MW i σ).enum ρ).1, fun a => ?_⟩` and prove the remaining obligations. Take `⟨z, hz⟩` from `Formalism.L2.NTheta.lamAt_int (D.hc (lab σ ρ)) a`. Take `⟨s, hs'⟩` from `Formalism.L2.NTheta.odd_r D.R`. Use `⟨z - s, ?_⟩` and prove the remaining obligations. Establish `hn : (((Wc D i).rank : ℕ) : ℝ) = 2 * s + 1` using `by rw [rank_Wc i, hs']; push_cast; rfl`.

Rewrite using `[(key ρ a).1, hz, hn]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `⟨fun ρ => ⟨hc ρ, _, by omega, fun a => (key ρ a).2⟩, fun ρ => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[nNeg_shape (by omega) fun a => (key ρ a).2]`.

Use linear arithmetic over natural numbers and integers. Use `choose w hw using fun ρ a => Formalism.QuantumDeterminants.low_k_integrable_holds _ ((R.MW i σ).ε ρ) _ (hc ρ).2 a`. Conclude with `⟨fun ρ c => w ρ (revNeg ((R.MW i σ).ε ρ) (arr (nNeg ((R.MW i σ).ε ρ)) c)), fun ρ c => (hw ρ _).symm⟩`.
-/
theorem holShape_of_good : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), TieIn T R κ v₀ → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (res T σ) → HolShape (R.MW i σ) ∧ (∀ ρ, nNeg ((R.MW i σ).ε ρ) = (D.R.sigW ((i : ℕ) + 1)).2) ∧ ∃ w, WtIs (R.MW i σ) w := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ ht i σ hσ
  have hs : ∀ ρ, (Wc D i).sig (tauE D ρ) = D.R.sigW ((i : ℕ) + 1) := fun ρ => D.sp.W_sigval _ (inR i).1 (inR i).2 _
  have hr : (D.R.sigW ((i : ℕ) + 1)).1 + (D.R.sigW ((i : ℕ) + 1)).2 = (Wc D i).rank := by
    have := D.R.m_add_three_le_k
    have hi := i.2
    rw [rank_Wc i]
    simp only [Ranks.sigW, Ranks.r]
    omega
  have key : ∀ ρ a, (R.MW i σ).lam ρ a = (Formalism.L2.NTheta.lamAt (D.hc (lab σ ρ)) a : ℝ) ∧
      (R.MW i σ).ε ρ a = decide ((a : ℕ) < (D.R.sigW ((i : ℕ) + 1)).1) := fun ρ a => by
    have he := (R.MW i σ).enum ρ
    unfold Links.parAt at he
    rw [if_pos ((GlobalTheory.ConjReading.branch_of_pins T ht.alg ht.laws.pins σ ρ).1 hσ)] at he
    rw [← hs ρ]
    exact isEnum_holPar_kapW _ (rank_Wc i) (by rw [hs ρ]; exact hr) he a
  have hc : ∀ ρ, Formalism.QuantumDeterminants.IsHCParam ((R.MW i σ).lam ρ) := fun ρ => by
    refine ⟨((R.MW i σ).enum ρ).1, fun a => ?_⟩
    obtain ⟨z, hz⟩ := Formalism.L2.NTheta.lamAt_int (D.hc (lab σ ρ)) a
    obtain ⟨s, hs'⟩ := Formalism.L2.NTheta.odd_r D.R
    refine ⟨z - s, ?_⟩
    have hn : (((Wc D i).rank : ℕ) : ℝ) = 2 * s + 1 := by rw [rank_Wc i, hs']; push_cast; rfl
    rw [(key ρ a).1, hz, hn]
    push_cast
    ring
  refine ⟨fun ρ => ⟨hc ρ, _, by omega, fun a => (key ρ a).2⟩, fun ρ => ?_, ?_⟩
  · rw [nNeg_shape (by omega) fun a => (key ρ a).2]
    omega
  · choose w hw using fun ρ a => Formalism.QuantumDeterminants.low_k_integrable_holds _ ((R.MW i σ).ε ρ) _ (hc ρ).2 a
    exact ⟨fun ρ c => w ρ (revNeg ((R.MW i σ).ε ρ) (arr (nNeg ((R.MW i σ).ε ρ)) c)), fun ρ c => (hw ρ _).symm⟩

end GlobalTheory.HolDict
