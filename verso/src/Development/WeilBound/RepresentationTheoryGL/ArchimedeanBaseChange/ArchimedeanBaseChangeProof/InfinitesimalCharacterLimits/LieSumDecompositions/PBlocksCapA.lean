import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksDefs
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.InfInd2Holds

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.CompanionTheory.CTFin GlobalTheory.BlockCap PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockCapelli

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem qdet_slice {n : Fin 2 → ℕ} (h : ∑ i, n i = n 0 + n 1) (τ : E →+* ℂ) (i : Fin 2) (w : ℂ)
    (ψ : Sm E (n 0 + n 1)) (m : ∀ j, GA E (n j)) (θ : Sm E (n i))
    (hθ : ∀ y, ψ.1 (leviEmb (Ad E) (stdBlocks n h) (Function.update m i y)) = θ.1 y) :
    (Formalism.REAL.qdet (fun p q : Fin (n i) => Eop (a := n 0 + n 1) τ (stdBlocks n h ⟨i, p⟩) (stdBlocks n h ⟨i, q⟩)) w ψ).1
      (leviEmb (Ad E) (stdBlocks n h) m) = (Formalism.REAL.qdet (Eop (a := n i) τ) w θ).1 (m i) := by
  have hR : restrLin (stdBlocks n h) m i ψ = θ := Subtype.ext (funext fun y => hθ y)
  have key := LinearMap.congr_fun (qdet_intertwine (restrLin (stdBlocks n h) m i) _ (Eop τ)
    (restrLin_Eop (stdBlocks n h) m i τ) w) ψ
  rw [LinearMap.comp_apply, LinearMap.comp_apply, hR] at key
  have k2 := congrArg (fun φ : Sm E (n i) => φ.1 (m i)) key
  have hm : Function.update m i (m i) = m := Function.update_eq_self i m
  have k3 : (Formalism.REAL.qdet (fun p q : Fin (n i) => Eop (a := n 0 + n 1) τ (stdBlocks n h ⟨i, p⟩)
      (stdBlocks n h ⟨i, q⟩)) w ψ).1 (leviEmb (Ad E) (stdBlocks n h) (Function.update m i (m i))) =
      (Formalism.REAL.qdet (Eop (a := n i) τ) w θ).1 (m i) := k2
  rwa [hm] at k3

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
theorem update_levPair_zero {n : Fin 2 → ℕ} (p : GA E (n 0) × GA E (n 1)) (y : GA E (n 0)) :
    Function.update (CapFactor.levPair p) 0 y = CapFactor.levPair (y, p.2) := by
  funext j
  match j with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
theorem update_levPair_one {n : Fin 2 → ℕ} (p : GA E (n 0) × GA E (n 1)) (y : GA E (n 1)) :
    Function.update (CapFactor.levPair p) 1 y = CapFactor.levPair (p.1, y) := by
  funext j
  match j with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact.

Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem capR_expand {n : Fin 2 → ℕ} (τ : E →+* ℂ) (w : ℂ) (G : Sm E (n 0 + n 1)) {k : ℕ}
    (b : Fin k → Sm E (n 0)) (q : Fin k → Sm E (n 1))
    (hG : ∀ p, G.1 (lev (Ad E) (n 0) (n 1) p) = ∑ i, (b i).1 p.1 * (q i).1 p.2) (p : GA E (n 0) × GA E (n 1)) :
    (capR (n 0) (n 1) τ w G).1 (lev (Ad E) (n 0) (n 1) p) = ∑ i, (cap τ w (b i)).1 p.1 * (q i).1 p.2 := by
  have h : ∑ i, n i = n 0 + n 1 := CapFactor.two_sum n
  set θ : Sm E (n 0) := ∑ i, (q i).1 p.2 • b i with hθ
  have key := qdet_slice h τ 0 (w + ((n 0 : ℂ) - 1) / 2) G (CapFactor.levPair p) θ (fun y => by
    rw [update_levPair_zero, ← CapFactor.lev_eq_leviEmb n h, hG]
    simp [hθ, Finset.sum_apply, mul_comm])
  have e1 : (fun p q : Fin (n 0) => Eop (a := n 0 + n 1) τ (stdBlocks n h ⟨0, p⟩) (stdBlocks n h ⟨0, q⟩)) =
      fun p q => Eop (a := n 0 + n 1) τ (Fin.castAdd (n 1) p) (Fin.castAdd (n 1) q) := by
    funext p q
    rw [CapFactor.std_zero, CapFactor.std_zero]
  rw [e1, ← CapFactor.lev_eq_leviEmb n h] at key
  change (capR (n 0) (n 1) τ w G).1 _ = (cap τ w θ).1 p.1 at key
  rw [key, hθ, map_sum]
  simp [Finset.sum_apply, mul_comm]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact.

Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem capS_expand {n : Fin 2 → ℕ} (τ : E →+* ℂ) (w : ℂ) (G : Sm E (n 0 + n 1)) {k : ℕ}
    (b : Fin k → Sm E (n 0)) (q : Fin k → Sm E (n 1))
    (hG : ∀ p, G.1 (lev (Ad E) (n 0) (n 1) p) = ∑ i, (b i).1 p.1 * (q i).1 p.2) (p : GA E (n 0) × GA E (n 1)) :
    (capS (n 0) (n 1) τ w G).1 (lev (Ad E) (n 0) (n 1) p) = ∑ i, (b i).1 p.1 * (cap τ w (q i)).1 p.2 := by
  have h : ∑ i, n i = n 0 + n 1 := CapFactor.two_sum n
  set θ : Sm E (n 1) := ∑ i, (b i).1 p.1 • q i with hθ
  have key := qdet_slice h τ 1 (w + ((n 1 : ℂ) - 1) / 2) G (CapFactor.levPair p) θ (fun y => by
    rw [update_levPair_one, ← CapFactor.lev_eq_leviEmb n h, hG]
    simp [hθ, Finset.sum_apply])
  have e1 : (fun p q : Fin (n 1) => Eop (a := n 0 + n 1) τ (stdBlocks n h ⟨1, p⟩) (stdBlocks n h ⟨1, q⟩)) =
      fun p q => Eop (a := n 0 + n 1) τ (Fin.natAdd (n 0) p) (Fin.natAdd (n 0) q) := by
    funext p q
    rw [CapFactor.std_one, CapFactor.std_one]
  rw [e1, ← CapFactor.lev_eq_leviEmb n h] at key
  change (capS (n 0) (n 1) τ w G).1 _ = (cap τ w θ).1 p.2 at key
  rw [key, hθ, map_sum]
  simp [Finset.sum_apply]

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockCapelli

end
