import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridFirstColumnSpaceRankSignatureSelfDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinitePrimeSetAvoidingGridPlacesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterUnramifiedOffFinitePrimesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrthonormalBasisSplitSupportedAdelicPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridTopVertexFramePointTransportLatticeStatement

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FunObj

/- English proof (translation)
Break down `X with ⟨i, j⟩ | i | j` into its components or cases. Take `⟨hi, rfl⟩` from `hX`. Break down `i with _ | i` into its components or cases. Establish `h` using `colY_isV D T L μ0 hL D.R.m le_rfl`. Rewrite `h` using `[Nat.sub_self, Nat.zero_div]`.

Conclude with `h`. Establish `h` using `G.isV (X := .grid (i + 1) D.R.m) ⟨hi, le_rfl⟩ (fun j h => by cases h)`. Simplify using `only [Node.neg, Nat.sub_self, Nat.zero_div] at h`. Conclude with `h`. Conclude with `absurd hX id`.

Conclude with `G.isV (X := .top j) hX (fun j' h => by cases h)`.
-/
theorem defNode_isV {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (μ0 : T) (hL : L.Is μ0)
    (X : Node) (hX : DefNode D.R.m X) : (G.node X).IsV (X.rank D) 0 := by
  rcases X with ⟨i, j⟩ | i | j
  · obtain ⟨hi, rfl⟩ := hX
    rcases i with _ | i
    · have h := colY_isV D T L μ0 hL D.R.m le_rfl
      rw [Nat.sub_self, Nat.zero_div] at h
      exact h
    · have h := G.isV (X := .grid (i + 1) D.R.m) ⟨hi, le_rfl⟩ (fun j h => by cases h)
      simp only [Node.neg, Nat.sub_self, Nat.zero_div] at h
      exact h
  · exact absurd hX id
  · exact G.isV (X := .top j) hX (fun j' h => by cases h)

/- English proof (translation)
Introduce `x h1 h2 h3` and use `by rw [MonoidHom.mul_apply, ha x h1 h2 h3, hb x h1 h2 h3, one_mul]`.
-/
theorem unrIdem_mul {D : D7} {a b : (AE D)ˣ →* Circle} {e : AE D} (ha : UnrIdem a e) (hb : UnrIdem b e) :
    UnrIdem (a * b) e := fun x h1 h2 h3 => by
  rw [MonoidHom.mul_apply, ha x h1 h2 h3, hb x h1 h2 h3, one_mul]

/- English proof (translation)
Introduce `q hq` and use `hw q (h hq)`.
-/
theorem off_mono {D : D7} {S S' : Finset ℕ} (h : S ⊆ S') {w : Pl D.host.E} (hw : Off S' w) : Off S w :=
  fun q hq => hw q (h hq)

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Take `⟨S₁, hS₁p, hS₁⟩` from `GlobalTheory.T.exists_finite_primeSet_avoiding_gridPlaces D T L sc G U hU`. Establish `key : ∀ c : (AE D)ˣ →* Circle, ∃ S : Finset ℕ, (∀ q ∈ S, q.Prime) ∧ (Continuous c → ∀ w : Pl D.host.E, Off S w → ∀ e, Formalism.L2.NTheta.IsIdemAt e w → UnrIdem c e)` using `fun c => by`. Distinguish the cases in `hc : Continuous c`. Take `⟨S, h1, h2⟩` from `GlobalTheory.T.character_unramified_off_finite_primes D c hc`. Conclude with `⟨S, h1, fun _ => h2⟩`.

Conclude with `⟨∅, by simp, fun h => absurd h hc⟩`. Use `choose Sc hScp hSc using key`. Use `set S : Finset ℕ := S₁ ∪ (Finset.range (D.R.m + 1)).biUnion (fun j => Sc (L.mu0 j)) ∪ hU.toFinset.biUnion (fun t => Sc (L.xi t)) with hSdef`. Establish `hSp : ∀ q ∈ S, q.Prime`. Introduce `q hq`.

Simplify using `only [hSdef, Finset.mem_union, Finset.mem_biUnion] at hq`. Break down `hq with (hq | ⟨j, -, hq⟩) | ⟨t, -, hq⟩` into its components or cases. Conclude with `hS₁p q hq`. Conclude with `hScp _ q hq`. Conclude with `hScp _ q hq`.

Establish `hsub1 : S₁ ⊆ S` using `fun q hq => by simp [hSdef, hq]`. Establish `hsubμ : ∀ j, j ≤ D.R.m → Sc (L.mu0 j) ⊆ S` using `fun j hj q hq => by`. Simplify using `only [hSdef, Finset.mem_union, Finset.mem_biUnion, Finset.mem_range]`. Conclude with `Or.inl (Or.inr ⟨j, by omega, hq⟩)`. Establish `hsubξ : ∀ t ∈ U, Sc (L.xi t) ⊆ S` using `fun t ht q hq => by`.

Simplify using `only [hSdef, Finset.mem_union, Finset.mem_biUnion, Set.Finite.mem_toFinset]`. Conclude with `Or.inr ⟨t, ht, hq⟩`. Establish `hcμ : ∀ j, 1 ≤ j → j ≤ D.R.m → Continuous (L.mu0 j)` using `fun j h1 h2 => by`. Take `⟨k, rfl⟩ : ∃ k, j = k + 1` from `⟨j - 1, by omega⟩`. Conclude with `(hL.mu0 ⟨k, by omega⟩).1.1`.

Establish `hV : ∀ X, DefNode D.R.m X → ∃ (fr : GL (Fin (G.V X).rank) D.host.E) (u : FinPt G X), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr.1 * (G.V X).gram * fr.1 = 1 ∧ (∃ (P : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e P ∧ SuppAt e _ u.1 ∧ ∀ w ∈ P, Off S w) ∧ ∀ v, v ∈ Form …` using `D.host.F) (colLat fr) ↔ (Formalism.IndefR.Lev.finE (G.V X) u.1).1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ X) := by`. Introduce `X hX`. Establish `h` using `defNode_isV G μ0 hL X hX`. Conclude with `GlobalTheory.T.exists_orthonormalBasis_splitSupported_adelicPoint D (G.V X) (G.Λ X) h.sigOK (fun τ => by rw [h.sig τ, h.rank, Nat.sub_zero]) h.sd S hSp`. Use `choose fr0 u0 h0 using hV`.

Establish `hmm : DefNode D.R.m (.grid D.R.m D.R.m)` using `⟨le_rfl, rfl⟩`. Take `⟨frT, uT, hT1, hT2, hT3, hT4, hT5, hT6, hT7⟩` from `GlobalTheory.T.gridTopVertex_frame_point_transport_lattice D T L sc G S (fr0 _ hmm) (u0 _ hmm) (h0 _ hmm).1 (h0 _ hmm).2.1 (h0 _ hmm).2.2`. Establish `hne : (Node.grid D.R.m D.R.m) ≠ Node.top D.R.m` using `fun h => by cases h`. Take `⟨fr, frt, hfr⟩ : ∃ fr : ∀ X : Node, GL (Fin (G.V X).rank) D.host.E, fr (.top D.R.m) = frT ∧ ∀ X (hX : DefNode D.R.m X), X ≠ .top D.R.m → fr X = fr0 X hX` from `⟨Function.update (fun X => if h : DefNode D.R.m X then fr0 X h else 1) (.top D.R.m) frT, Function.update_self _ _ _, fun X hX hXt => by rw [Function.update_of_ne hXt, dif_pos hX]⟩`. Take `⟨u, ut, hu⟩ : ∃ u : ∀ X : Node, FinPt G X, u (.top D.R.m) = uT ∧ ∀ X (hX : DefNode D.R.m X), X ≠ .top D.R.m → u X = u0 X hX` from `⟨Function.update (fun X => if h : DefNode D.R.m X then u0 X h else 1) (.top D.R.m) uT, Function.update_self _ _ _, fun X hX hXt => by rw [Function.update_of_ne hXt, dif_pos hX]⟩`.

Establish `frmm` using `hfr _ hmm hne`. Establish `hu_mm` using `hu _ hmm hne`. Use `⟨⟨S, hSp, ?_, ?_, fr, ?_, u, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩` and prove the remaining obligations. Conclude with `fun w hw => hS₁ w (off_mono hsub1 hw)`. Introduce `w hw e he t ht j h1 h2`.

Conclude with `unrIdem_mul (hSc _ (hcμ j h1 h2) w (off_mono (hsubμ j h2) hw) e he) (hSc _ (hL.xi t).1.1 w (off_mono (hsubξ t ht) hw) e he)`. Introduce `X hX`. Distinguish the cases in `hXt : X = .top D.R.m`. Substitute `hXt` using the available equality. Rewrite using `[frt]`.

Conclude with `hT1`. Use `hfr X hX hXt` as an intermediate fact. Rewrite using `[this]`. Conclude with `(h0 X hX).1`. Introduce `X hX`.

Distinguish the cases in `hXt : X = .top D.R.m`. Substitute `hXt` using the available equality. Rewrite using `[ut]`. Conclude with `hT2`. Use `hu X hX hXt` as an intermediate fact.

Rewrite using `[this]`. Conclude with `(h0 X hX).2.1`. Introduce `X hX`. Distinguish the cases in `hXt : X = .top D.R.m`. Substitute `hXt` using the available equality.

Rewrite using `[frt, ut]`. Conclude with `hT3`. Establish `e1` using `hfr X hX hXt`. Establish `e2` using `hu X hX hXt`. Rewrite using `[e1, e2]`.

Conclude with `(h0 X hX).2.2`. Introduce `i k`. Rewrite using `[frt, frmm]`. Conclude with `hT4 i k`. Introduce `i`.

Rewrite using `[frt]`. Conclude with `hT5 i`. Rewrite using `[ut, hu_mm]`. Conclude with `hT6`. Rewrite using `[ut]`.

Conclude with `hT7`.
-/
theorem exists_std {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (μ0 : T) (hL : L.Is μ0)
    (U : Set T) (hU : U.Finite) : Nonempty (Std G U) := by
  classical
  obtain ⟨S₁, hS₁p, hS₁⟩ := GlobalTheory.T.exists_finite_primeSet_avoiding_gridPlaces D T L sc G U hU
  have key : ∀ c : (AE D)ˣ →* Circle, ∃ S : Finset ℕ, (∀ q ∈ S, q.Prime) ∧
      (Continuous c → ∀ w : Pl D.host.E, Off S w → ∀ e, Formalism.L2.NTheta.IsIdemAt e w → UnrIdem c e) := fun c => by
    by_cases hc : Continuous c
    · obtain ⟨S, h1, h2⟩ := GlobalTheory.T.character_unramified_off_finite_primes D c hc
      exact ⟨S, h1, fun _ => h2⟩
    · exact ⟨∅, by simp, fun h => absurd h hc⟩
  choose Sc hScp hSc using key
  set S : Finset ℕ := S₁ ∪ (Finset.range (D.R.m + 1)).biUnion (fun j => Sc (L.mu0 j)) ∪
    hU.toFinset.biUnion (fun t => Sc (L.xi t)) with hSdef
  have hSp : ∀ q ∈ S, q.Prime := by
    intro q hq
    simp only [hSdef, Finset.mem_union, Finset.mem_biUnion] at hq
    rcases hq with (hq | ⟨j, -, hq⟩) | ⟨t, -, hq⟩
    · exact hS₁p q hq
    · exact hScp _ q hq
    · exact hScp _ q hq
  have hsub1 : S₁ ⊆ S := fun q hq => by simp [hSdef, hq]
  have hsubμ : ∀ j, j ≤ D.R.m → Sc (L.mu0 j) ⊆ S := fun j hj q hq => by
    simp only [hSdef, Finset.mem_union, Finset.mem_biUnion, Finset.mem_range]
    exact Or.inl (Or.inr ⟨j, by omega, hq⟩)
  have hsubξ : ∀ t ∈ U, Sc (L.xi t) ⊆ S := fun t ht q hq => by
    simp only [hSdef, Finset.mem_union, Finset.mem_biUnion, Set.Finite.mem_toFinset]
    exact Or.inr ⟨t, ht, hq⟩
  have hcμ : ∀ j, 1 ≤ j → j ≤ D.R.m → Continuous (L.mu0 j) := fun j h1 h2 => by
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    exact (hL.mu0 ⟨k, by omega⟩).1.1
  have hV : ∀ X, DefNode D.R.m X → ∃ (fr : GL (Fin (G.V X).rank) D.host.E) (u : FinPt G X),
      Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr.1 * (G.V X).gram * fr.1 = 1 ∧
      (∃ (P : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e P ∧ SuppAt e _ u.1 ∧ ∀ w ∈ P, Off S w) ∧
      ∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr) ↔
        (Formalism.IndefR.Lev.finE (G.V X) u.1).1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ X) := by
    intro X hX
    have h := defNode_isV G μ0 hL X hX
    exact GlobalTheory.T.exists_orthonormalBasis_splitSupported_adelicPoint D (G.V X) (G.Λ X) h.sigOK (fun τ => by rw [h.sig τ, h.rank, Nat.sub_zero]) h.sd S hSp
  choose fr0 u0 h0 using hV
  have hmm : DefNode D.R.m (.grid D.R.m D.R.m) := ⟨le_rfl, rfl⟩
  obtain ⟨frT, uT, hT1, hT2, hT3, hT4, hT5, hT6, hT7⟩ :=
    GlobalTheory.T.gridTopVertex_frame_point_transport_lattice D T L sc G S (fr0 _ hmm) (u0 _ hmm) (h0 _ hmm).1 (h0 _ hmm).2.1 (h0 _ hmm).2.2
  have hne : (Node.grid D.R.m D.R.m) ≠ Node.top D.R.m := fun h => by cases h
  obtain ⟨fr, frt, hfr⟩ : ∃ fr : ∀ X : Node, GL (Fin (G.V X).rank) D.host.E, fr (.top D.R.m) = frT ∧
      ∀ X (hX : DefNode D.R.m X), X ≠ .top D.R.m → fr X = fr0 X hX :=
    ⟨Function.update (fun X => if h : DefNode D.R.m X then fr0 X h else 1) (.top D.R.m) frT,
      Function.update_self _ _ _, fun X hX hXt => by rw [Function.update_of_ne hXt, dif_pos hX]⟩
  obtain ⟨u, ut, hu⟩ : ∃ u : ∀ X : Node, FinPt G X, u (.top D.R.m) = uT ∧
      ∀ X (hX : DefNode D.R.m X), X ≠ .top D.R.m → u X = u0 X hX :=
    ⟨Function.update (fun X => if h : DefNode D.R.m X then u0 X h else 1) (.top D.R.m) uT,
      Function.update_self _ _ _, fun X hX hXt => by rw [Function.update_of_ne hXt, dif_pos hX]⟩
  have frmm := hfr _ hmm hne
  have hu_mm := hu _ hmm hne
  refine ⟨⟨S, hSp, ?_, ?_, fr, ?_, u, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact fun w hw => hS₁ w (off_mono hsub1 hw)
  · intro w hw e he t ht j h1 h2
    exact unrIdem_mul (hSc _ (hcμ j h1 h2) w (off_mono (hsubμ j h2) hw) e he)
      (hSc _ (hL.xi t).1.1 w (off_mono (hsubξ t ht) hw) e he)
  · intro X hX
    by_cases hXt : X = .top D.R.m
    · subst hXt; rw [frt]; exact hT1
    · have := hfr X hX hXt
      rw [this]; exact (h0 X hX).1
  · intro X hX
    by_cases hXt : X = .top D.R.m
    · subst hXt; rw [ut]; exact hT2
    · have := hu X hX hXt
      rw [this]; exact (h0 X hX).2.1
  · intro X hX
    by_cases hXt : X = .top D.R.m
    · subst hXt; rw [frt, ut]; exact hT3
    · have e1 := hfr X hX hXt
      have e2 := hu X hX hXt
      rw [e1, e2]; exact (h0 X hX).2.2
  · intro i k; rw [frt, frmm]; exact hT4 i k
  · intro i; rw [frt]; exact hT5 i
  · rw [ut, hu_mm]; exact hT6
  · rw [ut]; exact hT7

end GlobalTheory.FunObj
