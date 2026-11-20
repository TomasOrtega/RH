import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CMTypeEmbeddings

noncomputable section

namespace GlobalTheory.Survey.EmbeddingValuationsAnti

open Formalism.BasicNotions Formalism.MainNotions.N Formalism.L2.Host NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings GlobalTheory.HeightCounting

/- English proof (translation)
Establish `hk` using `R.m_add_three_le_k`. Establish `step : ∀ (n : ℕ) (h : n + 1 < R.k - 1), P.v ⟨n + 1, h⟩ < P.v ⟨n, by omega⟩` using `fun n h => (P.u_gt_v ⟨n + 1, h⟩).trans (P.v_gt_u ⟨n, by omega⟩)`. Establish `key : ∀ (d n : ℕ) (h : n + d + 1 < R.k - 1), P.v ⟨n + d + 1, h⟩ < P.v ⟨n, by omega⟩`. Introduce `d`. Proceed by induction on `d with`.

Consider the case `zero => intro n h`. Conclude with `step n h`. Consider the case `succ d ih => intro n h; exact (step (n + d + 1) (by omega)).trans (ih n (by omega))`. Introduce `a b hab`. Take `⟨a, ha⟩` from `a`.

Take `⟨b, hb⟩` from `b`. Establish `: a < b` using `hab`. Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_lt this`. Conclude with `key d a hb`.
-/
theorem v_strictAnti {R : Ranks} (P : HCParam R) : StrictAnti P.v := by
  have hk := R.m_add_three_le_k
  have step : ∀ (n : ℕ) (h : n + 1 < R.k - 1), P.v ⟨n + 1, h⟩ < P.v ⟨n, by omega⟩ := fun n h =>
    (P.u_gt_v ⟨n + 1, h⟩).trans (P.v_gt_u ⟨n, by omega⟩)
  have key : ∀ (d n : ℕ) (h : n + d + 1 < R.k - 1), P.v ⟨n + d + 1, h⟩ < P.v ⟨n, by omega⟩ := by
    intro d
    induction d with
    | zero => intro n h; exact step n h
    | succ d ih => intro n h; exact (step (n + d + 1) (by omega)).trans (ih n (by omega))
  intro a b hab
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  have : a < b := hab
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt this
  exact key d a hb

/- English proof (translation)
Establish `ht : (0 : ℚ) < ((R.t : ℚ) + 3) / 2` using `by positivity`. Establish `step : ∀ (n : ℕ) (h : n + 1 < R.m), P.b ⟨n, by omega⟩ < P.b ⟨n + 1, h⟩` using `fun n h => by`. Establish `h1` using `P.gap_be ⟨n, by omega⟩`. Establish `h2` using `P.gap_eb ⟨n, by omega⟩ h`. Simplify using `only at h2`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `key : ∀ (d n : ℕ) (h : n + d + 1 < R.m), P.b ⟨n, by omega⟩ < P.b ⟨n + d + 1, h⟩`. Introduce `d`. Proceed by induction on `d with`. Consider the case `zero => intro n h`.

Conclude with `step n h`. Consider the case `succ d ih => intro n h; exact (ih n (by omega)).trans (step (n + d + 1) (by omega))`. Introduce `a b hab`. Take `⟨a, ha⟩` from `a`. Take `⟨b, hb⟩` from `b`.

Establish `: a < b` using `hab`. Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_lt this`. Conclude with `key d a hb`.
-/
theorem b_strictMono {R : Ranks} (P : HCParam R) : StrictMono P.b := by
  have ht : (0 : ℚ) < ((R.t : ℚ) + 3) / 2 := by positivity
  have step : ∀ (n : ℕ) (h : n + 1 < R.m), P.b ⟨n, by omega⟩ < P.b ⟨n + 1, h⟩ := fun n h => by
    have h1 := P.gap_be ⟨n, by omega⟩
    have h2 := P.gap_eb ⟨n, by omega⟩ h
    simp only at h2
    linarith
  have key : ∀ (d n : ℕ) (h : n + d + 1 < R.m), P.b ⟨n, by omega⟩ < P.b ⟨n + d + 1, h⟩ := by
    intro d
    induction d with
    | zero => intro n h; exact step n h
    | succ d ih => intro n h; exact (ih n (by omega)).trans (step (n + d + 1) (by omega))
  intro a b hab
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  have : a < b := hab
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt this
  exact key d a hb

/- English proof (translation)
Establish `hk` using `R.m_add_three_le_k`. Establish `hm` using `R.two_le_m`. Establish `h1` using `P.u_last_gt (by omega) (by omega)`. Establish `h2 : P.u ⟨R.k - 1, by omega⟩ < P.v ⟨R.k - 2, by omega⟩`. Use `P.v_gt_u ⟨R.k - 2, by omega⟩` as an intermediate fact.

Establish `e : (⟨R.k - 2 + 1, by omega⟩ : Fin R.k) = ⟨R.k - 1, by omega⟩` using `Fin.ext (by simp; omega)`. Simplify `this` using `[e]`. Establish `h3 : P.v ⟨R.k - 2, by omega⟩ ≤ P.v i` using `(v_strictAnti P).antitone (by`. Use `i.2` as an intermediate fact. Use `show i.1 ≤ R.k - 2`.

Use the proof step `omega)`. Establish `h4 : P.b ⟨0, by omega⟩ ≤ P.b j` using `(b_strictMono P).monotone (by show 0 ≤ j.1; omega)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem neg_b_lt_v {R : Ranks} (P : HCParam R) (i : Fin (R.k - 1)) (j : Fin R.m) : -P.b j < P.v i := by
  have hk := R.m_add_three_le_k
  have hm := R.two_le_m
  have h1 := P.u_last_gt (by omega) (by omega)
  have h2 : P.u ⟨R.k - 1, by omega⟩ < P.v ⟨R.k - 2, by omega⟩ := by
    have := P.v_gt_u ⟨R.k - 2, by omega⟩
    have e : (⟨R.k - 2 + 1, by omega⟩ : Fin R.k) = ⟨R.k - 1, by omega⟩ := Fin.ext (by simp; omega)
    simpa [e] using this
  have h3 : P.v ⟨R.k - 2, by omega⟩ ≤ P.v i := (v_strictAnti P).antitone (by
    have := i.2; show i.1 ≤ R.k - 2; omega)
  have h4 : P.b ⟨0, by omega⟩ ≤ P.b j := (b_strictMono P).monotone (by show 0 ≤ j.1; omega)
  linarith

/- English proof (translation)
Unfold `hcSigma`. Rewrite using `[Multiset.nodup_add]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Use `Multiset.Nodup.map (fun a b h => (v_strictAnti P).injective ?_) Finset.univ.nodup` and prove the remaining obligations. Conclude with `h` after adjusting the coercions.

Use `Multiset.Nodup.map (fun a b h => (b_strictMono P).injective ?_) Finset.univ.nodup` and prove the remaining obligations. Use `neg_injective h` as an intermediate fact. Conclude with `this` after adjusting the coercions. Rewrite using `[Multiset.disjoint_left]`. Introduce `z h1 h2`.

Take `⟨i, -, rfl⟩` from `Multiset.mem_map.1 h1`. Take `⟨j, -, hj⟩` from `Multiset.mem_map.1 h2`. Establish `: -P.b j = P.v i` using `by exact_mod_cast hj`. Conclude with `(neg_b_lt_v P i j).ne this`.
-/
theorem nodup_hcSigma {R : Ranks} (P : HCParam R) : (hcSigma P).Nodup := by
  unfold hcSigma
  rw [Multiset.nodup_add]
  refine ⟨?_, ?_, ?_⟩
  · refine Multiset.Nodup.map (fun a b h => (v_strictAnti P).injective ?_) Finset.univ.nodup
    exact_mod_cast h
  · refine Multiset.Nodup.map (fun a b h => (b_strictMono P).injective ?_) Finset.univ.nodup
    have := neg_injective h
    exact_mod_cast this
  · rw [Multiset.disjoint_left]
    intro z h1 h2
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 h1
    obtain ⟨j, -, hj⟩ := Multiset.mem_map.1 h2
    have : -P.b j = P.v i := by exact_mod_cast hj
    exact (neg_b_lt_v P i j).ne this

/- English proof (translation)
Introduce `g g' h`. Establish `h1 : D.host.sigmaOf g = D.host.sigmaOf g'` using `AlgEquiv.ext fun x => D.host.φ₀.injective (RingHom.congr_fun h x)`. Conclude with `(D.host.gal).symm.injective h1`.
-/
theorem emb_injective (D : D7) : Function.Injective D.host.emb := by
  intro g g' h
  have h1 : D.host.sigmaOf g = D.host.sigmaOf g' :=
    AlgEquiv.ext fun x => D.host.φ₀.injective (RingHom.congr_fun h x)
  exact (D.host.gal).symm.injective h1

/- English proof (translation)
Introduce `_ _ h` and use `D.eTau.injective (Subtype.ext (emb_injective D h))`.
-/
theorem embTau_injective (D : D7) : Function.Injective (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D) := fun _ _ h =>
  D.eTau.injective (Subtype.ext (emb_injective D h))

/- English proof (translation)
Introduce `h`. Establish `hc : embTauBar D τ = D.host.emb (D.R.cc * (D.eTau τ : D.R.GG))`. Use `RingHom.ext fun x => ?_` and prove the remaining obligations. Simplify using `only [embTauBar, GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau, embPsi, Formalism.BasicNotions.Host.emb, Formalism.BasicNotions.Host.sigmaOf, RingHom.comp_apply, map_mul]`. Rewrite using `[← D.host.conjE_apply D.host.φ₀]`.

Both sides reduce to the same expression. Rewrite `h` using `[hc]`. Establish `h1` using `emb_injective D h`. Establish `hn : D.R.cc ∉ D.R.Psi`. Rewrite using `[Formalism.HC.Frame.mem_Psi_iff]`.

Simplify using `[Formalism.HC.Frame.cc, Formalism.FrobeniusOrbits.c0]`. Apply `hn` to reduce the goal to its premises. Establish `h2 : D.R.cc = ((D.eTau τ' : D.R.Psi) : D.R.GG) * ((D.eTau τ : D.R.Psi) : D.R.GG)⁻¹`. Rewrite using `[← h1]`. Use `group`.

Rewrite using `[h2]`. Conclude with `(D.R.Psi).mul_mem (D.eTau τ').2 ((D.R.Psi).inv_mem (D.eTau τ).2)`.
-/
theorem embTau_ne_bar (D : D7) (τ τ' : D.what₂.Tau) : embTauBar D τ ≠ GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ' := by
  intro h
  have hc : embTauBar D τ = D.host.emb (D.R.cc * (D.eTau τ : D.R.GG)) := by
    refine RingHom.ext fun x => ?_
    simp only [embTauBar, GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau, embPsi, Formalism.BasicNotions.Host.emb, Formalism.BasicNotions.Host.sigmaOf, RingHom.comp_apply, map_mul]
    rw [← D.host.conjE_apply D.host.φ₀]
    rfl
  rw [hc] at h
  have h1 := emb_injective D h
  have hn : D.R.cc ∉ D.R.Psi := by
    rw [Formalism.HC.Frame.mem_Psi_iff]
    simp [Formalism.HC.Frame.cc, Formalism.FrobeniusOrbits.c0]
  apply hn
  have h2 : D.R.cc =
      ((D.eTau τ' : D.R.Psi) : D.R.GG) *
        ((D.eTau τ : D.R.Psi) : D.R.GG)⁻¹ := by
    rw [← h1]; group
  rw [h2]
  exact (D.R.Psi).mul_mem (D.eTau τ').2 ((D.R.Psi).inv_mem (D.eTau τ).2)

open Classical in

def perturbedSide {D : D7} (S : RowSide D) : RowSide D where
  locR σ w := if ∃ k v, D.naut.plGw k v = w then S.locR σ w else D.naut.lpZero w
  satR := S.satR
  lab_eq k σ v := by rw [if_pos ⟨k, v, rfl⟩]; exact S.lab_eq k σ v

def LabelsOnly (D : D7) (σ : D.what₂.FT) (π : D.naut.CG D.R.r) : Prop :=
  D.naut.csd π ∧ D.naut.ralg π ∧
  (∀ k v, D.nd.lab k σ v = D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG π (D.naut.plGw k v))) ∧
  (∀ w : PlE D.host, ¬ IsSplitPl D.host w → D.naut.unr (D.naut.locG π w)) ∧
  (∀ w : PlE D.host, IsSplitPl D.host w → (∀ k : Fin 2, w ∉ placesOver D.host.E (D.host.g k)) →
    D.naut.unr (D.naut.locG π w)) ∧
  (∀ τ : D.what₂.Tau, D.naut.infG π (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ) = hcSigma (D.hc τ) ∧
    D.naut.infG π (embTauBar D τ) = (hcSigma (D.hc τ)).map (fun z => -z))

end GlobalTheory.Survey.EmbeddingValuationsAnti

end
