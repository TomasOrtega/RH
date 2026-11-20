import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.ZNClosed
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.CentralizerRepresentatives.Imports
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.CentralizerRepresentatives.GradeColMatMulVec
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.CentralizerRepresentatives.ExistsEquivLs

noncomputable section

open Matrix GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil

namespace PositivityTheory.RgUd.T.Nil.Orb.BReps

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Unfold `Reps`. Introduce `n Z hZ c hc`. Take `⟨hcomm, hred⟩` from `hZ`. Take `⟨M, hM, L, hLf, hL, R, o, hF⟩` from `exists_frames Z hcomm hred`. Establish `hcZ : ∀ a ∈ Z, a * c = c * a` using `fun a ha => hcomm a ha c hc`.

Establish `hN : ∀ x ∈ Bz Z, ∀ z ∈ Z, z * (x - c) = (x - c) * z`. Introduce `x hx z hz`. Rewrite using `[mul_sub, sub_mul, hx z hz, hcZ z hz]`. Set `S : Type` to `{p : Sp k n // p.1 ∈ Bz Z ∧ IsNilpotent (p.1 - c) ∧ p.2 ≠ 0}`. Set `F : (p : S) → Frame Z M L R o (p.1.1 - c) p.1.2` to `fun p => Classical.choice (hF _ (hN _ p.2.1) p.2.2.1 p.1.2)`.

Establish `hb : ∀ (p : S) (m : M) (ℓ σ : ℕ), Nat.card {a : (F p).ι m // (F p).l m a = ℓ ∧ (F p).s m a = σ} < n + 1`. Introduce `p m ℓ σ`. Use `haveI := (F p).fι m`. Conclude with `Nat.lt_succ_of_le ((Finite.card_subtype_le _).trans ((F p).card_le m))`. Set `τ : S → M → Fin (n + 1) → Fin (n + 1) → Fin (n + 1)` to `fun p m ℓ σ => ⟨Nat.card {a : (F p).ι m // (F p).l m a = ℓ.1 ∧ (F p).s m a = σ.1}, hb p m ℓ σ⟩`.

Establish `hrep : ∀ t : Set.range τ, ∃ p : S, τ p = t.1` using `fun t => t.2`. Set `rep : Set.range τ → S` to `fun t => Classical.choose (hrep t)`. Establish `hrepτ : ∀ t, τ (rep t) = t.1` using `fun t => Classical.choose_spec (hrep t)`. Use `⟨(Set.finite_range (fun t : Set.range τ => (rep t).1)).toFinset, ?_, ?_⟩` and prove the remaining obligations. Introduce `p hp`.

Rewrite `hp` using `[Set.Finite.mem_toFinset]`. Take `⟨t, rfl⟩` from `hp`. Take `⟨h1, h2, h3⟩` from `(rep t).2`. Take `⟨P, w, hPw, hu⟩` from `grade_of_frame (F (rep t))`. Use `⟨h1, h2, h3, P, w, hPw, ?_⟩` and prove the remaining obligations.

Introduce `a haZ hax`. Apply `hu a haZ` to reduce the goal to its premises. Establish `hac : a * c = c * a` using `(haZ c hc).symm`. Rewrite using `[mul_sub, sub_mul, hac]`. Use `show a * (rep t).1.1 - c * a = (rep t).1.1 * a - c * a`.

Rewrite using `[hax]`. Introduce `x hx hnil v hv`. Set `q : S` to `⟨(x, v), hx, hnil, hv⟩`. Set `t : Set.range τ` to `⟨τ q, q, rfl⟩`. Use `⟨(rep t).1, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Set.Finite.mem_toFinset]`. Conclude with `⟨t, rfl⟩`. Establish `he : τ (rep t) = τ q` using `hrepτ t`. Take `⟨g, hgZ, hgN, hgv⟩` from `conj_of_frames (F (rep t)) (F q) (by`. Introduce `m ℓ σ hℓ hσ`.

Conclude with `congrArg (fun f => (f m ⟨ℓ, Nat.lt_succ_of_le hℓ⟩ ⟨σ, Nat.lt_succ_of_le hσ⟩).1) he)`. Use `⟨g, hgZ, ?_⟩` and prove the remaining obligations. Establish `hgc : (g : Matrix (Fin n) (Fin n) k) * c = c * g` using `(hgZ c hc).symm`. Establish `key : (g : Matrix (Fin n) (Fin n) k) * (rep t).1.1 = x * g`. Establish `h` using `hgN`.

Simplify using `only [mul_sub, sub_mul] at h`. Rewrite `h` using `[hgc]`. Simplify using `using h`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Use `show (g : Matrix (Fin n) (Fin n) k) * (rep t).1.1 * ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = x`.

Rewrite using `[key, mul_assoc, Units.mul_inv, mul_one]`. Conclude with `hgv`.
-/
theorem reps [CharZero k] : Reps (k := k) := by
  unfold Reps
  intro n Z hZ c hc
  obtain ⟨hcomm, hred⟩ := hZ
  obtain ⟨M, hM, L, hLf, hL, R, o, hF⟩ := exists_frames Z hcomm hred
  classical
  have hcZ : ∀ a ∈ Z, a * c = c * a := fun a ha => hcomm a ha c hc
  have hN : ∀ x ∈ Bz Z, ∀ z ∈ Z, z * (x - c) = (x - c) * z := by
    intro x hx z hz
    rw [mul_sub, sub_mul, hx z hz, hcZ z hz]
  let S : Type := {p : Sp k n // p.1 ∈ Bz Z ∧ IsNilpotent (p.1 - c) ∧ p.2 ≠ 0}
  let F : (p : S) → Frame Z M L R o (p.1.1 - c) p.1.2 := fun p =>
    Classical.choice (hF _ (hN _ p.2.1) p.2.2.1 p.1.2)
  have hb : ∀ (p : S) (m : M) (ℓ σ : ℕ),
      Nat.card {a : (F p).ι m // (F p).l m a = ℓ ∧ (F p).s m a = σ} < n + 1 := by
    intro p m ℓ σ
    haveI := (F p).fι m
    exact Nat.lt_succ_of_le ((Finite.card_subtype_le _).trans ((F p).card_le m))
  let τ : S → M → Fin (n + 1) → Fin (n + 1) → Fin (n + 1) := fun p m ℓ σ =>
    ⟨Nat.card {a : (F p).ι m // (F p).l m a = ℓ.1 ∧ (F p).s m a = σ.1}, hb p m ℓ σ⟩
  have hrep : ∀ t : Set.range τ, ∃ p : S, τ p = t.1 := fun t => t.2
  let rep : Set.range τ → S := fun t => Classical.choose (hrep t)
  have hrepτ : ∀ t, τ (rep t) = t.1 := fun t => Classical.choose_spec (hrep t)
  refine ⟨(Set.finite_range (fun t : Set.range τ => (rep t).1)).toFinset, ?_, ?_⟩
  · intro p hp
    rw [Set.Finite.mem_toFinset] at hp
    obtain ⟨t, rfl⟩ := hp
    obtain ⟨h1, h2, h3⟩ := (rep t).2
    obtain ⟨P, w, hPw, hu⟩ := grade_of_frame (F (rep t))
    refine ⟨h1, h2, h3, P, w, hPw, ?_⟩
    intro a haZ hax
    apply hu a haZ
    have hac : a * c = c * a := (haZ c hc).symm
    rw [mul_sub, sub_mul, hac]
    show a * (rep t).1.1 - c * a = (rep t).1.1 * a - c * a
    rw [hax]
  · intro x hx hnil v hv
    let q : S := ⟨(x, v), hx, hnil, hv⟩
    let t : Set.range τ := ⟨τ q, q, rfl⟩
    refine ⟨(rep t).1, ?_, ?_⟩
    · rw [Set.Finite.mem_toFinset]
      exact ⟨t, rfl⟩
    · have he : τ (rep t) = τ q := hrepτ t
      obtain ⟨g, hgZ, hgN, hgv⟩ := conj_of_frames (F (rep t)) (F q) (by
        intro m ℓ σ hℓ hσ
        exact congrArg (fun f => (f m ⟨ℓ, Nat.lt_succ_of_le hℓ⟩ ⟨σ, Nat.lt_succ_of_le hσ⟩).1) he)
      refine ⟨g, hgZ, ?_⟩
      have hgc : (g : Matrix (Fin n) (Fin n) k) * c = c * g := (hgZ c hc).symm
      have key : (g : Matrix (Fin n) (Fin n) k) * (rep t).1.1 = x * g := by
        have h := hgN
        simp only [mul_sub, sub_mul] at h
        rw [hgc] at h
        simpa using h
      refine Prod.ext ?_ ?_
      · show (g : Matrix (Fin n) (Fin n) k) * (rep t).1.1 * ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = x
        rw [key, mul_assoc, Units.mul_inv, mul_one]
      · exact hgv

end PositivityTheory.RgUd.T.Nil.Orb.BReps
