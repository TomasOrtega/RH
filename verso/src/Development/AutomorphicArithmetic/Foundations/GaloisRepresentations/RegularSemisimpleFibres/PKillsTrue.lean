import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.SuppBCOfMix
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsInCharacterIsotypicPartSelf

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
private theorem JD_cons' {F : Type} [Field F] (θ : AlgebraicClosure F →* ℂ) (p : ℕ × ℕ) (D L : List (ℕ × ℕ))
    (b n : ℕ) (h : deg D + deg L = b) :
    JD θ (p :: D) L n = hc p.1 b (detc θ p.1 p.2) (JD θ D L b) n := by
  subst h; rfl

/- English proof (translation)
Introduce `x y`. Establish `hd : ((y⁻¹ * x * y : GL (Fin t) F) : Matrix (Fin t) (Fin t) F).det = (x : Matrix (Fin t) (Fin t) F).det`. Rewrite using `[Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, mul_comm (Matrix.det ((y⁻¹ : GL (Fin t) F) : Matrix (Fin t) (Fin t) F)), mul_assoc, ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one, mul_one]`. Simplify using `only [detc, hd]`.
-/
private theorem isCl_detc {F : Type} [Field F] (θ : AlgebraicClosure F →* ℂ) (t k : ℕ) : IsCl (detc θ t k) := by
  intro x y
  have hd : ((y⁻¹ * x * y : GL (Fin t) F) : Matrix (Fin t) (Fin t) F).det =
      (x : Matrix (Fin t) (Fin t) F).det := by
    rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul,
      mul_comm (Matrix.det ((y⁻¹ : GL (Fin t) F) : Matrix (Fin t) (Fin t) F)), mul_assoc,
      ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one, mul_one]
  simp only [detc, hd]

/- English proof (translation)
Establish `: Finite F` using `Finite.of_injective _ (algebraMap F F').injective`. Establish `: Fintype F` using `Fintype.ofFinite F`. Establish `hs' : s = FiniteField.frobeniusAlgEquivOfAlgebraic F F'`. Use extensionality with `z`. Simplify using `[hs z, FiniteField.coe_frobeniusAlgEquivOfAlgebraic, Nat.card_eq_fintype_card]`.

Take `⟨n, hn⟩` from `(FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow F F').2 t`. Rewrite using `[hs']`. Conclude with `⟨(n.1 : ℤ), by simpa using hn⟩`.
-/
private theorem gen_of_frob {F F' : Type} [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F')
    (hs : ∀ z, s z = z ^ Nat.card F) (t : F' ≃ₐ[F] F') : t ∈ Subgroup.zpowers s := by
  have : Finite F := Finite.of_injective _ (algebraMap F F').injective
  have : Fintype F := Fintype.ofFinite F
  have hs' : s = FiniteField.frobeniusAlgEquivOfAlgebraic F F' := by
    ext z
    simp [hs z, FiniteField.coe_frobeniusAlgEquivOfAlgebraic, Nat.card_eq_fintype_card]
  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow F F').2 t
  rw [hs']
  exact ⟨(n.1 : ℤ), by simpa using hn⟩

/- English proof (translation)
Establish `: Finite F` using `Finite.of_injective _ (algebraMap F F').injective`. Conclude with `Module.natCard_eq_pow_finrank.symm`.
-/
private theorem card_lift {F F' : Type} [Field F] [Field F'] [Algebra F F'] [Finite F'] :
    Nat.card F ^ Module.finrank F F' = Nat.card F' := by
  have : Finite F := Finite.of_injective _ (algebraMap F F').injective
  exact Module.natCard_eq_pow_finrank.symm

/- English proof (translation)
Establish `hg : ∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s` using `gen_of_frob s hs`. Rewrite using `[JD_cons' (pullθ ι θ) p D L b n h₁, JD_cons' θ _ D' L' b n h₂]`. Rewrite using `[hLH F F' s hg p.1 b n hn _ _ (isCl_detc _ _ _) ((hJE F (pullθ ι θ)).2.2 D L b)]`. Rewrite using `[hLD F F' s hs ι θ p.1 p.2 (hNE F F' s hs p.1)]`. Conclude with `hKH F' (s : F' →+* F') p.1 b n hn _ _ _ _ ((hJC F' θ hθ).1 _ _) hB (kills_self _ _ ((hJC F' θ hθ).1 _ _)) IH`.
-/
private theorem step (hLH : LiftHc) (hKH : KillsHc) (hNE : NormEx) (hJE : JDEq) (hJC : JDChar) (hLD : LiftDet)
    {F F' : Type} [Field F] [Field F'] [Algebra F F'] [Finite F'] [Finite F] (s : F' ≃ₐ[F] F')
    (hs : ∀ z, s z = z ^ Nat.card F) (ι : AlgebraicClosure F →ₐ[F] AlgebraicClosure F')
    (θ : AlgebraicClosure F' →* ℂ) (hθ : Inj θ) (p : ℕ × ℕ) (D L D' L' : List (ℕ × ℕ)) (b n : ℕ)
    (hn : n = p.1 + b) (h₁ : deg D + deg L = b) (h₂ : deg D' + deg L' = b)
    (hB : GlobalTheory.BI.IsChar ℂ ℂ (JD θ D' L' b))
    (IH : Kills (shLift s (JD (pullθ ι θ) D L b)) (JD θ D' L' b)) :
    Kills (shLift s (JD (pullθ ι θ) (p :: D) L n))
      (JD θ ((p.1, p.2 * ∑ i ∈ Finset.range (Module.finrank F F'), Nat.card F ^ i) :: D') L' n) := by
  have hg : ∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s := gen_of_frob s hs
  rw [JD_cons' (pullθ ι θ) p D L b n h₁, JD_cons' θ _ D' L' b n h₂]
  rw [hLH F F' s hg p.1 b n hn _ _ (isCl_detc _ _ _) ((hJE F (pullθ ι θ)).2.2 D L b)]
  rw [hLD F F' s hs ι θ p.1 p.2 (hNE F F' s hs p.1)]
  exact hKH F' (s : F' →+* F') p.1 b n hn _ _ _ _ ((hJC F' θ hθ).1 _ _) hB
    (kills_self _ _ ((hJC F' θ hθ).1 _ _)) IH

/- English proof (translation)
Introduce `h0 hLH hKH hNE hLO hJE hJC hLD F F' _ _ _ _ s hl hs ι θ hθ a _ hok hq`. Establish `: Finite F` using `Finite.of_injective _ (algebraMap F F').injective`. Establish `hlift` using `hLO a (Module.finrank F F') hl hok`. Take `⟨q, D0, L0⟩` from `a`. Express the relevant statement in the definitionally equal form `q = Nat.card F at hq`.

Substitute `hq` using the available equality. Establish `hok'` using `hok`. Unfold `Lbl.Ok at hok'`. Take `⟨hq2, hDpos, hLok⟩` from `hok'`. Establish `hl1` using `hlift.1`.

Unfold `Lbl.Ok at hl1`. Take `⟨hq2', _, hLok'⟩` from `hl1`. Establish `hdegmap : ∀ D : List (ℕ × ℕ), deg (D.map fun p => (p.1, p.2 * ∑ i ∈ Finset.range (Module.finrank F F'), Nat.card F ^ i)) = deg D`. Introduce `D`. Simplify using `[GlobalTheory.Shin.deg, List.map_map, Function.comp_def]`.

Establish `hdegL : deg (liftAll (Nat.card F) (Module.finrank F F') L0) = deg L0`. Establish `h` using `hlift.2`. Simplify using `only [Lbl.rk, Lbl.lift, hdegmap] at h`. Use linear arithmetic over natural numbers and integers. Establish `key : ∀ D : List (ℕ × ℕ), (∀ p ∈ D, 0 < p.1) → Kills (shLift s (JD (pullθ ι θ) D L0 (deg D + deg L0))) (JD θ (D.map fun p => (p.1, p.2 * ∑ i ∈ Finset.range (Module.finrank F F'), Nat.card F ^ i)) (liftAll (Nat.card F) (Module.finrank F F') L0) (deg D + deg L0))`.

Introduce `D`. Proceed by induction on `D with`. Consider the case `nil`. Introduce `_`. Conclude with `h0 F F' s hl hs ι θ hθ ⟨Nat.card F, [], L0⟩ rfl (by unfold Lbl.Ok; exact ⟨hq2, by simp, hLok⟩) rfl`.

Consider the case `cons p D ih`. Introduce `hD`. Establish `hD' : ∀ x ∈ D, 0 < x.1` using `fun x hx => hD x (List.mem_cons_of_mem _ hx)`. Establish `tr : ∀ (D' L' : List (ℕ × ℕ)) (n m : ℕ), n = m → GlobalTheory.BI.IsChar ℂ ℂ (JD θ D' L' n) → GlobalTheory.BI.IsChar ℂ ℂ (JD θ D' L' m)`. Introduce `D' L' n m h`.

Substitute `h` using the available equality. Conclude with `id`. Establish `hB : GlobalTheory.BI.IsChar ℂ ℂ (JD θ (D.map fun p => (p.1, p.2 * ∑ i ∈ Finset.range (Module.finrank F F'), Nat.card F ^ i)) (liftAll (Nat.card F) (Module.finrank F F') L0) (deg D + deg L0))`. Establish `hc` using `(hJC F' θ hθ).2 ⟨Nat.card F ^ Module.finrank F F', D.map fun p => (p.1, p.2 * ∑ i ∈ Finset.range (Module.finrank F F'), Nat.card F ^ i), liftAll (Nat.card F) (Module.finrank F F') L0⟩ (by`. Unfold `Lbl.Ok`.

Use `⟨hq2', ?_, hLok'⟩` and prove the remaining obligations. Introduce `x hx`. Take `⟨y, hy, rfl⟩` from `List.mem_map.1 hx`. Conclude with `hD' y hy) card_lift`. Use `tr _ _ _ _ ?_ hc` and prove the remaining obligations.

Use `show deg _ + deg _ = _`. Rewrite using `[hdegmap, hdegL]`. Conclude with `step hLH hKH hNE hJE hJC hLD s hs ι θ hθ p D L0 _ _ (deg D + deg L0) _ (by simp only [GlobalTheory.Shin.deg, List.map_cons, List.sum_cons]; omega) rfl (by rw [hdegmap, hdegL]) hB (ih hD')`. Conclude with `key D0 hDpos`.
-/
theorem UpperTheory.Gal.InertialTypesAlt.killsTrue :
    (KillsOn fun a => a.D = []) → LiftHc → KillsHc → NormEx → LiftOk → JDEq → JDChar → LiftDet → KillsOn fun _ => True := by
  intro h0 hLH hKH hNE hLO hJE hJC hLD F F' _ _ _ _ s hl hs ι θ hθ a _ hok hq
  have : Finite F := Finite.of_injective _ (algebraMap F F').injective
  have hlift := hLO a (Module.finrank F F') hl hok
  obtain ⟨q, D0, L0⟩ := a
  change q = Nat.card F at hq
  subst hq
  have hok' := hok
  unfold Lbl.Ok at hok'
  obtain ⟨hq2, hDpos, hLok⟩ := hok'
  have hl1 := hlift.1
  unfold Lbl.Ok at hl1
  obtain ⟨hq2', _, hLok'⟩ := hl1
  have hdegmap : ∀ D : List (ℕ × ℕ),
      deg (D.map fun p => (p.1, p.2 * ∑ i ∈ Finset.range (Module.finrank F F'), Nat.card F ^ i)) =
        deg D := by
    intro D
    simp [GlobalTheory.Shin.deg, List.map_map, Function.comp_def]
  have hdegL : deg (liftAll (Nat.card F) (Module.finrank F F') L0) = deg L0 := by
    have h := hlift.2
    simp only [Lbl.rk, Lbl.lift, hdegmap] at h
    omega
  have key : ∀ D : List (ℕ × ℕ), (∀ p ∈ D, 0 < p.1) →
      Kills (shLift s (JD (pullθ ι θ) D L0 (deg D + deg L0)))
        (JD θ (D.map fun p => (p.1, p.2 * ∑ i ∈ Finset.range (Module.finrank F F'), Nat.card F ^ i))
          (liftAll (Nat.card F) (Module.finrank F F') L0) (deg D + deg L0)) := by
    intro D
    induction D with
    | nil =>
      intro _
      exact h0 F F' s hl hs ι θ hθ ⟨Nat.card F, [], L0⟩ rfl
        (by unfold Lbl.Ok; exact ⟨hq2, by simp, hLok⟩) rfl
    | cons p D ih =>
      intro hD
      have hD' : ∀ x ∈ D, 0 < x.1 := fun x hx => hD x (List.mem_cons_of_mem _ hx)
      have tr : ∀ (D' L' : List (ℕ × ℕ)) (n m : ℕ), n = m →
          GlobalTheory.BI.IsChar ℂ ℂ (JD θ D' L' n) → GlobalTheory.BI.IsChar ℂ ℂ (JD θ D' L' m) := by
        intro D' L' n m h
        subst h
        exact id
      have hB : GlobalTheory.BI.IsChar ℂ ℂ (JD θ
          (D.map fun p => (p.1, p.2 * ∑ i ∈ Finset.range (Module.finrank F F'), Nat.card F ^ i))
          (liftAll (Nat.card F) (Module.finrank F F') L0) (deg D + deg L0)) := by
        have hc := (hJC F' θ hθ).2 ⟨Nat.card F ^ Module.finrank F F',
          D.map fun p => (p.1, p.2 * ∑ i ∈ Finset.range (Module.finrank F F'), Nat.card F ^ i),
          liftAll (Nat.card F) (Module.finrank F F') L0⟩
          (by
            unfold Lbl.Ok
            refine ⟨hq2', ?_, hLok'⟩
            intro x hx
            obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
            exact hD' y hy) card_lift
        refine tr _ _ _ _ ?_ hc
        show deg _ + deg _ = _
        rw [hdegmap, hdegL]
      exact step hLH hKH hNE hJE hJC hLD s hs ι θ hθ p D L0 _ _ (deg D + deg L0) _
        (by simp only [GlobalTheory.Shin.deg, List.map_cons, List.sum_cons]; omega) rfl
        (by rw [hdegmap, hdegL]) hB (ih hD')
  exact key D0 hDpos
