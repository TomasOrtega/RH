import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsFirstOrderDeformationOfRZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LiftChart
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.SpLiftP
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TangentSpaceDeformationDualNumbers
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SgnMulSelf
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.OnCompSelf
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.OnCompMap
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.HV UpperTheory.V.Base IsLocalRing

/- English proof (translation)
Establish `e1 : adj (g.map f) * g.map f = (adj g * g).map f`. Rewrite using `[(grp B).2.2.2.2.2.1, Matrix.map_mul]`. Establish `e2 : f ν • (1 : M4 B') = (ν • (1 : M4 B)).map f`. Use extensionality with `i j`. Apply the tactic sequence `by_cases h : i = j <;> simp [Matrix.one_apply, h]`.

Unfold `IsGSp`. Rewrite using `[e1, e2]`. Conclude with `⟨fun h => by rw [h], fun hf h => Matrix.map_injective hf h⟩`.
-/
private theorem gsp_map {B B' : Type} [CommRing B] [CommRing B'] (f : B →+* B') (ν : B) (g : M4 B) :
    (IsGSp ν g → IsGSp (f ν) (g.map f)) ∧ (Function.Injective f → IsGSp (f ν) (g.map f) → IsGSp ν g) := by
  have e1 : adj (g.map f) * g.map f = (adj g * g).map f := by
    rw [(grp B).2.2.2.2.2.1, Matrix.map_mul]
  have e2 : f ν • (1 : M4 B') = (ν • (1 : M4 B)).map f := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  unfold IsGSp
  rw [e1, e2]
  exact ⟨fun h => by rw [h], fun hf h => Matrix.map_injective hf h⟩

private def w4 (a : Fin 4) : ℤ × ℤ := (lamW a, muW a)

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem w4_sub_w4_eq_wt (a b : Fin 4) : w4 a - w4 b = wt a b := rfl

/- English proof (translation)
Establish `h1 : ∀ i, u i ∈ wts` using `fun i => by`. Assume the negation of the conclusion as `h`. Establish `h0 : u i ≠ 0` using `fun e => h (e ▸ by decide)`. Establish `h3` using `hu (u i)`. Rewrite `h3` using `[dimsP, if_neg h0, if_neg h]`.

Use `haveI : Nonempty {k // u k = u i} := ⟨⟨i, rfl⟩⟩`. Conclude with `Nat.card_pos.ne' h3`. Establish `h2` using `Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := wts) (f := u) fun i _ => h1 i`. Rewrite `h2` using `[Finset.card_univ, Fintype.card_fin]`. Rewrite using `[h2, show 10 = ∑ j ∈ wts, dimsP j by decide]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← hu, Nat.card_eq_fintype_card, Fintype.card_subtype]`.
-/
private theorem card_ten {n : ℕ} (u : Fin n → ℤ × ℤ) (hu : ∀ j, Nat.card {i // u i = j} = dimsP j) : n = 10 := by
  classical
  have h1 : ∀ i, u i ∈ wts := fun i => by
    by_contra h
    have h0 : u i ≠ 0 := fun e => h (e ▸ by decide)
    have h3 := hu (u i)
    rw [dimsP, if_neg h0, if_neg h] at h3
    haveI : Nonempty {k // u k = u i} := ⟨⟨i, rfl⟩⟩
    exact Nat.card_pos.ne' h3
  have h2 := Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := wts) (f := u) fun i _ => h1 i
  rw [Finset.card_univ, Fintype.card_fin] at h2
  rw [h2, show 10 = ∑ j ∈ wts, dimsP j by decide]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← hu, Nat.card_eq_fintype_card, Fintype.card_subtype]

/- English proof (translation)
Introduce `Ω _ _ _ l _ c D hD q hq E _ _ _ _ _ _ _ _ R _ _ _ ρ hrep`. Use `haveI : IsGalois ℚ Ω := {}`. Use `haveI : CompactSpace (D.Gp q) := isCompact_iff_compactSpace.1 (isClosed_Dec _).isCompact`. Take `⟨ρ₀, h0, hpt⟩` from `r0pt D hD`. Establish `hQ0 : EqP D q (D.loc ρ₀ q).hom` using `((ptMap D hD c.O ρ₀).1 hpt).atP q hq`.

Establish `h0' : (D.loc ρ₀ q).hom = D.r0At q` using `congrArg (fun r => MonoidHom.comp r (D.Gp q).subtype) h0`. Establish `hst : ρ.TStable w4`. Introduce `R' _ _ _ f t ht`. Set `s : R'ˣ × R'ˣ` to `(t (Multiplicative.ofAdd (1, 0)), t (Multiplicative.ofAdd (0, 1)))`. Establish `hs : ∀ j, wv s j = t (Multiplicative.ofAdd j)` using `fun j => by show t (Multiplicative.ofAdd (1, 0)) ^ j.1 * t (Multiplicative.ofAdd (0, 1)) ^ j.2 = _`.

Rewrite using `[← map_zpow t, ← map_zpow t, ← map_mul, ← ofAdd_zsmul, ← ofAdd_zsmul, ← ofAdd_add]`. Simplify using the standard rewrite rules. Take `⟨-, -, -, -, -, -, -, -, hmul, hone, hadj, -⟩` from `grp R'`. Set `r' : Lift c.O (D.rbarAt q) R'` to `{ hom := ⟨⟨fun g => tconj s ((ρ.map f).hom g), by rw [map_one, hone]⟩, fun g h => by show tconj s _ = _`. Rewrite using `[map_mul, hmul]⟩`.

Use `cont := fun a b N => by show IsLocallyConstant fun g => Ideal.Quotient.mk _ ((wv s (wt a b) : R') * (ρ.map f).hom g a b)`. Simplify using `only [map_mul]`. Conclude with `(IsLocallyConstant.const _).mul ((ρ.map f).cont a b N)`. Use `red := fun g a b => by show res _ _ ((wv s (wt a b) : R') * (ρ.map f).hom g a b) = _`. Rewrite using `[map_mul, hs, ht, one_mul, (ρ.map f).red] }`.

Take `⟨h1, h2⟩` from `(hrep R').1 f`. Take `⟨f', hf', -⟩` from `(hrep R').2 r' ⟨fun g => by show adj (tconj s _) * tconj s _ = _`. Rewrite using `[hadj, ← hmul, h1 g]`. Use `conv_rhs => rw [← hone s]`. Use extensionality with `i j`.

Conclude with `mul_left_comm _ _ _, fun g hg => by`. Use `show tconj s _ = _`. Rewrite using `[h2 g hg, hone]⟩`. Use `⟨f', fun g a b => ?_⟩` and prove the remaining obligations. Rewrite using `[hf', w4_sub_w4_eq_wt, ← hs]`.

Both sides reduce to the same expression. Take `⟨x, P, n, u, φ, hx, hφ, hy, hw, hS⟩` from `liftChart (l := l) (D.rbarAt q) w4 E R ρ (fun B _ _ r => EqP D q r) (fun B B' _ _ _ _ f r => ⟨fun h => ⟨fun g => by`. Rewrite using `[← f.commutes]`. Conclude with `(gsp_map (f : B →+* B') _ _).1 (h.1 g), fun g hg => by`. Use `show (r g).map f = 1`.

Rewrite using `[h.2 g hg, Matrix.map_one _ (map_zero f) (map_one f)]⟩,`. Use `fun hf h => ⟨fun g => (gsp_map (f : B →+* B') _ _).2 hf (by`. Use `h.1 g` as an intermediate fact. Rewrite using `[← f.commutes] at this), fun g hg => Matrix.map_injective hf (by` and apply the resulting hypothesis. Conclude with `(h.2 g hg).trans (Matrix.map_one _ (map_zero f) (map_one f)).symm)⟩⟩)`.

Use `hrep hst (D.loc ρ₀ q) hQ0 (fun g a b hab => by`. Rewrite using `[h0']`. Conclude with `Matrix.diagonal_apply_ne (fun i => (D.ps i g : c.O)) fun e => hab (congrArg w4 e))`. Use the proof step `(by`. Introduce `B _ _ _ _ _ _ _ _ _ _ π hπ B' _ _ _ _ _ _ _ _ _ _ π' hπ' p hp hpc r' h1 h2 h3`.

Take `⟨r, a1, a2, a3⟩` from `spLiftP D hD q hq E B π hπ B' π' hπ' p hp hpc r' ⟨h0' ▸ h1, h2⟩ h3`. Conclude with `⟨r, a1.cont, a2, a3⟩)`. Establish `hu : ∀ j, Nat.card {i // u i = j} = dimsP j` using `fun j => by`. Take `⟨S, e, hS⟩` from `hS j`. Rewrite `hS` using `[h0']`.

Conclude with `e.trans (UpperTheory.tangent_space_deformation_dual_numbers D hD q hq E j S hS)`. Take `rfl` from `card_ten u hu`. Conclude with `⟨x, P, u, φ, by rw [hx, h0'], hφ, hy, hu, hw⟩`.
-/
theorem UpperTheory.V.Loc.spChartP :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (hD : D.Good) (q : ℕ), q ∈ D.Sb → ∀ (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra ↥c.O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ↥c.O E] [IsScalarTower ℤ_[l] ℚ_[l] E] [IsFractionRing ↥c.O E] (R : Type) [CommRing R] [Algebra ↥c.O R] [IsCO ↥c.O R] (ρ : Lift c.O (D.rbarAt q) R), Represents (D.condP q) ρ → ∃ (x : R →ₐ[c.O] c.O) (P : Ideal R) (w : Fin 10 → ℤ × ℤ) (φ : R →ₐ[c.O] MvPowerSeries (Fin 10) E), (ρ.map x).hom = D.r0At q ∧ UpperTheory.V.Loc.IsCompl P x φ ∧ (∃ y, x y ≠ 0 ∧ ∀ a ∈ P, y * a = 0) ∧ (∀ j, Nat.card {i // w i = j} = dimsP j) ∧ ∀ g a b, φ (ρ.hom g a b) ∈ wtPart E w (wt a b) := by
  intro Ω _ _ _ l _ c D hD q hq E _ _ _ _ _ _ _ _ R _ _ _ ρ hrep
  haveI : IsGalois ℚ Ω := {}
  haveI : CompactSpace (D.Gp q) := isCompact_iff_compactSpace.1 (isClosed_Dec _).isCompact
  obtain ⟨ρ₀, h0, hpt⟩ := r0pt D hD
  have hQ0 : EqP D q (D.loc ρ₀ q).hom := ((ptMap D hD c.O ρ₀).1 hpt).atP q hq
  have h0' : (D.loc ρ₀ q).hom = D.r0At q := congrArg (fun r => MonoidHom.comp r (D.Gp q).subtype) h0
  have hst : ρ.TStable w4 := by
    intro R' _ _ _ f t ht
    let s : R'ˣ × R'ˣ := (t (Multiplicative.ofAdd (1, 0)), t (Multiplicative.ofAdd (0, 1)))
    have hs : ∀ j, wv s j = t (Multiplicative.ofAdd j) := fun j => by
      show t (Multiplicative.ofAdd (1, 0)) ^ j.1 * t (Multiplicative.ofAdd (0, 1)) ^ j.2 = _
      rw [← map_zpow t, ← map_zpow t, ← map_mul, ← ofAdd_zsmul, ← ofAdd_zsmul, ← ofAdd_add]
      simp
    obtain ⟨-, -, -, -, -, -, -, -, hmul, hone, hadj, -⟩ := grp R'
    let r' : Lift c.O (D.rbarAt q) R' :=
      { hom := ⟨⟨fun g => tconj s ((ρ.map f).hom g), by rw [map_one, hone]⟩, fun g h => by
          show tconj s _ = _
          rw [map_mul, hmul]⟩
        cont := fun a b N => by
          show IsLocallyConstant fun g => Ideal.Quotient.mk _ ((wv s (wt a b) : R') * (ρ.map f).hom g a b)
          simp only [map_mul]
          exact (IsLocallyConstant.const _).mul ((ρ.map f).cont a b N)
        red := fun g a b => by
          show res _ _ ((wv s (wt a b) : R') * (ρ.map f).hom g a b) = _
          rw [map_mul, hs, ht, one_mul, (ρ.map f).red] }
    obtain ⟨h1, h2⟩ := (hrep R').1 f
    obtain ⟨f', hf', -⟩ := (hrep R').2 r' ⟨fun g => by
      show adj (tconj s _) * tconj s _ = _
      rw [hadj, ← hmul, h1 g]
      conv_rhs => rw [← hone s]
      ext i j
      exact mul_left_comm _ _ _, fun g hg => by
      show tconj s _ = _
      rw [h2 g hg, hone]⟩
    refine ⟨f', fun g a b => ?_⟩
    rw [hf', w4_sub_w4_eq_wt, ← hs]
    rfl
  obtain ⟨x, P, n, u, φ, hx, hφ, hy, hw, hS⟩ := liftChart (l := l) (D.rbarAt q) w4 E R ρ (fun B _ _ r => EqP D q r)
    (fun B B' _ _ _ _ f r => ⟨fun h => ⟨fun g => by
        rw [← f.commutes]
        exact (gsp_map (f : B →+* B') _ _).1 (h.1 g), fun g hg => by
        show (r g).map f = 1
        rw [h.2 g hg, Matrix.map_one _ (map_zero f) (map_one f)]⟩,
      fun hf h => ⟨fun g => (gsp_map (f : B →+* B') _ _).2 hf (by
        have := h.1 g
        rwa [← f.commutes] at this), fun g hg => Matrix.map_injective hf (by
        exact (h.2 g hg).trans (Matrix.map_one _ (map_zero f) (map_one f)).symm)⟩⟩)
    hrep hst (D.loc ρ₀ q) hQ0 (fun g a b hab => by
      rw [h0']
      exact Matrix.diagonal_apply_ne (fun i => (D.ps i g : c.O)) fun e => hab (congrArg w4 e))
    (by
      intro B _ _ _ _ _ _ _ _ _ _ π hπ B' _ _ _ _ _ _ _ _ _ _ π' hπ' p hp hpc r' h1 h2 h3
      obtain ⟨r, a1, a2, a3⟩ := spLiftP D hD q hq E B π hπ B' π' hπ' p hp hpc r' ⟨h0' ▸ h1, h2⟩ h3
      exact ⟨r, a1.cont, a2, a3⟩)
  have hu : ∀ j, Nat.card {i // u i = j} = dimsP j := fun j => by
    obtain ⟨S, e, hS⟩ := hS j
    rw [h0'] at hS
    exact e.trans (UpperTheory.tangent_space_deformation_dual_numbers D hD q hq E j S hS)
  obtain rfl := card_ten u hu
  exact ⟨x, P, u, φ, by rw [hx, h0'], hφ, hy, hu, hw⟩
