import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SqMap
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.HStable

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.BilQ

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.Flat.FrGauge
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

variable {R : Type} [CommRing R] {d d' : ℕ}

local notation "eX" => ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.eXv
local notation "eZ'" => ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.eZ

/- English proof (translation)
Rewrite using `[MvPowerSeries.rename_eq_subst]`. Unfold `ev`. Use `congr 1`. Use function extensionality and compare the values at `p`. Take `⟨j, i⟩` from `p`.

Use `fin_cases j`. Both sides reduce to the same expression.
-/
theorem eval_first_point_eq_rename (φ : PS R 1 d) : ev (n := 2) ![pt R d 0] φ = MvPowerSeries.rename (eX d) φ := by
  rw [MvPowerSeries.rename_eq_subst]
  unfold ev
  congr 1
  funext p
  obtain ⟨j, i⟩ := p
  fin_cases j
  rfl

/- English proof (translation)
Rewrite using `[MvPowerSeries.rename_eq_subst]`. Unfold `ev`. Use `congr 1`. Use function extensionality and compare the values at `p`. Take `⟨j, i⟩` from `p`.

Use `fin_cases j`. Both sides reduce to the same expression.
-/
theorem eval_second_point_eq_rename (φ : PS R 1 d) : ev (n := 2) ![pt R d 1] φ = MvPowerSeries.rename (eZ' d) φ := by
  rw [MvPowerSeries.rename_eq_subst]
  unfold ev
  congr 1
  funext p
  obtain ⟨j, i⟩ := p
  fin_cases j
  rfl

/- English proof (translation)
Establish `hA : ∀ u : Fin 2 × Fin d →₀ ℕ, u ((1 : Fin 2), b) ≠ 0 → MvPowerSeries.coeff u (MvPowerSeries.rename (eX d) P) = 0`. Introduce `u hu`. Use `MvPowerSeries.coeff_rename_eq_zero _ _ ?_` and prove the remaining obligations. Introduce and unpack `⟨w, hw⟩`. Apply `hu` to reduce the goal to its premises.

Rewrite using `[← hw]`. Use `Finsupp.mapDomain_notin_range _ _ ?_` and prove the remaining obligations. Introduce and unpack `⟨⟨p, q⟩, hp⟩`. Establish `h2 : (0 : Fin 2) = 1` using `congrArg Prod.fst hp`. Conclude with `absurd h2 (by simp)`.

Establish `hB : ∀ v : Fin 2 × Fin d →₀ ℕ, v ((0 : Fin 2), a) ≠ 0 → MvPowerSeries.coeff v (MvPowerSeries.rename (eZ' d) Q) = 0`. Introduce `v hv`. Use `MvPowerSeries.coeff_rename_eq_zero _ _ ?_` and prove the remaining obligations. Introduce and unpack `⟨w, hw⟩`. Apply `hv` to reduce the goal to its premises.

Rewrite using `[← hw]`. Use `Finsupp.mapDomain_notin_range _ _ ?_` and prove the remaining obligations. Introduce and unpack `⟨⟨p, q⟩, hp⟩`. Establish `h2 : (1 : Fin 2) = 0` using `congrArg Prod.fst hp`. Conclude with `absurd h2 (by simp)`.

Establish `hne : ((0 : Fin 2), a) ≠ ((1 : Fin 2), b)` using `fun e => absurd (congrArg Prod.fst e) (by simp)`. Establish `e0 : Finsupp.single ((0 : Fin 2), a) 1 = Finsupp.embDomain (eX d) (Finsupp.single ((0 : Fin 1), a) 1)`. Rewrite using `[Finsupp.embDomain_single]`. Both sides reduce to the same expression. Establish `e1 : Finsupp.single ((1 : Fin 2), b) 1 = Finsupp.embDomain (eZ' d) (Finsupp.single ((0 : Fin 1), b) 1)`.

Rewrite using `[Finsupp.embDomain_single]`. Both sides reduce to the same expression. Rewrite using `[MvPowerSeries.coeff_mul, Finset.sum_eq_single (Finsupp.single ((0 : Fin 2), a) 1, Finsupp.single ((1 : Fin 2), b) 1)]`. Use `show MvPowerSeries.coeff (Finsupp.single ((0 : Fin 2), a) 1) _ * MvPowerSeries.coeff (Finsupp.single ((1 : Fin 2), b) 1) _ = _`. Rewrite using `[e0, e1, MvPowerSeries.coeff_embDomain_rename, MvPowerSeries.coeff_embDomain_rename]`.

Introduce and unpack `⟨u, v⟩ huv hne'`. Rewrite `huv` using `[Finset.HasAntidiagonal.mem_antidiagonal]`. Simplify using `only at huv ⊢`. Distinguish the cases in `hu : u ((1 : Fin 2), b) = 0`. Distinguish the cases in `hv : v ((0 : Fin 2), a) = 0`.

It suffices to derive a contradiction. Apply `hne'` to reduce the goal to its premises. Establish `hv1` using `DFunLike.congr_fun huv ((1 : Fin 2), b)`. Establish `hu0` using `DFunLike.congr_fun huv ((0 : Fin 2), a)`. Simplify using `only [Finsupp.add_apply, Finsupp.single_apply, hne, hne.symm, if_true, if_false, hu, hv] at hv1 hu0`.

Establish `hrest : ∀ t, t ≠ ((0 : Fin 2), a) → t ≠ ((1 : Fin 2), b) → u t = 0 ∧ v t = 0`. Introduce `t h0 h1`. Establish `ht` using `DFunLike.congr_fun huv t`. Simplify using `only [Finsupp.add_apply, Finsupp.single_apply, Ne.symm h0, Ne.symm h1, if_false] at ht`. Use linear arithmetic over natural numbers and integers.

Use `Prod.ext (Finsupp.ext fun t => ?_) (Finsupp.ext fun t => ?_)` and prove the remaining obligations. Distinguish the cases in `h0 : t = ((0 : Fin 2), a)`. Substitute `h0` using the available equality. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers.

Distinguish the cases in `h1 : t = ((1 : Fin 2), b)`. Substitute `h1` using the available equality. Simplify using `[Finsupp.single_apply, hne.symm, hu]`. Simplify using `[Finsupp.single_apply, Ne.symm h0, (hrest t h0 h1).1]`. Distinguish the cases in `h1 : t = ((1 : Fin 2), b)`.

Substitute `h1` using the available equality. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Distinguish the cases in `h0 : t = ((0 : Fin 2), a)`. Substitute `h0` using the available equality.

Simplify using `[Finsupp.single_apply, hne, hv]`. Simplify using `[Finsupp.single_apply, Ne.symm h1, (hrest t h0 h1).2]`. Rewrite using `[hB v hv, mul_zero]`. Rewrite using `[hA u hu, zero_mul]`. Introduce `h`.

Rewrite `h` using `[Finset.HasAntidiagonal.mem_antidiagonal]`. Conclude with `absurd rfl h`.
-/
theorem coeff_xz_rename (P Q : PS R 1 d) (a b : Fin d) :
    MvPowerSeries.coeff (Finsupp.single ((0 : Fin 2), a) 1 + Finsupp.single ((1 : Fin 2), b) 1)
        (MvPowerSeries.rename (eX d) P * MvPowerSeries.rename (eZ' d) Q) =
      MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), a) 1) P *
        MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), b) 1) Q := by
  classical
  have hA : ∀ u : Fin 2 × Fin d →₀ ℕ, u ((1 : Fin 2), b) ≠ 0 →
      MvPowerSeries.coeff u (MvPowerSeries.rename (eX d) P) = 0 := by
    intro u hu
    refine MvPowerSeries.coeff_rename_eq_zero _ _ ?_
    rintro ⟨w, hw⟩
    apply hu
    rw [← hw]
    refine Finsupp.mapDomain_notin_range _ _ ?_
    rintro ⟨⟨p, q⟩, hp⟩
    have h2 : (0 : Fin 2) = 1 := congrArg Prod.fst hp
    exact absurd h2 (by simp)
  have hB : ∀ v : Fin 2 × Fin d →₀ ℕ, v ((0 : Fin 2), a) ≠ 0 →
      MvPowerSeries.coeff v (MvPowerSeries.rename (eZ' d) Q) = 0 := by
    intro v hv
    refine MvPowerSeries.coeff_rename_eq_zero _ _ ?_
    rintro ⟨w, hw⟩
    apply hv
    rw [← hw]
    refine Finsupp.mapDomain_notin_range _ _ ?_
    rintro ⟨⟨p, q⟩, hp⟩
    have h2 : (1 : Fin 2) = 0 := congrArg Prod.fst hp
    exact absurd h2 (by simp)
  have hne : ((0 : Fin 2), a) ≠ ((1 : Fin 2), b) := fun e => absurd (congrArg Prod.fst e) (by simp)
  have e0 : Finsupp.single ((0 : Fin 2), a) 1 = Finsupp.embDomain (eX d) (Finsupp.single ((0 : Fin 1), a) 1) := by
    rw [Finsupp.embDomain_single]; rfl
  have e1 : Finsupp.single ((1 : Fin 2), b) 1 = Finsupp.embDomain (eZ' d) (Finsupp.single ((0 : Fin 1), b) 1) := by
    rw [Finsupp.embDomain_single]; rfl
  rw [MvPowerSeries.coeff_mul, Finset.sum_eq_single
    (Finsupp.single ((0 : Fin 2), a) 1, Finsupp.single ((1 : Fin 2), b) 1)]
  · show MvPowerSeries.coeff (Finsupp.single ((0 : Fin 2), a) 1) _ * MvPowerSeries.coeff (Finsupp.single ((1 : Fin 2), b) 1) _ = _
    rw [e0, e1, MvPowerSeries.coeff_embDomain_rename, MvPowerSeries.coeff_embDomain_rename]
  · rintro ⟨u, v⟩ huv hne'
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at huv
    simp only at huv ⊢
    by_cases hu : u ((1 : Fin 2), b) = 0
    · by_cases hv : v ((0 : Fin 2), a) = 0
      · exfalso
        apply hne'
        have hv1 := DFunLike.congr_fun huv ((1 : Fin 2), b)
        have hu0 := DFunLike.congr_fun huv ((0 : Fin 2), a)
        simp only [Finsupp.add_apply, Finsupp.single_apply, hne, hne.symm, if_true, if_false, hu, hv] at hv1 hu0
        have hrest : ∀ t, t ≠ ((0 : Fin 2), a) → t ≠ ((1 : Fin 2), b) → u t = 0 ∧ v t = 0 := by
          intro t h0 h1
          have ht := DFunLike.congr_fun huv t
          simp only [Finsupp.add_apply, Finsupp.single_apply, Ne.symm h0, Ne.symm h1, if_false] at ht
          omega
        refine Prod.ext (Finsupp.ext fun t => ?_) (Finsupp.ext fun t => ?_)
        · by_cases h0 : t = ((0 : Fin 2), a)
          · subst h0; simp; omega
          by_cases h1 : t = ((1 : Fin 2), b)
          · subst h1; simp [Finsupp.single_apply, hne.symm, hu]
          simp [Finsupp.single_apply, Ne.symm h0, (hrest t h0 h1).1]
        · by_cases h1 : t = ((1 : Fin 2), b)
          · subst h1; simp; omega
          by_cases h0 : t = ((0 : Fin 2), a)
          · subst h0; simp [Finsupp.single_apply, hne, hv]
          simp [Finsupp.single_apply, Ne.symm h1, (hrest t h0 h1).2]
      · rw [hB v hv, mul_zero]
    · rw [hA u hu, zero_mul]
  · intro h
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at h
    exact absurd rfl h

/- English proof (translation)
Take `⟨j, i⟩` from `p`. Use `fin_cases j`. Use `show MvPowerSeries.constantCoeff (ev (n := 2) ![pt R d 0] (Qs i)) = 0`. Rewrite using `[eval_first_point_eq_rename, MvPowerSeries.constantCoeff_rename, hQ]`. Use `show MvPowerSeries.constantCoeff (ev (n := 2) ![pt R d 1] (Qs i)) = 0`.

Rewrite using `[eval_second_point_eq_rename, MvPowerSeries.constantCoeff_rename, hQ]`.
-/
theorem const_side {Qs : Fin d' → PS R 1 d} (hQ : ∀ i, MvPowerSeries.constantCoeff (Qs i) = 0)
    (p : Fin 2 × Fin d') :
    MvPowerSeries.constantCoeff (ev (n := 2) ![pt R d p.1] (Qs p.2)) = 0 := by
  obtain ⟨j, i⟩ := p
  fin_cases j
  · show MvPowerSeries.constantCoeff (ev (n := 2) ![pt R d 0] (Qs i)) = 0
    rw [eval_first_point_eq_rename, MvPowerSeries.constantCoeff_rename, hQ]
  · show MvPowerSeries.constantCoeff (ev (n := 2) ![pt R d 1] (Qs i)) = 0
    rw [eval_second_point_eq_rename, MvPowerSeries.constantCoeff_rename, hQ]

/- English proof (translation)
Establish `hs : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin d => (![pt R d j] q.1 q.2 : PS R 2 d))` using `MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => by`. Take `⟨u, i⟩` from `q`. Use `fin_cases u`. Conclude with `MvPowerSeries.constantCoeff_X _`. Unfold `ev`.

Rewrite using `[MvPowerSeries.subst_comp_subst_apply hs hb]`. Use `congr 1`. Use function extensionality and compare the values at `q`. Take `⟨u, i⟩` from `q`. Use `fin_cases u`.

Conclude with `MvPowerSeries.subst_X hb _`.
-/
theorem subst_side {τ : Type} {b : Fin 2 × Fin d → MvPowerSeries τ R} (hb : MvPowerSeries.HasSubst b) (j : Fin 2)
    (φ : PS R 1 d) :
    MvPowerSeries.subst b (ev (n := 2) ![pt R d j] φ) =
      MvPowerSeries.subst (fun q : Fin 1 × Fin d => b (j, q.2)) φ := by
  have hs : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin d => (![pt R d j] q.1 q.2 : PS R 2 d)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => by
      obtain ⟨u, i⟩ := q
      fin_cases u
      exact MvPowerSeries.constantCoeff_X _
  unfold ev
  rw [MvPowerSeries.subst_comp_subst_apply hs hb]
  congr 1
  funext q
  obtain ⟨u, i⟩ := q
  fin_cases u
  exact MvPowerSeries.subst_X hb _

/- English proof (translation)
Rewrite using `[← MvPowerSeries.coe_substAlgHom ha, map_one]`.
-/
theorem subst_one' {σ τ : Type} {a : σ → MvPowerSeries τ R} (ha : MvPowerSeries.HasSubst a) :
    MvPowerSeries.subst a (1 : MvPowerSeries σ R) = 1 := by
  rw [← MvPowerSeries.coe_substAlgHom ha, map_one]

/- English proof (translation)
Rewrite using `[← MvPowerSeries.coe_substAlgHom ha, map_zero]`.
-/
theorem subst_zero' {σ τ : Type} {a : σ → MvPowerSeries τ R} (ha : MvPowerSeries.HasSubst a) :
    MvPowerSeries.subst a (0 : MvPowerSeries σ R) = 0 := by
  rw [← MvPowerSeries.coe_substAlgHom ha, map_zero]

/- English proof (translation)
Establish `hb : MvPowerSeries.HasSubst (fun p : Fin 2 × Fin d => A p.1 p.2)` using `MvPowerSeries.hasSubst_of_constantCoeff_zero fun p => hA p.1 p.2`. Establish `hb' : MvPowerSeries.HasSubst (fun p : Fin 2 × Fin d' => A' p.1 p.2)` using `MvPowerSeries.hasSubst_of_constantCoeff_zero fun p => hA' p.1 p.2`. Establish `hσ : MvPowerSeries.HasSubst (fun p : Fin 2 × Fin d' => ev (n` using `2) ![pt R d p.1] (Qs p.2)) := MvPowerSeries.hasSubst_of_constantCoeff_zero (const_side hQ)`. Establish `hq : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin d' => Qs q.2)` using `MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => hQ q.2`. Establish `h1` using `congrArg (MvPowerSeries.subst (fun q : Fin 1 × Fin d' => Qs q.2)) h`.

Unfold `ev at h1`. Rewrite `h1` using `[subst_one' hq, MvPowerSeries.subst_comp_subst_apply hb' hq]`. Unfold `ev subQ`. Rewrite using `[MvPowerSeries.subst_comp_subst_apply hσ hb, ← h1]`. Use `congr 1`.

Use function extensionality and compare the values at `p`. Rewrite using `[subst_side hb, hc]`.
-/
theorem ev_subQ_eq_one {Qs : Fin d' → PS R 1 d} (hQ : ∀ i, MvPowerSeries.constantCoeff (Qs i) = 0)
    {f : PS R 2 d'} (A : Fin 2 → Pt R 1 d) (A' : Fin 2 → Pt R 1 d')
    (hA : ∀ j i, MvPowerSeries.constantCoeff (A j i) = 0) (hA' : ∀ j i, MvPowerSeries.constantCoeff (A' j i) = 0)
    (hc : ∀ j i, MvPowerSeries.subst (fun q : Fin 1 × Fin d => A j q.2) (Qs i) =
      MvPowerSeries.subst (fun q : Fin 1 × Fin d' => Qs q.2) (A' j i))
    (h : ev (n := 1) A' f = 1) : ev (n := 1) A (subQ Qs f) = 1 := by
  have hb : MvPowerSeries.HasSubst (fun p : Fin 2 × Fin d => A p.1 p.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun p => hA p.1 p.2
  have hb' : MvPowerSeries.HasSubst (fun p : Fin 2 × Fin d' => A' p.1 p.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun p => hA' p.1 p.2
  have hσ : MvPowerSeries.HasSubst (fun p : Fin 2 × Fin d' => ev (n := 2) ![pt R d p.1] (Qs p.2)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (const_side hQ)
  have hq : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin d' => Qs q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => hQ q.2
  have h1 := congrArg (MvPowerSeries.subst (fun q : Fin 1 × Fin d' => Qs q.2)) h
  unfold ev at h1
  rw [subst_one' hq, MvPowerSeries.subst_comp_subst_apply hb' hq] at h1
  unfold ev subQ
  rw [MvPowerSeries.subst_comp_subst_apply hσ hb, ← h1]
  congr 1
  funext p
  rw [subst_side hb, hc]

/- English proof (translation)
Establish `hq : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin d' => Qs q.2)` using `MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => hQ q.2`. Establish `hz : ∀ i, MvPowerSeries.subst (fun q : Fin 1 × Fin d => (0 : PS R 1 d)) (Qs i) = MvPowerSeries.subst (fun q : Fin 1 × Fin d' => Qs q.2) (0 : PS R 1 d')` using `fun i => by`. Rewrite using `[subst_zero' hq]`. Conclude with `MvPowerSeries.subst_zero_of_constantCoeff_zero (hQ i)`. Establish `hx : ∀ i, MvPowerSeries.subst (fun q : Fin 1 × Fin d => pt R d 0 q.2) (Qs i) = MvPowerSeries.subst (fun q : Fin 1 × Fin d' => Qs q.2) (pt R d' 0 i)` using `fun i => by`.

Establish `e : (fun q : Fin 1 × Fin d => pt R d 0 q.2) = MvPowerSeries.X`. Use function extensionality and compare the values at `q`. Take `⟨u, l⟩` from `q`. Use `fin_cases u`. Both sides reduce to the same expression.

Rewrite using `[e, MvPowerSeries.subst_self]`. Use `show _ = MvPowerSeries.subst _ (MvPowerSeries.X ((0 : Fin 1), i) : PS R 1 d')`. Rewrite using `[MvPowerSeries.subst_X hq]`. Both sides reduce to the same expression. Establish `c0 : ∀ {n : ℕ} (i : Fin n), MvPowerSeries.constantCoeff (pt R (n` using `1) n 0 i) = 0 := fun i => MvPowerSeries.constantCoeff_X _`.

Prove the components needed by the constructor for the conclusion. Use `ev_subQ_eq_one hQ _ _ ?_ ?_ ?_ hf.1` and prove the remaining obligations. Introduce `j i`. Use `fin_cases j`. Conclude with `map_zero _`.

Conclude with `c0 i`. Introduce `j i`. Use `fin_cases j`. Conclude with `map_zero _`. Conclude with `c0 i`.

Introduce `j i`. Use `fin_cases j`. Conclude with `hz i`. Conclude with `hx i`. Use `ev_subQ_eq_one hQ _ _ ?_ ?_ ?_ hf.2` and prove the remaining obligations.

Introduce `j i`. Use `fin_cases j`. Conclude with `c0 i`. Conclude with `map_zero _`. Introduce `j i`.

Use `fin_cases j`. Conclude with `c0 i`. Conclude with `map_zero _`. Introduce `j i`. Use `fin_cases j`.

Conclude with `hx i`. Conclude with `hz i`.
-/
theorem axOne_subQ {Qs : Fin d' → PS R 1 d} (hQ : ∀ i, MvPowerSeries.constantCoeff (Qs i) = 0)
    {f : PS R 2 d'} (hf : AxOne f) : AxOne (subQ Qs f) := by
  have hq : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin d' => Qs q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => hQ q.2
  have hz : ∀ i, MvPowerSeries.subst (fun q : Fin 1 × Fin d => (0 : PS R 1 d)) (Qs i) =
      MvPowerSeries.subst (fun q : Fin 1 × Fin d' => Qs q.2) (0 : PS R 1 d') := fun i => by
    rw [subst_zero' hq]
    exact MvPowerSeries.subst_zero_of_constantCoeff_zero (hQ i)
  have hx : ∀ i, MvPowerSeries.subst (fun q : Fin 1 × Fin d => pt R d 0 q.2) (Qs i) =
      MvPowerSeries.subst (fun q : Fin 1 × Fin d' => Qs q.2) (pt R d' 0 i) := fun i => by
    have e : (fun q : Fin 1 × Fin d => pt R d 0 q.2) = MvPowerSeries.X := by
      funext q
      obtain ⟨u, l⟩ := q
      fin_cases u
      rfl
    rw [e, MvPowerSeries.subst_self]
    show _ = MvPowerSeries.subst _ (MvPowerSeries.X ((0 : Fin 1), i) : PS R 1 d')
    rw [MvPowerSeries.subst_X hq]
    rfl
  have c0 : ∀ {n : ℕ} (i : Fin n), MvPowerSeries.constantCoeff (pt R (n := 1) n 0 i) = 0 := fun i =>
    MvPowerSeries.constantCoeff_X _
  constructor
  · refine ev_subQ_eq_one hQ _ _ ?_ ?_ ?_ hf.1
    · intro j i; fin_cases j
      · exact map_zero _
      · exact c0 i
    · intro j i; fin_cases j
      · exact map_zero _
      · exact c0 i
    · intro j i; fin_cases j
      · exact hz i
      · exact hx i
  · refine ev_subQ_eq_one hQ _ _ ?_ ?_ ?_ hf.2
    · intro j i; fin_cases j
      · exact c0 i
      · exact map_zero _
    · intro j i; fin_cases j
      · exact c0 i
      · exact map_zero _
    · intro j i; fin_cases j
      · exact hx i
      · exact hz i

/- English proof (translation)
Establish `hσ : MvPowerSeries.HasSubst (fun p : Fin 2 × Fin d' => ev (n` using `2) ![pt R d p.1] (Qs p.2)) := MvPowerSeries.hasSubst_of_constantCoeff_zero (const_side hQ)`. Establish `hA0 : MvPowerSeries.HasSubst (fun p : Fin 2 × Fin d' => (![0, pt R d' 0] : Fin 2 → Pt R 1 d') p.1 p.2)` using `MvPowerSeries.hasSubst_of_constantCoeff_zero fun p => by`. Take `⟨j, i⟩` from `p`. Use `fin_cases j`. Conclude with `map_zero _`.

Conclude with `MvPowerSeries.constantCoeff_X _`. Establish `hA1 : MvPowerSeries.HasSubst (fun p : Fin 2 × Fin d' => (![pt R d' 0, 0] : Fin 2 → Pt R 1 d') p.1 p.2)` using `MvPowerSeries.hasSubst_of_constantCoeff_zero fun p => by`. Take `⟨j, i⟩` from `p`. Use `fin_cases j`. Conclude with `MvPowerSeries.constantCoeff_X _`.

Conclude with `map_zero _`. Establish `h0 : ev (n` using `1) ![0, pt R d' 0] (f - 1) = 0 := by`. Unfold `ev`. Rewrite using `[MvPowerSeries.subst_sub hA0, subst_one' hA0]`. Conclude with `sub_eq_zero.2 hf.1`.

Establish `h1 : ev (n` using `1) ![pt R d' 0, 0] (f - 1) = 0 := by`. Unfold `ev`. Rewrite using `[MvPowerSeries.subst_sub hA1, subst_one' hA1]`. Conclude with `sub_eq_zero.2 hf.2`. Use extensionality with `a b`.

Establish `hdeg` using `ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.degree_xz a b`. Establish `hn : (Finsupp.single ((0 : Fin 2), a) 1 + Finsupp.single ((1 : Fin 2), b) 1 : Fin 2 × Fin d →₀ ℕ) ≠ 0`. Introduce `e`. Rewrite `hdeg` using `[e]`. Simplify using `at hdeg`.

Establish `key` using `ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.coeff_subst_xz (f - 1) h0 h1 _ (const_side hQ) _ hdeg`. Rewrite `key` using `[MvPowerSeries.subst_sub hσ, subst_one' hσ, map_sub, MvPowerSeries.coeff_one, if_neg hn, sub_zero]`. Use `show MvPowerSeries.coeff _ (subQ Qs f) = _`. Use `key.trans ?_` and prove the remaining obligations. Simplify using `only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Establish `hl : (Finsupp.single ((0 : Fin 2), l) 1 + Finsupp.single ((1 : Fin 2), m) 1 : Fin 2 × Fin d' →₀ ℕ) ≠ 0`. Introduce `e`. Establish `hd` using `ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.degree_xz l m`.

Rewrite `hd` using `[e]`. Simplify using `at hd`. Establish `e0 : ev (n` using `2) ![pt R d ((0 : Fin 2), l).1] (Qs ((0 : Fin 2), l).2) = MvPowerSeries.rename (eX d) (Qs l) := eval_first_point_eq_rename _`. Establish `e1 : ev (n` using `2) ![pt R d ((1 : Fin 2), m).1] (Qs ((1 : Fin 2), m).2) = MvPowerSeries.rename (eZ' d) (Qs m) := eval_second_point_eq_rename _`. Rewrite using `[map_sub, MvPowerSeries.coeff_one, if_neg hl, sub_zero, e0, e1, coeff_xz_rename]`.

Use `show _ = linQ Qs l a * bil f 1 1 l m * linQ Qs m b`. Simplify using `only [linQ, bil]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem bil_subQ {Qs : Fin d' → PS R 1 d} (hQ : ∀ i, MvPowerSeries.constantCoeff (Qs i) = 0)
    {f : PS R 2 d'} (hf : AxOne f) : bil (subQ Qs f) 1 1 = (linQ Qs).transpose * bil f 1 1 * linQ Qs := by
  classical
  have hσ : MvPowerSeries.HasSubst (fun p : Fin 2 × Fin d' => ev (n := 2) ![pt R d p.1] (Qs p.2)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (const_side hQ)
  have hA0 : MvPowerSeries.HasSubst (fun p : Fin 2 × Fin d' => (![0, pt R d' 0] : Fin 2 → Pt R 1 d') p.1 p.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun p => by
      obtain ⟨j, i⟩ := p
      fin_cases j
      · exact map_zero _
      · exact MvPowerSeries.constantCoeff_X _
  have hA1 : MvPowerSeries.HasSubst (fun p : Fin 2 × Fin d' => (![pt R d' 0, 0] : Fin 2 → Pt R 1 d') p.1 p.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun p => by
      obtain ⟨j, i⟩ := p
      fin_cases j
      · exact MvPowerSeries.constantCoeff_X _
      · exact map_zero _
  have h0 : ev (n := 1) ![0, pt R d' 0] (f - 1) = 0 := by
    unfold ev
    rw [MvPowerSeries.subst_sub hA0, subst_one' hA0]
    exact sub_eq_zero.2 hf.1
  have h1 : ev (n := 1) ![pt R d' 0, 0] (f - 1) = 0 := by
    unfold ev
    rw [MvPowerSeries.subst_sub hA1, subst_one' hA1]
    exact sub_eq_zero.2 hf.2
  ext a b
  have hdeg := ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.degree_xz a b
  have hn : (Finsupp.single ((0 : Fin 2), a) 1 + Finsupp.single ((1 : Fin 2), b) 1 : Fin 2 × Fin d →₀ ℕ) ≠ 0 := by
    intro e
    rw [e] at hdeg
    simp at hdeg
  have key := ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.coeff_subst_xz (f - 1) h0 h1 _ (const_side hQ) _ hdeg
  rw [MvPowerSeries.subst_sub hσ, subst_one' hσ, map_sub, MvPowerSeries.coeff_one, if_neg hn, sub_zero] at key
  show MvPowerSeries.coeff _ (subQ Qs f) = _
  refine key.trans ?_
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun l _ => ?_
  have hl : (Finsupp.single ((0 : Fin 2), l) 1 + Finsupp.single ((1 : Fin 2), m) 1 : Fin 2 × Fin d' →₀ ℕ) ≠ 0 := by
    intro e
    have hd := ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.degree_xz l m
    rw [e] at hd
    simp at hd
  have e0 : ev (n := 2) ![pt R d ((0 : Fin 2), l).1] (Qs ((0 : Fin 2), l).2) = MvPowerSeries.rename (eX d) (Qs l) :=
    eval_first_point_eq_rename _
  have e1 : ev (n := 2) ![pt R d ((1 : Fin 2), m).1] (Qs ((1 : Fin 2), m).2) = MvPowerSeries.rename (eZ' d) (Qs m) :=
    eval_second_point_eq_rename _
  rw [map_sub, MvPowerSeries.coeff_one, if_neg hl, sub_zero, e0, e1, coeff_xz_rename]
  show _ = linQ Qs l a * bil f 1 1 l m * linQ Qs m b
  simp only [linQ, bil]
  ring

/- English proof (translation)
Introduce `_ _ _ _ _ _ hQ hf` and use `⟨axOne_subQ hQ hf, bil_subQ hQ hf⟩`.
-/
theorem bil_axOne_subQ : ∀ (R : Type) [CommRing R] (d d' : ℕ) (Qs : Fin d' → PS R 1 d) (f : PS R 2 d'),
    (∀ i, MvPowerSeries.constantCoeff (Qs i) = 0) → AxOne f →
      AxOne (subQ Qs f) ∧ bil (subQ Qs f) 1 1 = (linQ Qs).transpose * bil f 1 1 * linQ Qs :=
  fun _ _ _ _ _ _ hQ hf => ⟨axOne_subQ hQ hf, bil_subQ hQ hf⟩

end GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.BilQ
