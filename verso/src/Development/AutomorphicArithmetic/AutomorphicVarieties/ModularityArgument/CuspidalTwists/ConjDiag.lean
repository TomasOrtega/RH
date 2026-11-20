import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.OverOf4

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial
open UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3

namespace UpperTheory.V.Cu.RankFourResidualFlag

section Alg

variable {R : Type} [CommRing R]

def mat (P b e : R) : M4 R := !![P, 0, 0, 0; 0, P * e, 0, 0; 0, -(b * e), e, 0; b, 0, 0, 1]

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [flg, tn, nA, low, Matrix.mul_apply, Fin.sum_univ_succ]`.
-/
theorem flg_eq (x s : R) : flg x s = !![1, 0, 0, 0; s, 1, 0, 0; -(x * s), -x, 1, 0; x, 0, -s, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [flg, tn, nA, low, Matrix.mul_apply, Fin.sum_univ_succ]

/- English proof (translation)
Rewrite using `[flg_eq, flg_eq]`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp`.
-/
theorem flg_map {R' : Type} [CommRing R'] (f : R →+* R') (x s : R) : (flg x s).map f = flg (f x) (f s) := by
  rw [flg_eq, flg_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/- English proof (translation)
Rewrite using `[flg_eq]`. Simplify using the standard rewrite rules.
-/
theorem flg_10 (x s : R) : flg x s 1 0 = s := by
  rw [flg_eq]
  simp

/- English proof (translation)
Rewrite using `[flg_eq]`. Apply the tactic sequence `fin_cases i <;> simp [adj_apply, mat, Matrix.mul_apply, Fin.sum_univ_succ, sgn, Fin.rev]`.
-/
theorem conj_diag (x s dl P b e : R) (i : Fin 4) :
    (adj (flg x s) * (dl • mat P b e) * flg x s) i i = (dl • mat P b e) i i := by
  rw [flg_eq]
  fin_cases i <;> simp [adj_apply, mat, Matrix.mul_apply, Fin.sum_univ_succ, sgn, Fin.rev]

/- English proof (translation)
Introduce `i j hij hw`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> first | (simp [mat]; done) | exact absurd h1 hw | exact absurd h2 hw | exact absurd rfl hij`.
-/
theorem mat_supp {S : Finset (ℤ × ℤ)} (h1 : wt 2 1 ∈ S) (h2 : wt 3 0 ∈ S) (dl P b e : R) : SuppM S (dl • mat P b e) := by
  intro i j hij hw
  fin_cases i <;> fin_cases j <;> first | (simp [mat]; done) | exact absurd h1 hw | exact absurd h2 hw | exact absurd rfl hij

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [tn]`.
-/
theorem tn_map {R' : Type} [CommRing R'] (f : R →+* R') (g t : M2 R) : (tn g t).map f = tn (g.map f) (t.map f) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tn]

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [tn, mat, hg, ht1, ht2, ht0, hg1]`.
-/
theorem tn_eq (g t : M2 R) (hg : g 0 1 = 0) (ht1 : t 0 1 = 0) (ht2 : t 1 0 = 0) (ht0 : t 0 0 = 1)
    (hg1 : g 1 1 = 1) : tn g t = mat (g 0 0) (g 1 0) (t 1 1) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tn, mat, hg, ht1, ht2, ht0, hg1]

/- English proof (translation)
Establish `e : (u : O) = ((u * v⁻¹ : Oˣ) : O) * (v : O)` using `by simp`. Rewrite using `[e, map_mul, h]`.
-/
theorem res_mul {O : Type} [CommRing O] [IsLocalRing O] (u v : Oˣ) {t : ResidueField O}
    (h : residue O ((u * v⁻¹ : Oˣ) : O) = t) : residue O (u : O) = t * residue O (v : O) := by
  have e : (u : O) = ((u * v⁻¹ : Oˣ) : O) * (v : O) := by simp
  rw [e, map_mul, h]

end Alg

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Apply the tactic sequence `cases pr <;> simp [chi, lab, Raw.ps, Raw.th, mul_comm]`.
-/
theorem chi_mul {c : Coef l} (D : Raw Ω c) (pr : Bool) (g : G ℚ Ω) :
    chi D pr 0 g * chi D pr 3 g = chi D pr 1 g * chi D pr 2 g := by
  cases pr <;> simp [chi, lab, Raw.ps, Raw.th, mul_comm]

/- English proof (translation)
Establish `hint : (inc h).IsIntegral`. Introduce `y`. Take `⟨p, hp, e⟩ : IsIntegral ℤ_[l] y` from `Algebra.IsIntegral.isIntegral y`. Use `⟨p.map (algebraMap ℤ_[l] c.O), hp.map _, ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.eval₂_map]`.

Conclude with `e`. Use `haveI : IsLocalHom (inc h) := hint.isLocalHom (Subalgebra.inclusion_injective h)`. Conclude with `map_nonunit (inc h) x hx`.
-/
private theorem inc_mem {c c' : Coef l} (h : c.O ≤ c'.O) {x : c.O}
    (hx : x ∈ maximalIdeal c.O) : inc h x ∈ maximalIdeal c'.O := by
  have hint : (inc h).IsIntegral := by
    intro y
    obtain ⟨p, hp, e⟩ : IsIntegral ℤ_[l] y := Algebra.IsIntegral.isIntegral y
    refine ⟨p.map (algebraMap ℤ_[l] c.O), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    exact e
  haveI : IsLocalHom (inc h) := hint.isLocalHom (Subalgebra.inclusion_injective h)
  exact map_nonunit (inc h) x hx

/- English proof (translation)
Establish `h1 : x - y ∈ maximalIdeal c.O`. Rewrite using `[← residue_eq_zero_iff, map_sub, e, sub_self]`. Establish `h2` using `hf _ (inc_mem h h1)`. Rewrite `h2` using `[map_sub, map_sub, sub_eq_zero]`. Then use the resulting hypothesis.
-/
theorem eq_of_res {c c' : Coef l} (h : c.O ≤ c'.O) {R : Type} [CommRing R]
    (f : c'.O →+* R) (hf : ∀ y ∈ maximalIdeal c'.O, f y = 0) {x y : c.O} (e : residue c.O x = residue c.O y) :
    f (inc h x) = f (inc h y) := by
  have h1 : x - y ∈ maximalIdeal c.O := by
    rw [← residue_eq_zero_iff, map_sub, e, sub_self]
  have h2 := hf _ (inc_mem h h1)
  rwa [map_sub, map_sub, sub_eq_zero] at h2

end UpperTheory.V.Cu.RankFourResidualFlag

open UpperTheory.V.Cu.RankFourResidualFlag in
/- English proof (translation)
Introduce `Ω _ _ _ l _ d T hT W R _ f hf`. Establish `hpr : T.pr = d.T₀.pr` using `hT.pr`. Establish `h00 : ∀ g, f (d.ρ₁ g 0 0) = f (inc d.h (Phi d.D d.T₀.pr d.k g : d.c.O))` using `fun g => by`. Use `hf _ (d.mod.red g).1` as an intermediate fact. Rewrite `this` using `[map_sub, sub_eq_zero]`. Then use the resulting hypothesis.

Establish `h11 : ∀ g, f (d.ρ₁ g 1 1) = 1` using `fun g => by`. Use `hf _ (d.mod.red g).2.1` as an intermediate fact. Rewrite `this` using `[map_sub, sub_eq_zero, map_one]`. Then use the resulting hypothesis. Establish `h01 : ∀ g, f (d.ρ₁ g 0 1) = 0` using `fun g => hf _ (d.mod.red g).2.2`. Establish `t00 : ∀ g, f (d.τ g 0 0) = 1` using `fun g => by`.

Use `hf _ (d.tau.red g).1` as an intermediate fact. Rewrite `this` using `[map_sub, sub_eq_zero, map_one]`. Then use the resulting hypothesis. Establish `t01 : ∀ g, f (d.τ g 0 1) = 0` using `fun g => hf _ (d.tau.red g).2`. Establish `hne : ∀ u : d.c.Oˣ, f (inc d.h (u : d.c.O)) ≠ 0` using `fun u => by`. Establish `: IsUnit (f (inc d.h (u : d.c.O)))` using `(u.isUnit.map (inc d.h)).map f`.

Conclude with `this.ne_zero`. Establish `sgnK : ∀ g : G T.F Ω, ∃ e : R, (e = 1 ∨ e = -1) ∧ f (d.τ (resQ T.F g) 1 1) = e ∧ f (d.τ (resQ T.F g) 1 0) = 0 ∧ f (inc d.h (chi d.D d.T₀.pr 1 (resQ T.F g) : d.c.O)) = f (inc d.h (chi d.D d.T₀.pr 0 (resQ T.F g) : d.c.O)) * e ∧ f (inc d.h (chi d.D d.T₀.pr 2 (resQ T.F g) : d.c.O)) = …`. Introduce `g`. Establish `hres : resQ d.T₀.F (resLe hT.le g) = resQ T.F g` using `AlgEquiv.ext fun _ => rfl`. Establish `hrb : ∀ t : ResidueField d.c.O, d.T₀.rb wAl (resLe hT.le g) = t → residue d.c.O (chi d.D d.T₀.pr 0 (resQ T.F g) : d.c.O) = t * residue d.c.O (chi d.D d.T₀.pr 1 (resQ T.F g) : d.c.O)` using `fun t ht => by`.

Apply `res_mul` to reduce the goal to its premises. Simplify using `only [Tower.rb, Fr.rt, Tower.fr, MonoidHom.coe_mk, OneHom.coe_mk, MonoidHom.comp_apply, wAl, zpow_one, zpow_zero, mul_one, hres] at ht`. Conclude with `ht`. Establish `hprod` using `congrArg (fun u : d.c.Oˣ => f (inc d.h (u : d.c.O))) (chi_mul d.D d.T₀.pr (resQ T.F g))`. Simplify using `only [Units.val_mul, map_mul] at hprod`.

Establish `h0` using `hne (chi d.D d.T₀.pr 0 (resQ T.F g))`. Distinguish the cases in `hK : resQ T.F g ∈ d.K'.fixingSubgroup`. Establish `e1` using `hrb 1 (d.quad.on _ (by rwa [hres]))`. Rewrite `e1` using `[one_mul]`. Establish `e2` using `eq_of_res d.h f hf e1.symm`.

Take `⟨a1, a2⟩` from `d.tau.on _ hK`. Use `⟨1, Or.inl rfl, by rw [a1, t00], by rw [a2, t01], by rw [e2, mul_one], ?_⟩` and prove the remaining obligations. Rewrite `hprod` using `[e2]`. Rewrite using `[mul_one]`. Conclude with `(mul_left_cancel₀ h0 hprod).symm`.

Establish `e1` using `hrb (-1) (d.quad.off _ (by rwa [hres]))`. Establish `e1' : residue d.c.O (chi d.D d.T₀.pr 1 (resQ T.F g) : d.c.O) = residue d.c.O (-(chi d.D d.T₀.pr 0 (resQ T.F g) : d.c.O))`. Rewrite using `[map_neg, e1]`. Expand and normalize the polynomial expressions, which then agree. Establish `e2` using `eq_of_res d.h f hf e1'`.

Rewrite `e2` using `[map_neg, map_neg]`. Take `⟨a1, a2⟩` from `d.tau.off _ hK`. Use `⟨-1, Or.inr rfl, by rw [a1, map_neg, t00], by rw [a2, map_neg, t01, neg_zero], by rw [e2]; ring, ?_⟩` and prove the remaining obligations. Rewrite `hprod` using `[e2]`. Use `mul_left_cancel₀ h0 (hprod.trans (by ring) : _ = f (inc d.h (chi d.D d.T₀.pr 0 (resQ T.F g) : d.c.O)) * (-f (inc d.h (chi d.D d.T₀.pr 2 (resQ T.F g) : d.c.O))))` as an intermediate fact.

Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree. Establish `hr : ∀ g, ((d.Q T).map f).r g = f (inc d.h (d.δ (resQ T.F g) : d.c.O)) • tn ((d.ρ₁ (resQ T.F g)).map f) ((d.τ (resQ T.F g)).map f)` using `fun g => by`. Rewrite using `[← tn_map]`. Use extensionality with `i j`.

Conclude with `map_mul f _ _`. Establish `key : ∀ g : G T.F Ω, ∃ e P b dl : R, ((d.Q T).map f).r g = dl • mat P b e ∧ (f.comp (inc d.h)) ((T.fr W).χ 0 g : d.c.O) = dl * P ∧ (f.comp (inc d.h)) ((T.fr W).χ 1 g : d.c.O) = dl * (P * e) ∧ (f.comp (inc d.h)) ((T.fr W).χ 2 g : d.c.O) = dl * e ∧ (f.comp (inc d.h)) ((T.fr W).χ 3 …`. Introduce `g`. Take `⟨e, -, he, he10, e1, e2⟩` from `sgnK g`. Establish `hrg` using `hr g`.

Establish `hχ : ∀ i, (f.comp (inc d.h)) ((T.fr W).χ i g : d.c.O) = f (inc d.h (chi d.D d.T₀.pr i (resQ T.F g) : d.c.O))` using `fun i => by`. Rewrite using `[← hpr]`. Both sides reduce to the same expression. Generalize the expression as in `resQ T.F g = g' at he he10 e1 e2 hrg hχ`. Establish `r0 : f (inc d.h (chi d.D d.T₀.pr 0 g' : d.c.O)) = f (inc d.h (d.δ g' : d.c.O)) * f (inc d.h (Phi d.D d.T₀.pr d.k g' : d.c.O))`.

Rewrite using `[← map_mul, ← map_mul]`. Apply `eq_of_res d.h f hf` to reduce the goal to its premises. Rewrite using `[map_mul]`. Conclude with `d.tw.red0 g'`. Establish `r3` using `eq_of_res d.h f hf (d.tw.red3 g')`.

Use `⟨e, f (inc d.h (Phi d.D d.T₀.pr d.k g' : d.c.O)), f (d.ρ₁ g' 1 0), f (inc d.h (d.δ g' : d.c.O)), ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hrg, tn_eq _ _ (by rw [Matrix.map_apply]; exact h01 _) (by rw [Matrix.map_apply]; exact t01 _) (by rw [Matrix.map_apply]; exact he10) (by rw [Matrix.map_apply]; exact t00 _) (by rw [Matrix.map_apply]; exact h11 _)]`. Simplify using `only [Matrix.map_apply]`. Rewrite using `[h00, he]`. Rewrite using `[hχ 0]`.

Conclude with `r0`. Rewrite using `[hχ 1, e1, r0]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hχ 2, e2, r3]`. Rewrite using `[hχ 3]`.

Conclude with `r3`. Establish `hn : ∀ v, ((d.Q T).map f).n v = flg (f (d.x (T.pl v))) (f (d.s (T.pl v)))` using `fun v => flg_map f _ _`. Establish `hs : ∀ S : Finset (ℤ × ℤ), wt 2 1 ∈ S → wt 3 0 ∈ S → Supp S ((d.Q T).map f).r` using `fun S h1 h2 g => by`. Take `⟨e, P, b, dl, h, -⟩` from `key g`. Rewrite using `[h]`.

Conclude with `mat_supp h1 h2 dl P b e`. Establish `hsM : Supp nM ((d.Q T).map f).r` using `hs nM (by decide) (by decide)`. Use `⟨⟨fun g i => ?_, fun (v : T.ι) s _ i => ?_, Or.inr hsM⟩, hsM, ⟨hs aA (by decide) (by decide), fun v => ?_⟩, fun g => ?_⟩` and prove the remaining obligations. Take `⟨e, P, b, dl, h, c0, c1, c2, c3⟩` from `key g`. Rewrite using `[h]`.

Use `fin_cases i`. Use `exacts [c0.symm, c1.symm, c2.symm, (mul_one dl).trans c3.symm]`. Take `⟨e, P, b, dl, h, c0, c1, c2, c3⟩` from `key s show (adj (((d.Q T).map f).n v) * ((d.Q T).map f).r s * ((d.Q T).map f).n v) i i = _`. Rewrite using `[hn v, h, conj_diag]`. Use `fin_cases i`.

Use `exacts [c0.symm, c1.symm, c2.symm, (mul_one dl).trans c3.symm]`. Rewrite using `[hn, flg_10]`. Apply the tactic sequence `rcases d.tau.sgn (T.pl v) with h | h <;> rw [h] <;> simp`. Rewrite using `[Matrix.det_fin_two, map_sub, map_mul, map_mul, h00, h11, h01]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.V.Cu.resOf4 : UpperTheory.V.Cu.ResOf4 := by
  intro Ω _ _ _ l _ d T hT W R _ f hf
  have hpr : T.pr = d.T₀.pr := hT.pr

  have h00 : ∀ g, f (d.ρ₁ g 0 0) = f (inc d.h (Phi d.D d.T₀.pr d.k g : d.c.O)) := fun g => by
    have := hf _ (d.mod.red g).1
    rwa [map_sub, sub_eq_zero] at this
  have h11 : ∀ g, f (d.ρ₁ g 1 1) = 1 := fun g => by
    have := hf _ (d.mod.red g).2.1
    rwa [map_sub, sub_eq_zero, map_one] at this
  have h01 : ∀ g, f (d.ρ₁ g 0 1) = 0 := fun g => hf _ (d.mod.red g).2.2
  have t00 : ∀ g, f (d.τ g 0 0) = 1 := fun g => by
    have := hf _ (d.tau.red g).1
    rwa [map_sub, sub_eq_zero, map_one] at this
  have t01 : ∀ g, f (d.τ g 0 1) = 0 := fun g => hf _ (d.tau.red g).2
  have hne : ∀ u : d.c.Oˣ, f (inc d.h (u : d.c.O)) ≠ 0 := fun u => by
    have : IsUnit (f (inc d.h (u : d.c.O))) := (u.isUnit.map (inc d.h)).map f
    exact this.ne_zero

  have sgnK : ∀ g : G T.F Ω, ∃ e : R, (e = 1 ∨ e = -1) ∧ f (d.τ (resQ T.F g) 1 1) = e ∧ f (d.τ (resQ T.F g) 1 0) = 0 ∧
      f (inc d.h (chi d.D d.T₀.pr 1 (resQ T.F g) : d.c.O)) = f (inc d.h (chi d.D d.T₀.pr 0 (resQ T.F g) : d.c.O)) * e ∧
      f (inc d.h (chi d.D d.T₀.pr 2 (resQ T.F g) : d.c.O)) = f (inc d.h (chi d.D d.T₀.pr 3 (resQ T.F g) : d.c.O)) * e := by
    intro g
    have hres : resQ d.T₀.F (resLe hT.le g) = resQ T.F g := AlgEquiv.ext fun _ => rfl
    have hrb : ∀ t : ResidueField d.c.O, d.T₀.rb wAl (resLe hT.le g) = t →
        residue d.c.O (chi d.D d.T₀.pr 0 (resQ T.F g) : d.c.O) =
          t * residue d.c.O (chi d.D d.T₀.pr 1 (resQ T.F g) : d.c.O) := fun t ht => by
      apply res_mul
      simp only [Tower.rb, Fr.rt, Tower.fr, MonoidHom.coe_mk, OneHom.coe_mk, MonoidHom.comp_apply, wAl, zpow_one,
        zpow_zero, mul_one, hres] at ht
      exact ht
    have hprod := congrArg (fun u : d.c.Oˣ => f (inc d.h (u : d.c.O))) (chi_mul d.D d.T₀.pr (resQ T.F g))
    simp only [Units.val_mul, map_mul] at hprod
    have h0 := hne (chi d.D d.T₀.pr 0 (resQ T.F g))
    by_cases hK : resQ T.F g ∈ d.K'.fixingSubgroup
    · have e1 := hrb 1 (d.quad.on _ (by rwa [hres]))
      rw [one_mul] at e1
      have e2 := eq_of_res d.h f hf e1.symm
      obtain ⟨a1, a2⟩ := d.tau.on _ hK
      refine ⟨1, Or.inl rfl, by rw [a1, t00], by rw [a2, t01], by rw [e2, mul_one], ?_⟩
      rw [e2] at hprod
      rw [mul_one]
      exact (mul_left_cancel₀ h0 hprod).symm
    · have e1 := hrb (-1) (d.quad.off _ (by rwa [hres]))
      have e1' : residue d.c.O (chi d.D d.T₀.pr 1 (resQ T.F g) : d.c.O) =
          residue d.c.O (-(chi d.D d.T₀.pr 0 (resQ T.F g) : d.c.O)) := by
        rw [map_neg, e1]
        ring
      have e2 := eq_of_res d.h f hf e1'
      rw [map_neg, map_neg] at e2
      obtain ⟨a1, a2⟩ := d.tau.off _ hK
      refine ⟨-1, Or.inr rfl, by rw [a1, map_neg, t00], by rw [a2, map_neg, t01, neg_zero], by rw [e2]; ring, ?_⟩
      rw [e2] at hprod
      have := mul_left_cancel₀ h0 (hprod.trans (by ring) : _ = f (inc d.h (chi d.D d.T₀.pr 0 (resQ T.F g) : d.c.O)) *
        (-f (inc d.h (chi d.D d.T₀.pr 2 (resQ T.F g) : d.c.O))))
      rw [this]
      ring

  have hr : ∀ g, ((d.Q T).map f).r g = f (inc d.h (d.δ (resQ T.F g) : d.c.O)) •
      tn ((d.ρ₁ (resQ T.F g)).map f) ((d.τ (resQ T.F g)).map f) := fun g => by
    rw [← tn_map]
    ext i j
    exact map_mul f _ _
  have key : ∀ g : G T.F Ω, ∃ e P b dl : R, ((d.Q T).map f).r g = dl • mat P b e ∧
      (f.comp (inc d.h)) ((T.fr W).χ 0 g : d.c.O) = dl * P ∧ (f.comp (inc d.h)) ((T.fr W).χ 1 g : d.c.O) = dl * (P * e) ∧
      (f.comp (inc d.h)) ((T.fr W).χ 2 g : d.c.O) = dl * e ∧ (f.comp (inc d.h)) ((T.fr W).χ 3 g : d.c.O) = dl := by
    intro g
    obtain ⟨e, -, he, he10, e1, e2⟩ := sgnK g
    have hrg := hr g
    have hχ : ∀ i, (f.comp (inc d.h)) ((T.fr W).χ i g : d.c.O) =
        f (inc d.h (chi d.D d.T₀.pr i (resQ T.F g) : d.c.O)) := fun i => by
      rw [← hpr]
      rfl
    generalize resQ T.F g = g' at he he10 e1 e2 hrg hχ
    have r0 : f (inc d.h (chi d.D d.T₀.pr 0 g' : d.c.O)) =
        f (inc d.h (d.δ g' : d.c.O)) * f (inc d.h (Phi d.D d.T₀.pr d.k g' : d.c.O)) := by
      rw [← map_mul, ← map_mul]
      apply eq_of_res d.h f hf
      rw [map_mul]
      exact d.tw.red0 g'
    have r3 := eq_of_res d.h f hf (d.tw.red3 g')
    refine ⟨e, f (inc d.h (Phi d.D d.T₀.pr d.k g' : d.c.O)), f (d.ρ₁ g' 1 0), f (inc d.h (d.δ g' : d.c.O)), ?_, ?_, ?_, ?_, ?_⟩
    · rw [hrg, tn_eq _ _ (by rw [Matrix.map_apply]; exact h01 _) (by rw [Matrix.map_apply]; exact t01 _)
        (by rw [Matrix.map_apply]; exact he10) (by rw [Matrix.map_apply]; exact t00 _) (by rw [Matrix.map_apply]; exact h11 _)]
      simp only [Matrix.map_apply]
      rw [h00, he]
    · rw [hχ 0]
      exact r0
    · rw [hχ 1, e1, r0]
      ring
    · rw [hχ 2, e2, r3]
    · rw [hχ 3]
      exact r3
  have hn : ∀ v, ((d.Q T).map f).n v = flg (f (d.x (T.pl v))) (f (d.s (T.pl v))) := fun v => flg_map f _ _
  have hs : ∀ S : Finset (ℤ × ℤ), wt 2 1 ∈ S → wt 3 0 ∈ S → Supp S ((d.Q T).map f).r := fun S h1 h2 g => by
    obtain ⟨e, P, b, dl, h, -⟩ := key g
    rw [h]
    exact mat_supp h1 h2 dl P b e
  have hsM : Supp nM ((d.Q T).map f).r := hs nM (by decide) (by decide)
  refine ⟨⟨fun g i => ?_, fun (v : T.ι) s _ i => ?_, Or.inr hsM⟩, hsM, ⟨hs aA (by decide) (by decide), fun v => ?_⟩, fun g => ?_⟩
  · obtain ⟨e, P, b, dl, h, c0, c1, c2, c3⟩ := key g
    rw [h]
    fin_cases i
    exacts [c0.symm, c1.symm, c2.symm, (mul_one dl).trans c3.symm]
  · obtain ⟨e, P, b, dl, h, c0, c1, c2, c3⟩ := key s
    show (adj (((d.Q T).map f).n v) * ((d.Q T).map f).r s * ((d.Q T).map f).n v) i i = _
    rw [hn v, h, conj_diag]
    fin_cases i
    exacts [c0.symm, c1.symm, c2.symm, (mul_one dl).trans c3.symm]
  · rw [hn, flg_10]
    rcases d.tau.sgn (T.pl v) with h | h <;> rw [h] <;> simp
  · rw [Matrix.det_fin_two, map_sub, map_mul, map_mul, h00, h11, h01]
    ring
