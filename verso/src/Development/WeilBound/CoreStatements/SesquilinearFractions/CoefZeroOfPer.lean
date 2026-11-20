import Development.WeilBound.CoreStatements.SesquilinearFractions.EqZeroOfCoef
import Development.WeilBound.CoreStatements.SesquilinearFractions.PureTypeLatticesOrthogonal
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsEqSmulOfFinrankOne
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

noncomputable section

namespace PositivityTheory.Xgf.DPer

open scoped Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

/- English proof (translation)
Apply `sq_eq_sq_iff_eq_or_eq_neg.1` to reduce the goal to its premises. Use `congrArg (fun x : 𝓞 E => τ (x : E)) H.rt_sq` as an intermediate fact. Simplify using `at this`. Rewrite using `[H.sqrt_neg_disc_sq, ← this]`.
-/
theorem rt_cases (τ : E →+* ℂ) : τ (H.rt : E) = H.rt0 ∨ τ (H.rt : E) = -H.rt0 := by
  apply sq_eq_sq_iff_eq_or_eq_neg.1
  have := congrArg (fun x : 𝓞 E => τ (x : E)) H.rt_sq
  simp at this
  rw [H.sqrt_neg_disc_sq, ← this]

/- English proof (translation)
Consider the cases of `b`. Conclude with `GlobalTheory.CM.LatData.exists_embedding H (by simp [H.sqrt_neg_disc_sq])`. Conclude with `GlobalTheory.CM.LatData.exists_embedding H H.sqrt_neg_disc_sq`.
-/
theorem exists_emb (b : Bool) : ∃ τ : E →+* ℂ, τ (H.rt : E) = (if b then H.rt0 else -H.rt0) := by
  cases b
  · exact GlobalTheory.CM.LatData.exists_embedding H (by simp [H.sqrt_neg_disc_sq])
  · exact GlobalTheory.CM.LatData.exists_embedding H H.sqrt_neg_disc_sq

variable {g : ℕ} {ty : Fin g → (E →+* ℂ)} {p q : ℕ} (hty : IsTypeFn H p q ty)

def eP (τ : E →+* ℂ) (h : τ (H.rt : E) = H.rt0) : {k // ty k = τ} ≃ Fin p :=
  Fintype.equivFinOfCardEq (by rw [Fintype.card_eq_nat_card]; exact (hty τ).1 h)

def eQ (τ : E →+* ℂ) (h : τ (H.rt : E) ≠ H.rt0) : {k // ty k = τ} ≃ Fin q :=
  Fintype.equivFinOfCardEq (by rw [Fintype.card_eq_nat_card]; exact (hty τ).2 h)

def blk (k : Fin g) : Fin p ⊕ Fin q :=
  if h : ty k (H.rt : E) = H.rt0 then .inl (eP hty (ty k) h ⟨k, rfl⟩) else .inr (eQ hty (ty k) h ⟨k, rfl⟩)

/- English proof (translation)
Substitute `hk` using the available equality. Simplify using `[blk, h]`.
-/
theorem blk_inl (τ : E →+* ℂ) (h : τ (H.rt : E) = H.rt0) (k : Fin g) (hk : ty k = τ) :
    blk hty k = .inl (eP hty τ h ⟨k, hk⟩) := by
  subst hk
  simp [blk, h]

/- English proof (translation)
Substitute `hk` using the available equality. Simplify using `[blk, h]`.
-/
theorem blk_inr (τ : E →+* ℂ) (h : τ (H.rt : E) ≠ H.rt0) (k : Fin g) (hk : ty k = τ) :
    blk hty k = .inr (eQ hty τ h ⟨k, hk⟩) := by
  subst hk
  simp [blk, h]

variable {D : Datum H} (c : D.La →ₗ[𝓞 E] (Fin p ⊕ Fin q →₀ 𝓞 E)) (n : ℕ)

def per : D.La →+ (Fin g → ℂ) where
  toFun y k := ty k ((c y (blk hty k) : 𝓞 E) : E) / n
  map_zero' := by funext k; simp
  map_add' y y' := by funext k; simp [add_div]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem per_apply (y : D.La) (k : Fin g) : per hty c n y k = ty k ((c y (blk hty k) : 𝓞 E) : E) / n := rfl

/- English proof (translation)
Simplify using `[per_apply, mul_div_assoc]`.
-/
theorem per_smul (a : 𝓞 E) (y : D.La) (k : Fin g) : per hty c n (a • y) k = ty k (a : E) * per hty c n y k := by
  simp [per_apply, mul_div_assoc]

/- English proof (translation)
Rewrite using `[per_apply, hc, blk_inr hty (ty k) hk k rfl]`. Simplify using the standard rewrite rules.
-/
theorem per_inl (y : D.La) (a : Fin p) (hc : c y = Finsupp.single (.inl a) (n : 𝓞 E)) (k : Fin g)
    (hk : ty k (H.rt : E) ≠ H.rt0) : per hty c n y k = 0 := by
  rw [per_apply, hc, blk_inr hty (ty k) hk k rfl]
  simp

/- English proof (translation)
Establish `h : ty k (H.rt : E) = H.rt0` using `(rt_cases (ty k)).resolve_right hk`. Rewrite using `[per_apply, hc, blk_inl hty (ty k) h k rfl]`. Simplify using the standard rewrite rules.
-/
theorem per_inr (y : D.La) (b : Fin q) (hc : c y = Finsupp.single (.inr b) (n : 𝓞 E)) (k : Fin g)
    (hk : ty k (H.rt : E) ≠ -H.rt0) : per hty c n y k = 0 := by
  have h : ty k (H.rt : E) = H.rt0 := (rt_cases (ty k)).resolve_right hk
  rw [per_apply, hc, blk_inl hty (ty k) h k rfl]
  simp

/- English proof (translation)
Use extensionality with `m`. Consider the cases of `m with`. Consider the case `inl a`. Take `⟨τ, hτ⟩` from `exists_emb (H := H) true`. Simplify using `only [if_true] at hτ`.

Set `k` to `((eP hty τ hτ).symm a).1`. Establish `hk : ty k = τ` using `((eP hty τ hτ).symm a).2`. Establish `hb : blk hty k = .inl a`. Rewrite using `[blk_inl hty τ hτ k hk]`. Simplify using `[k]`.

Establish `h1` using `congrFun h k`. Rewrite `h1` using `[per_apply, hb]`. Establish `hn' : (n : ℂ) ≠ 0` using `by exact_mod_cast hn.ne'`. Rewrite `h1` using `[Pi.zero_apply, div_eq_zero_iff, or_iff_left hn', map_eq_zero]`. Simplify using `using h1`.

Consider the case `inr b`. Take `⟨τ, hτ⟩` from `exists_emb (H := H) false`. Simplify using `only [Bool.false_eq_true, if_false] at hτ`. Establish `hτ' : τ (H.rt : E) ≠ H.rt0` using `by rw [hτ]; exact fun h => Host_rt0_ne_neg (H := H) h.symm`. Set `k` to `((eQ hty τ hτ').symm b).1`.

Establish `hk : ty k = τ` using `((eQ hty τ hτ').symm b).2`. Establish `hb : blk hty k = .inr b`. Rewrite using `[blk_inr hty τ hτ' k hk]`. Simplify using `[k]`. Establish `h1` using `congrFun h k`.

Rewrite `h1` using `[per_apply, hb]`. Establish `hn' : (n : ℂ) ≠ 0` using `by exact_mod_cast hn.ne'`. Rewrite `h1` using `[Pi.zero_apply, div_eq_zero_iff, or_iff_left hn', map_eq_zero]`. Simplify using `using h1`.
-/
theorem coef_zero_of_per (hn : 0 < n) (y : D.La) (h : per hty c n y = 0) : c y = 0 := by
  ext m
  cases m with
  | inl a =>
    obtain ⟨τ, hτ⟩ := exists_emb (H := H) true
    simp only [if_true] at hτ
    let k := ((eP hty τ hτ).symm a).1
    have hk : ty k = τ := ((eP hty τ hτ).symm a).2
    have hb : blk hty k = .inl a := by
      rw [blk_inl hty τ hτ k hk]
      simp [k]
    have h1 := congrFun h k
    rw [per_apply, hb] at h1
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [Pi.zero_apply, div_eq_zero_iff, or_iff_left hn', map_eq_zero] at h1
    simpa using h1
  | inr b =>
    obtain ⟨τ, hτ⟩ := exists_emb (H := H) false
    simp only [Bool.false_eq_true, if_false] at hτ
    have hτ' : τ (H.rt : E) ≠ H.rt0 := by rw [hτ]; exact fun h => Host_rt0_ne_neg (H := H) h.symm
    let k := ((eQ hty τ hτ').symm b).1
    have hk : ty k = τ := ((eQ hty τ hτ').symm b).2
    have hb : blk hty k = .inr b := by
      rw [blk_inr hty τ hτ' k hk]
      simp [k]
    have h1 := congrFun h k
    rw [per_apply, hb] at h1
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [Pi.zero_apply, div_eq_zero_iff, or_iff_left hn', map_eq_zero] at h1
    simpa using h1

end PositivityTheory.Xgf.DPer

end
