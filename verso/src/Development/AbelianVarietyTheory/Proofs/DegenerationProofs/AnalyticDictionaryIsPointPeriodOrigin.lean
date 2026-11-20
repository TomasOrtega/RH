import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ReframeSt

open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Arch

noncomputable section
namespace GlobalTheory.Ex.Arch

/- English proof (translation)
Establish `hπ : (2 * Real.pi * Complex.I : ℂ) ≠ 0` using `by simp [Real.pi_ne_zero, Complex.I_ne_zero]`. Establish `h0 : φ 0 = 1`. Establish `h00` using `h 0 0`. Rewrite `h00` using `[add_zero]`. Conclude with `mul_left_cancel (h00.symm.trans (mul_one _).symm)`.

Set `b` to `Module.Free.chooseBasis ℤ X`. Set `l : X →+ ℂ` to `(b.constr ℤ fun i => Complex.log (φ (b i)) / (2 * Real.pi * Complex.I)).toAddMonoidHom`. Use `⟨l, fun x => ?_⟩` and prove the remaining obligations. Set `f₁ : X →+ Additive ℂˣ` to `{ toFun := fun x => Additive.ofMul (φ x) map_zero' := by simp [h0] map_add' := fun x y => by simp [h] }`. Set `f₂ : X →+ Additive ℂˣ` to `{ toFun := fun x => Additive.ofMul (Units.mk0 (eTwoPi (l x)) (AnArc.e_ne_zero _)) map_zero' := by`.

Apply `Additive.toMul.injective` to reduce the goal to its premises. Use `ext`. Simplify using the standard rewrite rules. Use the proof step `map_add' := fun x y => by`. Apply `Additive.toMul.injective` to reduce the goal to its premises.

Use `ext`. Simplify using `[AnArc.e_add] }`. Establish `key : f₁.toIntLinearMap = f₂.toIntLinearMap`. Use `b.ext fun i => ?_` and prove the remaining obligations. Use `show Additive.ofMul (φ (b i)) = Additive.ofMul (Units.mk0 (eTwoPi (l (b i))) (AnArc.e_ne_zero _))`.

Use `congr 1`. Use `ext`. Rewrite using `[Units.val_mk0]`. Establish `hl : l (b i) = Complex.log (φ (b i)) / (2 * Real.pi * Complex.I)`. Simplify using `[l]`.

Rewrite using `[hl, eTwoPi, mul_div_cancel₀ _ hπ, Complex.exp_log (Units.ne_zero _)]`. Establish `hx` using `congrArg (fun u : Additive ℂˣ => ((Additive.toMul u : ℂˣ) : ℂ)) (LinearMap.congr_fun key x)`. Simplify `hx` using `[f₁, f₂]`.
-/
theorem exists_log_of_character {X : Type} [AddCommGroup X] [Module.Free ℤ X] (φ : X → ℂˣ)
    (h : ∀ x y, φ (x + y) = φ x * φ y) : ∃ l : X →+ ℂ, ∀ x, (φ x : ℂ) = eTwoPi (l x) := by
  classical
  have hπ : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have h0 : φ 0 = 1 := by
    have h00 := h 0 0
    rw [add_zero] at h00
    exact mul_left_cancel (h00.symm.trans (mul_one _).symm)
  let b := Module.Free.chooseBasis ℤ X
  let l : X →+ ℂ :=
    (b.constr ℤ fun i => Complex.log (φ (b i)) / (2 * Real.pi * Complex.I)).toAddMonoidHom
  refine ⟨l, fun x => ?_⟩
  let f₁ : X →+ Additive ℂˣ :=
    { toFun := fun x => Additive.ofMul (φ x)
      map_zero' := by simp [h0]
      map_add' := fun x y => by simp [h] }
  let f₂ : X →+ Additive ℂˣ :=
    { toFun := fun x => Additive.ofMul (Units.mk0 (eTwoPi (l x)) (AnArc.e_ne_zero _))
      map_zero' := by
        apply Additive.toMul.injective
        ext
        simp
      map_add' := fun x y => by
        apply Additive.toMul.injective
        ext
        simp [AnArc.e_add] }
  have key : f₁.toIntLinearMap = f₂.toIntLinearMap := by
    refine b.ext fun i => ?_
    show Additive.ofMul (φ (b i)) = Additive.ofMul (Units.mk0 (eTwoPi (l (b i))) (AnArc.e_ne_zero _))
    congr 1
    ext
    rw [Units.val_mk0]
    have hl : l (b i) = Complex.log (φ (b i)) / (2 * Real.pi * Complex.I) := by
      simp [l]
    rw [hl, eTwoPi, mul_div_cancel₀ _ hπ, Complex.exp_log (Units.ne_zero _)]
  have hx := congrArg (fun u : Additive ℂˣ => ((Additive.toMul u : ℂˣ) : ℂ)) (LinearMap.congr_fun key x)
  simpa [f₁, f₂] using hx

variable {O : Type} [CommRing O] [StarRing O] {N : NumD ℂ} {B : AnArc O} (d : Dict N B)

/- English proof (translation)
Establish `h` using `congrArg Units.val (d.ab.2.2.2.2.2.1 x y z)`. Move the coercions through the operations in `at h`. Conclude with `h`.
-/
theorem Dict.cube_val (x y z : Fin B.gB → ℂ) :
    (N.θ (d.ex x) (d.ex y) (d.ex z) : ℂ) * d.fr (x + y) * d.fr (x + z) * d.fr (y + z) =
      d.fr (x + y + z) * d.fr x * d.fr y * d.fr z := by
  have h := congrArg Units.val (d.ab.2.2.2.2.2.1 x y z)
  push_cast at h
  exact h

/- English proof (translation)
Set `E : B.X → ℂˣ` to `fun x => Units.mk0 (eTwoPi (v.1 x)) (AnArc.e_ne_zero _)`. Set `s : N.X → ℂˣ` to `fun χ => E (d.eX.symm χ) * d.fr (B.ct (d.eX.symm χ)) * d.fr v.2 * (d.fr (B.ct (d.eX.symm χ) + v.2))⁻¹`. Establish `hs : ∀ χ χ', s (χ + χ') * N.θ (N.c χ) (N.c χ') (d.ex v.2) = s χ * s χ'`. Introduce `χ χ'`. Take `⟨x, rfl⟩` from `d.eX.surjective χ`.

Take `⟨x', rfl⟩` from `d.eX.surjective χ'`. Rewrite using `[← map_add d.eX, d.c_eq, d.c_eq]`. Establish `h` using `d.cube_val (B.ct x) (B.ct x') v.2`. Use `ext`. Simplify using `only [s, E, AddEquiv.symm_apply_apply, map_add, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, AnArc.e_add]`.

Establish `hθ : (N.θ (d.ex (B.ct x)) (d.ex (B.ct x')) (d.ex v.2) : ℂ) = d.fr (B.ct x + B.ct x' + v.2) * d.fr (B.ct x) * d.fr (B.ct x') * d.fr v.2 / (d.fr (B.ct x + B.ct x') * d.fr (B.ct x + v.2) * d.fr (B.ct x' + v.2))`. Rewrite using `[eq_div_iff (by simp)]`. Take the linear combination `h`. Rewrite using `[hθ]`. Clear the denominators using the available nonvanishing facts.

Use `⟨⟨d.ex v.2, s, hs⟩, ⟨rfl, fun x => ?_⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [s, E, AddEquiv.symm_apply_apply, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]`. Rewrite using `[inv_mul_cancel_right₀ (Units.ne_zero _)]`. Introduce and unpack `g ⟨hb, hg⟩`. Use `NumD.Gt.ext hb (funext fun χ => ?_)` and prove the remaining obligations.

Take `⟨x, rfl⟩` from `d.eX.surjective χ`. Apply `Units.ext` to reduce the goal to its premises. Establish `h` using `hg x`. Simplify using `only [s, E, AddEquiv.symm_apply_apply, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]`. Rewrite using `[eq_mul_inv_iff_mul_eq₀ (Units.ne_zero _)]`.

Conclude with `h`.
-/
theorem Dict.existsUnique_isPt (v : B.V) : ∃! g, d.IsPt v g := by
  let E : B.X → ℂˣ := fun x => Units.mk0 (eTwoPi (v.1 x)) (AnArc.e_ne_zero _)
  let s : N.X → ℂˣ := fun χ =>
    E (d.eX.symm χ) * d.fr (B.ct (d.eX.symm χ)) * d.fr v.2 * (d.fr (B.ct (d.eX.symm χ) + v.2))⁻¹
  have hs : ∀ χ χ', s (χ + χ') * N.θ (N.c χ) (N.c χ') (d.ex v.2) = s χ * s χ' := by
    intro χ χ'
    obtain ⟨x, rfl⟩ := d.eX.surjective χ
    obtain ⟨x', rfl⟩ := d.eX.surjective χ'
    rw [← map_add d.eX, d.c_eq, d.c_eq]
    have h := d.cube_val (B.ct x) (B.ct x') v.2
    ext
    simp only [s, E, AddEquiv.symm_apply_apply, map_add, Units.val_mul, Units.val_inv_eq_inv_val,
      Units.val_mk0, AnArc.e_add]
    have hθ : (N.θ (d.ex (B.ct x)) (d.ex (B.ct x')) (d.ex v.2) : ℂ) =
        d.fr (B.ct x + B.ct x' + v.2) * d.fr (B.ct x) * d.fr (B.ct x') * d.fr v.2 /
          (d.fr (B.ct x + B.ct x') * d.fr (B.ct x + v.2) * d.fr (B.ct x' + v.2)) := by
      rw [eq_div_iff (by simp)]
      linear_combination h
    rw [hθ]
    field_simp
  refine ⟨⟨d.ex v.2, s, hs⟩, ⟨rfl, fun x => ?_⟩, ?_⟩
  · simp only [s, E, AddEquiv.symm_apply_apply, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
    rw [inv_mul_cancel_right₀ (Units.ne_zero _)]
  · rintro g ⟨hb, hg⟩
    refine NumD.Gt.ext hb (funext fun χ => ?_)
    obtain ⟨x, rfl⟩ := d.eX.surjective χ
    apply Units.ext
    have h := hg x
    simp only [s, E, AddEquiv.symm_apply_apply, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
    rw [eq_mul_inv_iff_mul_eq₀ (Units.ne_zero _)]
    exact h

/- English proof (translation)
Take `⟨w, hw⟩` from `d.ab.2.1 g.b`. Set `φ : B.X → ℂˣ` to `fun x => g.s (d.eX x) * d.fr (B.ct x + w) * (d.fr (B.ct x) * d.fr w)⁻¹`. Establish `hφ : ∀ x y, φ (x + y) = φ x * φ y`. Introduce `x y`. Establish `hm` using `g.mult (d.eX x) (d.eX y)`.

Rewrite `hm` using `[d.c_eq, d.c_eq, ← hw]`. Establish `hm'` using `congrArg Units.val hm`. Move the coercions through the operations in `at hm'`. Establish `h` using `d.cube_val (B.ct x) (B.ct y) w`. Use `ext`.

Simplify using `only [φ, map_add, Units.val_mul, Units.val_inv_eq_inv_val, mul_inv]`. Establish `hS : (g.s (d.eX x + d.eX y) : ℂ) = g.s (d.eX x) * g.s (d.eX y) / N.θ (d.ex (B.ct x)) (d.ex (B.ct y)) (d.ex w)`. Rewrite using `[eq_div_iff (Units.ne_zero _)]`. Conclude with `hm'`. Establish `hθ : (N.θ (d.ex (B.ct x)) (d.ex (B.ct y)) (d.ex w) : ℂ) = d.fr (B.ct x + B.ct y + w) * d.fr (B.ct x) * d.fr (B.ct y) * d.fr w / (d.fr (B.ct x + B.ct y) * d.fr (B.ct x + w) * d.fr (B.ct y + w))`.

Rewrite using `[eq_div_iff (by simp)]`. Take the linear combination `h`. Rewrite using `[hS, hθ]`. Clear the denominators using the available nonvanishing facts. Take `⟨l, hl⟩` from `exists_log_of_character φ hφ`.

Use `⟨(l, w), hw.symm, fun x => ?_⟩` and prove the remaining obligations. Use `show (g.s (d.eX x) : ℂ) * d.fr (B.ct x + w) = eTwoPi (l x) * d.fr (B.ct x) * d.fr w`. Rewrite using `[← hl x]`. Simplify using `only [φ, Units.val_mul, Units.val_inv_eq_inv_val]`. Clear the denominators using the available nonvanishing facts.
-/
theorem Dict.exists_isPt (g : N.Gt) : ∃ v, d.IsPt v g := by
  obtain ⟨w, hw⟩ := d.ab.2.1 g.b
  let φ : B.X → ℂˣ := fun x => g.s (d.eX x) * d.fr (B.ct x + w) * (d.fr (B.ct x) * d.fr w)⁻¹
  have hφ : ∀ x y, φ (x + y) = φ x * φ y := by
    intro x y
    have hm := g.mult (d.eX x) (d.eX y)
    rw [d.c_eq, d.c_eq, ← hw] at hm
    have hm' := congrArg Units.val hm
    push_cast at hm'
    have h := d.cube_val (B.ct x) (B.ct y) w
    ext
    simp only [φ, map_add, Units.val_mul, Units.val_inv_eq_inv_val, mul_inv]
    have hS : (g.s (d.eX x + d.eX y) : ℂ) =
        g.s (d.eX x) * g.s (d.eX y) / N.θ (d.ex (B.ct x)) (d.ex (B.ct y)) (d.ex w) := by
      rw [eq_div_iff (Units.ne_zero _)]
      exact hm'
    have hθ : (N.θ (d.ex (B.ct x)) (d.ex (B.ct y)) (d.ex w) : ℂ) =
        d.fr (B.ct x + B.ct y + w) * d.fr (B.ct x) * d.fr (B.ct y) * d.fr w /
          (d.fr (B.ct x + B.ct y) * d.fr (B.ct x + w) * d.fr (B.ct y + w)) := by
      rw [eq_div_iff (by simp)]
      linear_combination h
    rw [hS, hθ]
    field_simp
  obtain ⟨l, hl⟩ := exists_log_of_character φ hφ
  refine ⟨(l, w), hw.symm, fun x => ?_⟩
  show (g.s (d.eX x) : ℂ) * d.fr (B.ct x + w) = eTwoPi (l x) * d.fr (B.ct x) * d.fr w
  rw [← hl x]
  simp only [φ, Units.val_mul, Units.val_inv_eq_inv_val]
  field_simp

/- English proof (translation)
Take `⟨hb, hs⟩` from `h`. Take `⟨hb', hs'⟩` from `h'`. Use `⟨?_, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[NumD.Gt.mul_b, hb, hb', Prod.snd_add, d.ab.1]`. Establish `e1` using `hs x`.

Establish `e2` using `hs' x`. Establish `hc` using `d.cube_val (B.ct x) v.2 v'.2`. Rewrite using `[NumD.Gt.mul_s, d.c_eq, hb, hb']`. Simplify using `only [Prod.fst_add, Prod.snd_add, AddMonoidHom.add_apply, AnArc.e_add, Units.val_div_eq_div_val, Units.val_mul, ← add_assoc]`. Establish `h1 : (g.s (d.eX x) : ℂ) = eTwoPi (v.1 x) * d.fr (B.ct x) * d.fr v.2 / d.fr (B.ct x + v.2)`.

Rewrite using `[eq_div_iff (Units.ne_zero _)]`. Conclude with `e1`. Establish `h2 : (g'.s (d.eX x) : ℂ) = eTwoPi (v'.1 x) * d.fr (B.ct x) * d.fr v'.2 / d.fr (B.ct x + v'.2)`. Rewrite using `[eq_div_iff (Units.ne_zero _)]`. Conclude with `e2`.

Establish `hθ : (N.θ (d.ex (B.ct x)) (d.ex v.2) (d.ex v'.2) : ℂ) = d.fr (B.ct x + v.2 + v'.2) * d.fr (B.ct x) * d.fr v.2 * d.fr v'.2 / (d.fr (B.ct x + v.2) * d.fr (B.ct x + v'.2) * d.fr (v.2 + v'.2))`. Rewrite using `[eq_div_iff (by simp)]`. Take the linear combination `hc`. Rewrite using `[h1, h2, hθ]`. Clear the denominators using the available nonvanishing facts.
-/
theorem Dict.IsPt.add {d : Dict N B} {v v' : B.V} {g g' : N.Gt} (h : d.IsPt v g) (h' : d.IsPt v' g') :
    d.IsPt (v + v') (g * g') := by
  obtain ⟨hb, hs⟩ := h
  obtain ⟨hb', hs'⟩ := h'
  refine ⟨?_, fun x => ?_⟩
  · rw [NumD.Gt.mul_b, hb, hb', Prod.snd_add, d.ab.1]
  · have e1 := hs x
    have e2 := hs' x
    have hc := d.cube_val (B.ct x) v.2 v'.2
    rw [NumD.Gt.mul_s, d.c_eq, hb, hb']
    simp only [Prod.fst_add, Prod.snd_add, AddMonoidHom.add_apply, AnArc.e_add, Units.val_div_eq_div_val,
      Units.val_mul, ← add_assoc]
    have h1 : (g.s (d.eX x) : ℂ) = eTwoPi (v.1 x) * d.fr (B.ct x) * d.fr v.2 / d.fr (B.ct x + v.2) := by
      rw [eq_div_iff (Units.ne_zero _)]
      exact e1
    have h2 : (g'.s (d.eX x) : ℂ) = eTwoPi (v'.1 x) * d.fr (B.ct x) * d.fr v'.2 / d.fr (B.ct x + v'.2) := by
      rw [eq_div_iff (Units.ne_zero _)]
      exact e2
    have hθ : (N.θ (d.ex (B.ct x)) (d.ex v.2) (d.ex v'.2) : ℂ) =
        d.fr (B.ct x + v.2 + v'.2) * d.fr (B.ct x) * d.fr v.2 * d.fr v'.2 /
          (d.fr (B.ct x + v.2) * d.fr (B.ct x + v'.2) * d.fr (v.2 + v'.2)) := by
      rw [eq_div_iff (by simp)]
      linear_combination hc
    rw [h1, h2, hθ]
    field_simp

/- English proof (translation)
Use `⟨?_, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[NumD.io_b, d.c_eq, AnArc.degeneratingTori_basePeriodMap_snd, d.ab.1, (d.ab.2.2.1 _).mpr la.l.2, mul_one]`. Rewrite using `[NumD.io_s, AnArc.degeneratingTori_basePeriodMap_snd, AnArc.degeneratingTori_basePeriodMap_fst_apply, sub_eq_add_neg, AnArc.e_add, AnArc.e_add, AnArc.e_intCast, AnArc.e_neg_div, Complex.exp_neg, mul_one]`. Establish `h1` using `congrArg Units.val (N.ψ_add (d.eX la.y) (d.eX x))`. Establish `h2` using `congrArg Units.val (d.ψ_eq (la.y + x))`.

Establish `h3` using `B.psi_add la.y x`. Establish `h4` using `congrArg Units.val (d.ψ_eq la.y)`. Establish `h5` using `congrArg Units.val (d.ψ_eq x)`. Establish `h6` using `d.ab.2.2.2.2.1 la.l (B.ct la.y + B.ct x)`. Establish `h7` using `d.ab.2.2.2.2.1 la.l (B.ct la.y)`.

Establish `h8` using `B.ah_add la.l (B.ct la.y) (B.ct x)`. Move the coercions through the operations in `at h1 h2 h4 h5`. Rewrite `h2` using `[map_add d.eX, map_add B.ct]`. Rewrite `h6` using `[show B.ct la.y + B.ct x + (la.l : Fin B.gB → ℂ) = B.ct x + (B.ct la.y + la.l) by abel]`. Establish `key : ((N.τ (d.eX la.y) (d.eX x) : ℂ) * d.fr (B.ct x + (B.ct la.y + la.l)) * Complex.exp (Real.pi * B.H (B.ct x) la.l) - eTwoPi (B.T la.y x) * d.fr (B.ct x) * d.fr (B.ct la.y + la.l)) * ((N.ψ (d.eX la.y) : ℂ) * N.ψ (d.eX x) * B.ah la.l (B.ct la.y)) = 0`.

Take the linear combination `(-((d.fr (B.ct x + (B.ct la.y + la.l)) : ℂ) * Complex.exp (Real.pi * B.H (B.ct x) la.l) * B.ah la.l (B.ct la.y))) * h1 - (N.ψ (d.eX la.y + d.eX x) : ℂ) * d.fr (B.ct x + (B.ct la.y + la.l)) * h8 - (N.ψ (d.eX la.y + d.eX x) : ℂ) * h6 + h2 + h3 - (B.psi la.y : ℂ) * eTwoPi (B.T la.y …`. Establish `hne : ((N.ψ (d.eX la.y) : ℂ) * N.ψ (d.eX x) * B.ah la.l (B.ct la.y)) ≠ 0` using `mul_ne_zero (mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)) (B.ah_ne_zero _ _)`. Establish `hD` using `sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_right hne)`. Establish `hQ : Complex.exp (Real.pi * B.H (B.ct x) la.l) ≠ 0` using `Complex.exp_ne_zero _`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[mul_inv_cancel_right₀ hQ]`. Use `_ = _ := by rw [hD]; ring`.
-/
theorem Dict.analyticDictionary_isPoint_period_origin (la : B.La) : d.IsPt (B.P0 la) (N.io (d.eX la.y)) := by
  refine ⟨?_, fun x => ?_⟩
  · rw [NumD.io_b, d.c_eq, AnArc.degeneratingTori_basePeriodMap_snd, d.ab.1, (d.ab.2.2.1 _).mpr la.l.2, mul_one]
  · rw [NumD.io_s, AnArc.degeneratingTori_basePeriodMap_snd, AnArc.degeneratingTori_basePeriodMap_fst_apply, sub_eq_add_neg, AnArc.e_add, AnArc.e_add,
      AnArc.e_intCast, AnArc.e_neg_div, Complex.exp_neg, mul_one]
    have h1 := congrArg Units.val (N.ψ_add (d.eX la.y) (d.eX x))
    have h2 := congrArg Units.val (d.ψ_eq (la.y + x))
    have h3 := B.psi_add la.y x
    have h4 := congrArg Units.val (d.ψ_eq la.y)
    have h5 := congrArg Units.val (d.ψ_eq x)
    have h6 := d.ab.2.2.2.2.1 la.l (B.ct la.y + B.ct x)
    have h7 := d.ab.2.2.2.2.1 la.l (B.ct la.y)
    have h8 := B.ah_add la.l (B.ct la.y) (B.ct x)
    push_cast at h1 h2 h4 h5
    rw [map_add d.eX, map_add B.ct] at h2
    rw [show B.ct la.y + B.ct x + (la.l : Fin B.gB → ℂ) = B.ct x + (B.ct la.y + la.l) by abel] at h6
    have key : ((N.τ (d.eX la.y) (d.eX x) : ℂ) * d.fr (B.ct x + (B.ct la.y + la.l)) *
          Complex.exp (Real.pi * B.H (B.ct x) la.l) -
        eTwoPi (B.T la.y x) * d.fr (B.ct x) * d.fr (B.ct la.y + la.l)) *
        ((N.ψ (d.eX la.y) : ℂ) * N.ψ (d.eX x) * B.ah la.l (B.ct la.y)) = 0 := by
      linear_combination
        (-((d.fr (B.ct x + (B.ct la.y + la.l)) : ℂ) * Complex.exp (Real.pi * B.H (B.ct x) la.l) *
            B.ah la.l (B.ct la.y))) * h1
        - (N.ψ (d.eX la.y + d.eX x) : ℂ) * d.fr (B.ct x + (B.ct la.y + la.l)) * h8
        - (N.ψ (d.eX la.y + d.eX x) : ℂ) * h6 + h2 + h3
        - (B.psi la.y : ℂ) * eTwoPi (B.T la.y x) * h5
        - (N.ψ (d.eX x) : ℂ) * d.fr (B.ct x) * eTwoPi (B.T la.y x) * h4
        + (N.ψ (d.eX la.y) : ℂ) * N.ψ (d.eX x) * d.fr (B.ct x) * eTwoPi (B.T la.y x) * h7
    have hne : ((N.ψ (d.eX la.y) : ℂ) * N.ψ (d.eX x) * B.ah la.l (B.ct la.y)) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)) (B.ah_ne_zero _ _)
    have hD := sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_right hne)
    have hQ : Complex.exp (Real.pi * B.H (B.ct x) la.l) ≠ 0 := Complex.exp_ne_zero _
    calc (N.τ (d.eX la.y) (d.eX x) : ℂ) * d.fr (B.ct x + (B.ct la.y + la.l))
        = (N.τ (d.eX la.y) (d.eX x) : ℂ) * d.fr (B.ct x + (B.ct la.y + la.l)) *
            Complex.exp (Real.pi * B.H (B.ct x) la.l) * (Complex.exp (Real.pi * B.H (B.ct x) la.l))⁻¹ := by
          rw [mul_inv_cancel_right₀ hQ]
      _ = _ := by rw [hD]; ring

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hb, hs⟩`. Rewrite `hb` using `[NumD.Gt.one_b]`. Establish `hl : v.2 ∈ B.abelian₂` using `(d.ab.2.2.1 v.2).mp hb.symm`. Set `l : B.abelian₂` to `⟨v.2, hl⟩`.

Establish `hp0 : (1 : ℂ) = B.ah l 0 * d.fr v.2`. Establish `h0 : (d.fr 0 : ℂ) = B.ah l 0 * d.fr (0 + v.2)` using `d.ab.2.2.2.2.1 l 0`. Rewrite `h0` using `[zero_add, d.ab.2.2.2.1, Units.val_one]`. Then use the resulting hypothesis. Establish `hhalf : ∀ z : ℂ, eTwoPi (z / (2 * Complex.I)) = Complex.exp (Real.pi * z)`. Introduce `z`.

Use `AnArc.e_neg_div (-z)` as an intermediate fact. Rewrite `this` using `[neg_div, neg_neg, mul_neg, neg_neg]`. Then use the resulting hypothesis. Establish `hint : ∀ x, ∃ m : ℤ, (m : ℂ) = v.1 x + B.H (B.ct x) v.2 / (2 * Complex.I)`. Introduce `x`. Establish `hsx` using `hs x`.

Rewrite `hsx` using `[NumD.Gt.generator_inv_base, Units.val_one, one_mul]`. Establish `hp1 : (d.fr (B.ct x) : ℂ) = B.ah l (B.ct x) * d.fr (B.ct x + v.2)` using `d.ab.2.2.2.2.1 l (B.ct x)`. Establish `hq` using `B.ah_add l 0 (B.ct x)`. Rewrite `hq` using `[zero_add]`. Establish `hF : (d.fr (B.ct x + v.2) : ℂ) * (1 - eTwoPi (v.1 x) * Complex.exp (Real.pi * B.H (B.ct x) v.2)) = 0`.

Take the linear combination `hsx + eTwoPi (v.1 x) * d.fr v.2 * hp1 + eTwoPi (v.1 x) * d.fr v.2 * d.fr (B.ct x + v.2) * hq - eTwoPi (v.1 x) * Complex.exp (Real.pi * B.H (B.ct x) v.2) * d.fr (B.ct x + v.2) * hp0`. Establish `h1` using `sub_eq_zero.mp ((mul_eq_zero.mp hF).resolve_left (Units.ne_zero _))`. Establish `he : eTwoPi (v.1 x + B.H (B.ct x) v.2 / (2 * Complex.I)) = 1`. Rewrite using `[AnArc.e_add, hhalf]`. Conclude with `h1.symm`.

Take `⟨m, hm⟩` from `Complex.exp_eq_one_iff.mp he`. Use `⟨m, ?_⟩` and prove the remaining obligations. Establish `hπ : (2 * Real.pi * Complex.I : ℂ) ≠ 0` using `by simp [Real.pi_ne_zero, Complex.I_ne_zero]`. Apply `mul_left_cancel₀ hπ` to reduce the goal to its premises. Rewrite using `[hm]`.

Expand and normalize the polynomial expressions, which then agree. Set `n : B.X →+ ℤ` to `{ toFun := fun x => (hint x).choose map_zero' := Int.cast_injective (α := ℂ) (by`. Rewrite using `[(hint 0).choose_spec, Int.cast_zero]`. Use the proof step `simp)`. Use the proof step `map_add' := fun x y => Int.cast_injective (α := ℂ) (by`.

Rewrite using `[Int.cast_add, (hint (x + y)).choose_spec, (hint x).choose_spec, (hint y).choose_spec]`. Simplify using `only [map_add, AnArc.H_add_left]`. Use the proof step `ring) }`. Use `⟨AnArc.La.mk 0 n l, AnArc.La.mk_y _ _ _, ?_⟩` and prove the remaining obligations. Use `Prod.ext (AddMonoidHom.ext fun x => ?_) ?_` and prove the remaining obligations.

Rewrite using `[AnArc.degeneratingTori_basePeriodMap_fst_apply, AnArc.La.mk_y, AnArc.La.mk_n, AnArc.La.mk_l, map_zero, AddMonoidHom.zero_apply, zero_add] show v.1 x = ((hint x).choose : ℂ) - B.H (B.ct x) v.2 / (2 * Complex.I)`. Rewrite using `[(hint x).choose_spec]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[AnArc.degeneratingTori_basePeriodMap_snd, AnArc.La.mk_y, AnArc.La.mk_l, map_zero, zero_add]`. Introduce and unpack `⟨la, hy, rfl⟩`.

Establish `h` using `d.analyticDictionary_isPoint_period_origin la`. Rewrite `h` using `[hy, map_zero, NumD.io_zero]`. Then use the resulting hypothesis.
-/
theorem Dict.isPt_one_iff (v : B.V) : d.IsPt v 1 ↔ ∃ la : B.La, la.y = 0 ∧ v = B.P0 la := by
  constructor
  · rintro ⟨hb, hs⟩
    rw [NumD.Gt.one_b] at hb
    have hl : v.2 ∈ B.abelian₂ := (d.ab.2.2.1 v.2).mp hb.symm
    let l : B.abelian₂ := ⟨v.2, hl⟩
    have hp0 : (1 : ℂ) = B.ah l 0 * d.fr v.2 := by
      have h0 : (d.fr 0 : ℂ) = B.ah l 0 * d.fr (0 + v.2) := d.ab.2.2.2.2.1 l 0
      rwa [zero_add, d.ab.2.2.2.1, Units.val_one] at h0
    have hhalf : ∀ z : ℂ, eTwoPi (z / (2 * Complex.I)) = Complex.exp (Real.pi * z) := by
      intro z
      have := AnArc.e_neg_div (-z)
      rwa [neg_div, neg_neg, mul_neg, neg_neg] at this
    have hint : ∀ x, ∃ m : ℤ, (m : ℂ) = v.1 x + B.H (B.ct x) v.2 / (2 * Complex.I) := by
      intro x
      have hsx := hs x
      rw [NumD.Gt.generator_inv_base, Units.val_one, one_mul] at hsx
      have hp1 : (d.fr (B.ct x) : ℂ) = B.ah l (B.ct x) * d.fr (B.ct x + v.2) := d.ab.2.2.2.2.1 l (B.ct x)
      have hq := B.ah_add l 0 (B.ct x)
      rw [zero_add] at hq
      have hF : (d.fr (B.ct x + v.2) : ℂ) *
          (1 - eTwoPi (v.1 x) * Complex.exp (Real.pi * B.H (B.ct x) v.2)) = 0 := by
        linear_combination hsx + eTwoPi (v.1 x) * d.fr v.2 * hp1 +
          eTwoPi (v.1 x) * d.fr v.2 * d.fr (B.ct x + v.2) * hq -
          eTwoPi (v.1 x) * Complex.exp (Real.pi * B.H (B.ct x) v.2) * d.fr (B.ct x + v.2) * hp0
      have h1 := sub_eq_zero.mp ((mul_eq_zero.mp hF).resolve_left (Units.ne_zero _))
      have he : eTwoPi (v.1 x + B.H (B.ct x) v.2 / (2 * Complex.I)) = 1 := by
        rw [AnArc.e_add, hhalf]
        exact h1.symm
      obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp he
      refine ⟨m, ?_⟩
      have hπ : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
      apply mul_left_cancel₀ hπ
      rw [hm]
      ring
    let n : B.X →+ ℤ :=
      { toFun := fun x => (hint x).choose
        map_zero' := Int.cast_injective (α := ℂ) (by
          rw [(hint 0).choose_spec, Int.cast_zero]
          simp)
        map_add' := fun x y => Int.cast_injective (α := ℂ) (by
          rw [Int.cast_add, (hint (x + y)).choose_spec, (hint x).choose_spec, (hint y).choose_spec]
          simp only [map_add, AnArc.H_add_left]
          ring) }
    refine ⟨AnArc.La.mk 0 n l, AnArc.La.mk_y _ _ _, ?_⟩
    refine Prod.ext (AddMonoidHom.ext fun x => ?_) ?_
    · rw [AnArc.degeneratingTori_basePeriodMap_fst_apply, AnArc.La.mk_y, AnArc.La.mk_n, AnArc.La.mk_l, map_zero,
        AddMonoidHom.zero_apply, zero_add]
      show v.1 x = ((hint x).choose : ℂ) - B.H (B.ct x) v.2 / (2 * Complex.I)
      rw [(hint x).choose_spec]
      ring
    · rw [AnArc.degeneratingTori_basePeriodMap_snd, AnArc.La.mk_y, AnArc.La.mk_l, map_zero, zero_add]
  · rintro ⟨la, hy, rfl⟩
    have h := d.analyticDictionary_isPoint_period_origin la
    rwa [hy, map_zero, NumD.io_zero] at h

/- English proof (translation)
Introduce `_ _ _ _ _ d` and use `⟨d.existsUnique_isPt, d.exists_isPt, fun _ _ _ _ h h' => h.add h', d.isPt_one_iff, d.analyticDictionary_isPoint_period_origin⟩`.
-/
theorem ptSt : PtSt := fun _ _ _ _ _ d =>
  ⟨d.existsUnique_isPt, d.exists_isPt, fun _ _ _ _ h h' => h.add h', d.isPt_one_iff, d.analyticDictionary_isPoint_period_origin⟩

end GlobalTheory.Ex.Arch
end
