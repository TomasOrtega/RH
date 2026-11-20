import Formalism.EllipticTorsion.CoeffRing
import Formalism.EllipticTorsion.EllipticTorsionProofs.WChord
import Formalism.EllipticTorsion.EllipticTorsionProofs.ExistsUnitFactor
import Formalism.EllipticTorsion.EllipticTorsionProofs.WSubst
import Formalism.EllipticTorsion.EllipticTorsionProofs.WSeries

open PowerSeries

universe u

noncomputable section

namespace Formalism.ELL
namespace CubeThreeAlt

open WeierstrassChordSeries

section Alg
variable {R : Type*} [CommRing R]

def Hv (a1 a2 a3 a4 a6 z v v' : R) : R :=
  a1 * z + a2 * z ^ 2 + a3 * (v + v') + a4 * z * (v + v') + a6 * (v ^ 2 + v * v' + v' ^ 2) - 1

/- English proof (translation)
Unfold `Formalism.ELL.WeierstrassChordSeries.G Hv`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma G_sub (a1 a2 a3 a4 a6 z v v' : R) :
    G a1 a2 a3 a4 a6 z v - G a1 a2 a3 a4 a6 z v' = (v - v') * Hv a1 a2 a3 a4 a6 z v v' := by
  unfold Formalism.ELL.WeierstrassChordSeries.G Hv
  ring

/- English proof (translation)
Take `⟨-, h2, h3⟩` from `Formalism.ELL.WeierstrassChordSeries.vieta hab ha hb he1`. Rewrite using `[Formalism.ELL.WeierstrassChordSeries.G_line]`. Take the linear combination `c ^ 2 * he1 - c * h2 + h3`.
-/
lemma line_fact [IsDomain R] {a1 a2 a3 a4 a6 l n a b z : R} (hab : a ≠ b)
    (ha : G a1 a2 a3 a4 a6 a (l * a + n) = 0) (hb : G a1 a2 a3 a4 a6 b (l * b + n) = 0)
    (he1 : c3 a2 a4 a6 l * (a + b + z) + c2 a1 a2 a3 a4 a6 l n = 0) (c : R) :
    G a1 a2 a3 a4 a6 c (l * c + n) = c3 a2 a4 a6 l * (c - a) * (c - b) * (c - z) := by
  obtain ⟨-, h2, h3⟩ := Formalism.ELL.WeierstrassChordSeries.vieta hab ha hb he1
  rw [Formalism.ELL.WeierstrassChordSeries.G_line]
  linear_combination c ^ 2 * he1 - c * h2 + h3

/- English proof (translation)
Establish `hA : Formalism.ELL.WeierstrassChordSeries.c3 a2 a4 a6 l = 1 + a2 * l + a4 * l ^ 2 + a6 * l ^ 3` using `rfl`. Establish `hE : u * (Formalism.ELL.WeierstrassChordSeries.c3 a2 a4 a6 l * u ^ 2 + (a1 * l + a3 * l ^ 2) * u - l) = 0`. Unfold `Formalism.ELL.WeierstrassChordSeries.G at hG`. Rewrite using `[hA]`. Take the linear combination `hG`.

Establish `hE'` using `(mul_eq_zero.mp hE).resolve_left hu`. Establish `h1 : d * (Formalism.ELL.WeierstrassChordSeries.c3 a2 a4 a6 l * u * s + l) = 0`. Take the linear combination `(Formalism.ELL.WeierstrassChordSeries.c3 a2 a4 a6 l * u) * hsd + hE' + l * hd`. Establish `h1'` using `(mul_eq_zero.mp h1).resolve_left hd0`. Establish `h2 : u * (a1 * l + a3 * l ^ 2 + Formalism.ELL.WeierstrassChordSeries.c3 a2 a4 a6 l * u + Formalism.ELL.WeierstrassChordSeries.c3 a2 a4 a6 l * s) = 0`.

Take the linear combination `hE' + h1'`. Establish `h2'` using `(mul_eq_zero.mp h2).resolve_left hu`. Unfold `Formalism.ELL.WeierstrassChordSeries.G`. Take the linear combination `(-c ^ 3) * hA + c ^ 2 * h2' - c * h1'`.
-/
lemma q_fact [IsDomain R] {a1 a2 a3 a4 a6 u s d l c : R} (hu : u ≠ 0) (hd0 : d ≠ 0)
    (hsd : s * d = u) (hd : d = -1 + a1 * u + a3 * (l * u))
    (hG : G a1 a2 a3 a4 a6 u (l * u) = 0) :
    G a1 a2 a3 a4 a6 c (l * c) = c * c3 a2 a4 a6 l * (c - u) * (c - s) := by
  have hA : Formalism.ELL.WeierstrassChordSeries.c3 a2 a4 a6 l = 1 + a2 * l + a4 * l ^ 2 + a6 * l ^ 3 := rfl
  have hE : u * (Formalism.ELL.WeierstrassChordSeries.c3 a2 a4 a6 l * u ^ 2 + (a1 * l + a3 * l ^ 2) * u - l) = 0 := by
    unfold Formalism.ELL.WeierstrassChordSeries.G at hG
    rw [hA]
    linear_combination hG
  have hE' := (mul_eq_zero.mp hE).resolve_left hu
  have h1 : d * (Formalism.ELL.WeierstrassChordSeries.c3 a2 a4 a6 l * u * s + l) = 0 := by
    linear_combination (Formalism.ELL.WeierstrassChordSeries.c3 a2 a4 a6 l * u) * hsd + hE' + l * hd
  have h1' := (mul_eq_zero.mp h1).resolve_left hd0
  have h2 : u * (a1 * l + a3 * l ^ 2 + Formalism.ELL.WeierstrassChordSeries.c3 a2 a4 a6 l * u + Formalism.ELL.WeierstrassChordSeries.c3 a2 a4 a6 l * s) = 0 := by
    linear_combination hE' + h1'
  have h2' := (mul_eq_zero.mp h2).resolve_left hu
  unfold Formalism.ELL.WeierstrassChordSeries.G
  linear_combination (-c ^ 3) * hA + c ^ 2 * h2' - c * h1'

/- English proof (translation)
Rewrite using `[Matrix.det_fin_three]`. Simplify using `only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]`. Take the linear combination `(V 1 * V 2 * (t 2 - t 1)) * h 0 + (V 0 * V 2 * (t 0 - t 2)) * h 1 + (V 0 * V 1 * (t 1 - t 0)) * h 2`.
-/
lemma det_rows (t V ww : Fin 3 → R) (h : ∀ i, t i ^ 3 = V i * ww i) :
    (Matrix.of fun i => ![t i ^ 3, t i * V i, -V i]).det
      = -(V 0 * V 1 * V 2) * ((ww 1 - ww 0) * (t 2 - t 0) - (ww 2 - ww 0) * (t 1 - t 0)) := by
  rw [Matrix.det_fin_three]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  linear_combination (V 1 * V 2 * (t 2 - t 1)) * h 0 + (V 0 * V 2 * (t 0 - t 2)) * h 1
    + (V 0 * V 1 * (t 1 - t 0)) * h 2

/- English proof (translation)
Unfold `Hv`. Establish `hvv : v + v' ∈ T` using `T.add_mem hv hv'`. Conclude with `T.sub_mem (T.add_mem (T.add_mem (T.add_mem (T.add_mem (T.mul_mem h1 hz) (T.mul_mem h2 (T.pow_mem hz 2))) (T.mul_mem h3 hvv)) (T.mul_mem (T.mul_mem h4 hz) hvv)) (T.mul_mem h6 (T.add_mem (T.add_mem (T.pow_mem hv 2) (T.mul_mem hv hv')) (T.pow_mem hv' 2)))) T.one_mem`.
-/
lemma Hv_mem (T : Subring R) {a1 a2 a3 a4 a6 z v v' : R} (h1 : a1 ∈ T) (h2 : a2 ∈ T)
    (h3 : a3 ∈ T) (h4 : a4 ∈ T) (h6 : a6 ∈ T) (hz : z ∈ T) (hv : v ∈ T) (hv' : v' ∈ T) :
    Hv a1 a2 a3 a4 a6 z v v' ∈ T := by
  unfold Hv
  have hvv : v + v' ∈ T := T.add_mem hv hv'
  exact T.sub_mem (T.add_mem (T.add_mem (T.add_mem (T.add_mem (T.mul_mem h1 hz)
    (T.mul_mem h2 (T.pow_mem hz 2))) (T.mul_mem h3 hvv)) (T.mul_mem (T.mul_mem h4 hz) hvv))
    (T.mul_mem h6 (T.add_mem (T.add_mem (T.pow_mem hv 2) (T.mul_mem hv hv')) (T.pow_mem hv' 2)))) T.one_mem

end Alg

section Mser
variable {K : Type u} [Field K]

local notation "cc" => MvPowerSeries.constantCoeff

abbrev TT (W : WeierstrassCurve K) (σ : Type) : Subring (MvPowerSeries σ K) :=
  (MvPowerSeries.map (algebraMap (Sadj W) K)).range

variable {W : WeierstrassCurve K} {σ : Type}

/- English proof (translation)
Rewrite using `[TT, RingHom.mem_range]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨ψ, rfl⟩ e`. Rewrite using `[MvPowerSeries.coeff_map]`. Conclude with `(MvPowerSeries.coeff e ψ).2`.

Introduce `h`. Use `⟨(fun e => ⟨MvPowerSeries.coeff e φ, h e⟩ : MvPowerSeries σ (Formalism.ELL.WeierstrassChordSeries.Sadj W)), ?_⟩` and prove the remaining obligations. Use extensionality with `e`. Both sides reduce to the same expression.
-/
lemma mem_TT {φ : MvPowerSeries σ K} : φ ∈ TT W σ ↔ ∀ e, MvPowerSeries.coeff e φ ∈ Sadj W := by
  rw [TT, RingHom.mem_range]
  constructor
  · rintro ⟨ψ, rfl⟩ e
    rw [MvPowerSeries.coeff_map]
    exact (MvPowerSeries.coeff e ψ).2
  · intro h
    refine ⟨(fun e => ⟨MvPowerSeries.coeff e φ, h e⟩ : MvPowerSeries σ (Formalism.ELL.WeierstrassChordSeries.Sadj W)), ?_⟩
    ext e
    rfl

/- English proof (translation)
Establish `h'` using `h`. Rewrite `h'` using `[TT, RingHom.mem_range]`. Take `⟨ψ, hψ⟩` from `h'`. Establish `hc : ((MvPowerSeries.constantCoeff ψ : Formalism.ELL.WeierstrassChordSeries.Sadj W) : K) = cc φ`. Rewrite using `[← hψ, MvPowerSeries.constantCoeff_map]`.

Both sides reduce to the same expression. Establish `hmul : MvPowerSeries.constantCoeff ψ * (⟨(cc φ)⁻¹, hi⟩ : Formalism.ELL.WeierstrassChordSeries.Sadj W) = 1` using `Subtype.ext (by show ((MvPowerSeries.constantCoeff ψ : Formalism.ELL.WeierstrassChordSeries.Sadj W) : K) * (cc φ)⁻¹ = 1`. Rewrite using `[hc]`. Conclude with `mul_inv_cancel₀ h0)`. Establish `hu : IsUnit (MvPowerSeries.constantCoeff ψ)` using `⟨⟨_, _, hmul, (mul_comm _ _).trans hmul⟩, rfl⟩`.

Choose the witnesses or unpack the hypotheses as in `⟨g, hg⟩ : ∃ g, ψ * g = 1 := by`. Conclude with `(MvPowerSeries.isUnit_iff_constantCoeff.mpr hu).exists_right_inv`. Establish `hφg : φ * MvPowerSeries.map (algebraMap (Formalism.ELL.WeierstrassChordSeries.Sadj W) K) g = 1`. Rewrite using `[← hψ, ← map_mul, hg, map_one]`. Establish `key : φ⁻¹ = MvPowerSeries.map (algebraMap (Formalism.ELL.WeierstrassChordSeries.Sadj W) K) g`.

Combine the equalities or inequalities in the displayed calculation. Use `_ = MvPowerSeries.map (algebraMap (Formalism.ELL.WeierstrassChordSeries.Sadj W) K) g := by`. Rewrite using `[← mul_assoc, MvPowerSeries.inv_mul_cancel _ h0, one_mul]`. Rewrite using `[key]`. Conclude with `RingHom.mem_range_self _ g`.
-/
lemma inv_mem_TT {φ : MvPowerSeries σ K} (h : φ ∈ TT W σ) (h0 : cc φ ≠ 0)
    (hi : (cc φ)⁻¹ ∈ Sadj W) : φ⁻¹ ∈ TT W σ := by
  have h' := h
  rw [TT, RingHom.mem_range] at h'
  obtain ⟨ψ, hψ⟩ := h'
  have hc : ((MvPowerSeries.constantCoeff ψ : Formalism.ELL.WeierstrassChordSeries.Sadj W) : K) = cc φ := by
    rw [← hψ, MvPowerSeries.constantCoeff_map]
    rfl
  have hmul : MvPowerSeries.constantCoeff ψ * (⟨(cc φ)⁻¹, hi⟩ : Formalism.ELL.WeierstrassChordSeries.Sadj W) = 1 :=
    Subtype.ext (by
      show ((MvPowerSeries.constantCoeff ψ : Formalism.ELL.WeierstrassChordSeries.Sadj W) : K) * (cc φ)⁻¹ = 1
      rw [hc]
      exact mul_inv_cancel₀ h0)
  have hu : IsUnit (MvPowerSeries.constantCoeff ψ) := ⟨⟨_, _, hmul, (mul_comm _ _).trans hmul⟩, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g, ψ * g = 1 := by
    exact (MvPowerSeries.isUnit_iff_constantCoeff.mpr hu).exists_right_inv
  have hφg : φ * MvPowerSeries.map (algebraMap (Formalism.ELL.WeierstrassChordSeries.Sadj W) K) g = 1 := by
    rw [← hψ, ← map_mul, hg, map_one]
  have key : φ⁻¹ = MvPowerSeries.map (algebraMap (Formalism.ELL.WeierstrassChordSeries.Sadj W) K) g := by
    calc φ⁻¹ = φ⁻¹ * (φ * MvPowerSeries.map (algebraMap (Formalism.ELL.WeierstrassChordSeries.Sadj W) K) g) := by rw [hφg, mul_one]
    _ = MvPowerSeries.map (algebraMap (Formalism.ELL.WeierstrassChordSeries.Sadj W) K) g := by
      rw [← mul_assoc, MvPowerSeries.inv_mul_cancel _ h0, one_mul]
  rw [key]
  exact RingHom.mem_range_self _ g

/- English proof (translation)
Rewrite using `[mem_TT]`. Introduce `e`. Rewrite using `[MvPowerSeries.coeff_C]`. Use `split_ifs`. Conclude with `ha`.

Conclude with `zero_mem _`.
-/
lemma C_mem_TT {a : K} (ha : a ∈ Sadj W) : (MvPowerSeries.C a : MvPowerSeries σ K) ∈ TT W σ := by
  classical
  rw [mem_TT]
  intro e
  rw [MvPowerSeries.coeff_C]
  split_ifs
  · exact ha
  · exact zero_mem _

/- English proof (translation)
Rewrite using `[mem_TT]`. Introduce `e`. Rewrite using `[MvPowerSeries.coeff_X]`. Use `split_ifs`. Conclude with `one_mem _`.

Conclude with `zero_mem _`.
-/
lemma X_mem_TT (i : σ) : (MvPowerSeries.X i : MvPowerSeries σ K) ∈ TT W σ := by
  classical
  rw [mem_TT]
  intro e
  rw [MvPowerSeries.coeff_X]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

/- English proof (translation)
Conclude with `MvPowerSeries.hasSubst_of_constantCoeff_zero ha`.
-/
private theorem hasSubst_of_cc_zero_lemma {τ : Type} [Finite τ] {a : τ → MvPowerSeries σ K} (ha : ∀ i, cc (a i) = 0) :
    MvPowerSeries.HasSubst a := by
  exact MvPowerSeries.hasSubst_of_constantCoeff_zero ha

/- English proof (translation)
Establish `hA : MvPowerSeries.HasSubst a` using `hasSubst_of_cc_zero_lemma ha0`. Rewrite `hf`, the goal using `[mem_TT]`. Introduce `e`. Rewrite using `[MvPowerSeries.coeff_subst hA, finsum_def]`. Use `split_ifs with hfin`.

Use `sum_mem fun d _ => ?_` and prove the remaining obligations. Rewrite using `[smul_eq_mul]`. Use `mul_mem (hf d) ?_` and prove the remaining obligations. Establish `hp : (d.prod fun s n => a s ^ n) ∈ TT W σ`. Unfold `Finsupp.prod`.

Conclude with `prod_mem fun i _ => pow_mem (ha i) _`. Conclude with `(mem_TT.mp hp) e`. Conclude with `zero_mem _`.
-/
lemma subst_mem {τ : Type} [Finite τ] {f : MvPowerSeries τ K} (hf : f ∈ TT W τ)
    {a : τ → MvPowerSeries σ K} (ha : ∀ i, a i ∈ TT W σ) (ha0 : ∀ i, cc (a i) = 0) :
    MvPowerSeries.subst a f ∈ TT W σ := by
  classical
  have hA : MvPowerSeries.HasSubst a := hasSubst_of_cc_zero_lemma ha0
  rw [mem_TT] at hf ⊢
  intro e
  rw [MvPowerSeries.coeff_subst hA, finsum_def]
  split_ifs with hfin
  · refine sum_mem fun d _ => ?_
    rw [smul_eq_mul]
    refine mul_mem (hf d) ?_
    have hp : (d.prod fun s n => a s ^ n) ∈ TT W σ := by
      unfold Finsupp.prod
      exact prod_mem fun i _ => pow_mem (ha i) _
    exact (mem_TT.mp hp) e
  · exact zero_mem _

/- English proof (translation)
Establish `hfU : (f : MvPowerSeries Unit K) ∈ TT W Unit`. Rewrite using `[mem_TT]`. Introduce `e`. Establish `he : e = Finsupp.single () (e ())`. Use `ext`.

Simplify using the standard rewrite rules. Rewrite using `[he]`. Conclude with `hf (e ())`. Conclude with `subst_mem hfU (fun _ => ha) (fun _ => ha0)`.
-/
lemma psubst_mem {f : PowerSeries K} (hf : ∀ n, coeff n f ∈ Sadj W)
    {a : MvPowerSeries σ K} (ha : a ∈ TT W σ) (ha0 : cc a = 0) : f.subst a ∈ TT W σ := by
  have hfU : (f : MvPowerSeries Unit K) ∈ TT W Unit := by
    rw [mem_TT]
    intro e
    have he : e = Finsupp.single () (e ()) := by
      ext
      simp
    rw [he]
    exact hf (e ())
  exact subst_mem hfU (fun _ => ha) (fun _ => ha0)

def GG (W : WeierstrassCurve K) (z v : MvPowerSeries σ K) : MvPowerSeries σ K :=
  G (MvPowerSeries.C W.a₁) (MvPowerSeries.C W.a₂) (MvPowerSeries.C W.a₃) (MvPowerSeries.C W.a₄)
    (MvPowerSeries.C W.a₆) z v

def chordCoeffCubicAt (W : WeierstrassCurve K) (l : MvPowerSeries σ K) : MvPowerSeries σ K :=
  c3 (MvPowerSeries.C W.a₂) (MvPowerSeries.C W.a₄) (MvPowerSeries.C W.a₆) l

def chordCoeffQuadraticAt (W : WeierstrassCurve K) (l n : MvPowerSeries σ K) : MvPowerSeries σ K :=
  c2 (MvPowerSeries.C W.a₁) (MvPowerSeries.C W.a₂) (MvPowerSeries.C W.a₃) (MvPowerSeries.C W.a₄)
    (MvPowerSeries.C W.a₆) l n

def DDs (W : WeierstrassCurve K) (l n z : MvPowerSeries σ K) : MvPowerSeries σ K :=
  -1 + MvPowerSeries.C W.a₁ * z + MvPowerSeries.C W.a₃ * (l * z + n)

def HHs (W : WeierstrassCurve K) (z v v' : MvPowerSeries σ K) : MvPowerSeries σ K :=
  Hv (MvPowerSeries.C W.a₁) (MvPowerSeries.C W.a₂) (MvPowerSeries.C W.a₃) (MvPowerSeries.C W.a₄)
    (MvPowerSeries.C W.a₆) z v v'

/- English proof (translation)
Unfold `Formalism.ELL.WEqAt GG Formalism.ELL.WeierstrassChordSeries.G`. Simplify using `only [MvPowerSeries.smul_eq_C_mul]`. Apply the tactic sequence `constructor <;> intro h <;> linear_combination -h`.
-/
lemma weq_iff' (W : WeierstrassCurve K) (s v : MvPowerSeries σ K) :
    WEqAt W s v ↔ GG W s v = 0 := by
  unfold Formalism.ELL.WEqAt GG Formalism.ELL.WeierstrassChordSeries.G
  simp only [MvPowerSeries.smul_eq_C_mul]
  constructor <;> intro h <;> linear_combination -h

/- English proof (translation)
Apply the tactic sequence `fin_cases i <;> exact Algebra.subset_adjoin (by simp)`.
-/
lemma a_mem (i : Fin 5) : ![W.a₁, W.a₂, W.a₃, W.a₄, W.a₆] i ∈ Sadj W := by
  fin_cases i <;> exact Algebra.subset_adjoin (by simp)

/- English proof (translation)
Assemble the required witnesses or components as `⟨C_mem_TT (Algebra.subset_adjoin (by simp)), C_mem_TT (Algebra.subset_adjoin (by simp)), C_mem_TT (Algebra.subset_adjoin (by simp)), C_mem_TT (Algebra.subset_adjoin (by simp)), C_mem_TT (Algebra.subset_adjoin (by simp))⟩`.
-/
lemma Ca_mem : (MvPowerSeries.C W.a₁ : MvPowerSeries σ K) ∈ TT W σ ∧
    (MvPowerSeries.C W.a₂ : MvPowerSeries σ K) ∈ TT W σ ∧
    (MvPowerSeries.C W.a₃ : MvPowerSeries σ K) ∈ TT W σ ∧
    (MvPowerSeries.C W.a₄ : MvPowerSeries σ K) ∈ TT W σ ∧
    (MvPowerSeries.C W.a₆ : MvPowerSeries σ K) ∈ TT W σ :=
  ⟨C_mem_TT (Algebra.subset_adjoin (by simp)), C_mem_TT (Algebra.subset_adjoin (by simp)),
    C_mem_TT (Algebra.subset_adjoin (by simp)), C_mem_TT (Algebra.subset_adjoin (by simp)),
    C_mem_TT (Algebra.subset_adjoin (by simp))⟩

variable {w : PowerSeries K}

/- English proof (translation)
Take `⟨h0, h1, h2, -⟩` from `Formalism.ELL.WeierstrassChordSeries.w_low hw`. Use extensionality with `n`. Rewrite using `[PowerSeries.coeff_X_pow_mul', Formalism.ELL.wU]`. Use `split_ifs with hn`. Rewrite using `[PowerSeries.coeff_mk, Nat.sub_add_cancel hn]`.

Apply the tactic sequence `interval_cases n <;> assumption`.
-/
lemma w_eq (hw : WFixed W w) : w = X ^ 3 * wU w := by
  obtain ⟨h0, h1, h2, -⟩ := Formalism.ELL.WeierstrassChordSeries.w_low hw
  ext n
  rw [PowerSeries.coeff_X_pow_mul', Formalism.ELL.wU]
  split_ifs with hn
  · rw [PowerSeries.coeff_mk, Nat.sub_add_cancel hn]
  · interval_cases n <;> assumption

/- English proof (translation)
Rewrite using `[← PowerSeries.coeff_zero_eq_constantCoeff_apply, Formalism.ELL.wU, PowerSeries.coeff_mk]`. Conclude with `(Formalism.ELL.WeierstrassChordSeries.w_low hw).2.2.2`.
-/
lemma wU_cc (hw : WFixed W w) : constantCoeff (wU w) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Formalism.ELL.wU, PowerSeries.coeff_mk]
  exact (Formalism.ELL.WeierstrassChordSeries.w_low hw).2.2.2

/- English proof (translation)
Rewrite using `[Formalism.ELL.wU, PowerSeries.coeff_mk]`. Conclude with `Formalism.ELL.WeierstrassChordSeries.w_coeff_mem hw _`.
-/
lemma wU_coeff_mem (hw : WFixed W w) (n : ℕ) : coeff n (wU w) ∈ Sadj W := by
  rw [Formalism.ELL.wU, PowerSeries.coeff_mk]
  exact Formalism.ELL.WeierstrassChordSeries.w_coeff_mem hw _

/- English proof (translation)
Establish `hA0` using `Formalism.ELL.WeierstrassChordSeries.constantCoeff_chordCoeffCubic hw`. Establish `hD0` using `Formalism.ELL.WeierstrassChordSeries.dd_cc hw`. Establish `hAne : cc (Formalism.ELL.WeierstrassChordSeries.C3 W w) ≠ 0` using `by rw [hA0]; exact one_ne_zero`. Establish `hDne : cc (Formalism.ELL.WeierstrassChordSeries.dd W w) ≠ 0` using `by rw [hD0]; exact neg_ne_zero.mpr one_ne_zero`. Establish `c1 : Formalism.ELL.WeierstrassChordSeries.ca W.a₁ ∈ Formalism.ELL.WeierstrassChordSeries.T W` using `Formalism.ELL.WeierstrassChordSeries.constSeries_mem_integralSeries (by simp)`.

Establish `c2 : Formalism.ELL.WeierstrassChordSeries.ca W.a₂ ∈ Formalism.ELL.WeierstrassChordSeries.T W` using `Formalism.ELL.WeierstrassChordSeries.constSeries_mem_integralSeries (by simp)`. Establish `c3 : Formalism.ELL.WeierstrassChordSeries.ca W.a₃ ∈ Formalism.ELL.WeierstrassChordSeries.T W` using `Formalism.ELL.WeierstrassChordSeries.constSeries_mem_integralSeries (by simp)`. Establish `c4 : Formalism.ELL.WeierstrassChordSeries.ca W.a₄ ∈ Formalism.ELL.WeierstrassChordSeries.T W` using `Formalism.ELL.WeierstrassChordSeries.constSeries_mem_integralSeries (by simp)`. Establish `c6 : Formalism.ELL.WeierstrassChordSeries.ca W.a₆ ∈ Formalism.ELL.WeierstrassChordSeries.T W` using `Formalism.ELL.WeierstrassChordSeries.constSeries_mem_integralSeries (by simp)`. Establish `hl` using `Formalism.ELL.WeierstrassChordSeries.slope_mem_integralSeries hw`.

Establish `hn` using `Formalism.ELL.WeierstrassChordSeries.intercept_mem_integralSeries hw`. Establish `hA : Formalism.ELL.WeierstrassChordSeries.C3 W w ∈ Formalism.ELL.WeierstrassChordSeries.T W`. Unfold `Formalism.ELL.WeierstrassChordSeries.C3`. Conclude with `Formalism.ELL.WeierstrassChordSeries.lineCoeffCubic_mem _ c2 c4 c6 hl`. Establish `hAi : (Formalism.ELL.WeierstrassChordSeries.C3 W w)⁻¹ ∈ Formalism.ELL.WeierstrassChordSeries.T W` using `Formalism.ELL.WeierstrassChordSeries.inv_mem_integralSeries hA hAne (by rw [hA0, inv_one]; exact one_mem _)`.

Establish `hQ : Formalism.ELL.WeierstrassChordSeries.C2 W w ∈ Formalism.ELL.WeierstrassChordSeries.T W`. Unfold `Formalism.ELL.WeierstrassChordSeries.C2`. Conclude with `Formalism.ELL.WeierstrassChordSeries.lineCoeffQuadratic_mem _ c1 c2 c3 c4 c6 hl hn`. Establish `hz : Formalism.ELL.WeierstrassChordSeries.z3 W w ∈ Formalism.ELL.WeierstrassChordSeries.T W`. Unfold `Formalism.ELL.WeierstrassChordSeries.z3`.

Conclude with `sub_mem (sub_mem (neg_mem (Formalism.ELL.WeierstrassChordSeries.X_mem_T 0)) (Formalism.ELL.WeierstrassChordSeries.X_mem_T 1)) (mul_mem hQ hAi)`. Establish `hv : Formalism.ELL.WeierstrassChordSeries.w3 W w ∈ Formalism.ELL.WeierstrassChordSeries.T W`. Unfold `Formalism.ELL.WeierstrassChordSeries.w3`. Conclude with `add_mem (mul_mem hl hz) hn`. Establish `hD : Formalism.ELL.WeierstrassChordSeries.dd W w ∈ Formalism.ELL.WeierstrassChordSeries.T W`.

Unfold `Formalism.ELL.WeierstrassChordSeries.dd`. Conclude with `add_mem (add_mem (neg_mem (one_mem _)) (mul_mem c1 hz)) (mul_mem c3 hv)`. Conclude with `⟨MvPowerSeries.mul_inv_cancel _ hAne, MvPowerSeries.mul_inv_cancel _ hDne, hAi, Formalism.ELL.WeierstrassChordSeries.inv_mem_integralSeries hD hDne (by rw [hD0, inv_neg, inv_one]; exact neg_mem (one_mem _))⟩`.
-/
lemma chordCoeffCubic_inversionDenom_inv (hw : WFixed W w) : C3 W w * (C3 W w)⁻¹ = 1 ∧ dd W w * (dd W w)⁻¹ = 1 ∧
    (C3 W w)⁻¹ ∈ T W ∧ (dd W w)⁻¹ ∈ T W := by
  have hA0 := Formalism.ELL.WeierstrassChordSeries.constantCoeff_chordCoeffCubic hw
  have hD0 := Formalism.ELL.WeierstrassChordSeries.dd_cc hw
  have hAne : cc (Formalism.ELL.WeierstrassChordSeries.C3 W w) ≠ 0 := by rw [hA0]; exact one_ne_zero
  have hDne : cc (Formalism.ELL.WeierstrassChordSeries.dd W w) ≠ 0 := by rw [hD0]; exact neg_ne_zero.mpr one_ne_zero
  have c1 : Formalism.ELL.WeierstrassChordSeries.ca W.a₁ ∈ Formalism.ELL.WeierstrassChordSeries.T W := Formalism.ELL.WeierstrassChordSeries.constSeries_mem_integralSeries (by simp)
  have c2 : Formalism.ELL.WeierstrassChordSeries.ca W.a₂ ∈ Formalism.ELL.WeierstrassChordSeries.T W := Formalism.ELL.WeierstrassChordSeries.constSeries_mem_integralSeries (by simp)
  have c3 : Formalism.ELL.WeierstrassChordSeries.ca W.a₃ ∈ Formalism.ELL.WeierstrassChordSeries.T W := Formalism.ELL.WeierstrassChordSeries.constSeries_mem_integralSeries (by simp)
  have c4 : Formalism.ELL.WeierstrassChordSeries.ca W.a₄ ∈ Formalism.ELL.WeierstrassChordSeries.T W := Formalism.ELL.WeierstrassChordSeries.constSeries_mem_integralSeries (by simp)
  have c6 : Formalism.ELL.WeierstrassChordSeries.ca W.a₆ ∈ Formalism.ELL.WeierstrassChordSeries.T W := Formalism.ELL.WeierstrassChordSeries.constSeries_mem_integralSeries (by simp)
  have hl := Formalism.ELL.WeierstrassChordSeries.slope_mem_integralSeries hw
  have hn := Formalism.ELL.WeierstrassChordSeries.intercept_mem_integralSeries hw
  have hA : Formalism.ELL.WeierstrassChordSeries.C3 W w ∈ Formalism.ELL.WeierstrassChordSeries.T W := by
    unfold Formalism.ELL.WeierstrassChordSeries.C3
    exact Formalism.ELL.WeierstrassChordSeries.lineCoeffCubic_mem _ c2 c4 c6 hl
  have hAi : (Formalism.ELL.WeierstrassChordSeries.C3 W w)⁻¹ ∈ Formalism.ELL.WeierstrassChordSeries.T W :=
    Formalism.ELL.WeierstrassChordSeries.inv_mem_integralSeries hA hAne (by rw [hA0, inv_one]; exact one_mem _)
  have hQ : Formalism.ELL.WeierstrassChordSeries.C2 W w ∈ Formalism.ELL.WeierstrassChordSeries.T W := by
    unfold Formalism.ELL.WeierstrassChordSeries.C2
    exact Formalism.ELL.WeierstrassChordSeries.lineCoeffQuadratic_mem _ c1 c2 c3 c4 c6 hl hn
  have hz : Formalism.ELL.WeierstrassChordSeries.z3 W w ∈ Formalism.ELL.WeierstrassChordSeries.T W := by
    unfold Formalism.ELL.WeierstrassChordSeries.z3
    exact sub_mem (sub_mem (neg_mem (Formalism.ELL.WeierstrassChordSeries.X_mem_T 0)) (Formalism.ELL.WeierstrassChordSeries.X_mem_T 1)) (mul_mem hQ hAi)
  have hv : Formalism.ELL.WeierstrassChordSeries.w3 W w ∈ Formalism.ELL.WeierstrassChordSeries.T W := by
    unfold Formalism.ELL.WeierstrassChordSeries.w3
    exact add_mem (mul_mem hl hz) hn
  have hD : Formalism.ELL.WeierstrassChordSeries.dd W w ∈ Formalism.ELL.WeierstrassChordSeries.T W := by
    unfold Formalism.ELL.WeierstrassChordSeries.dd
    exact add_mem (add_mem (neg_mem (one_mem _)) (mul_mem c1 hz)) (mul_mem c3 hv)
  exact ⟨MvPowerSeries.mul_inv_cancel _ hAne, MvPowerSeries.mul_inv_cancel _ hDne, hAi,
    Formalism.ELL.WeierstrassChordSeries.inv_mem_integralSeries hD hDne (by rw [hD0, inv_neg, inv_one]; exact neg_mem (one_mem _))⟩

/- English proof (translation)
Establish `hA : MvPowerSeries.HasSubst a` using `hasSubst_of_cc_zero_lemma ha`. Rewrite using `[MvPowerSeries.constantCoeff_subst hA, finsum_eq_single _ 0]`. Simplify using the standard rewrite rules. Introduce `d hd`. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, d i ≠ 0 := by`.

Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hd (Finsupp.ext h)`. Establish `h0 : cc (d.prod fun s e => a s ^ e) = 0`. Rewrite using `[Finsupp.prod, map_prod]`.

Apply `Finset.prod_eq_zero (i := i) (Finsupp.mem_support_iff.mpr hi)` to reduce the goal to its premises. Rewrite using `[map_pow, ha, zero_pow hi]`. Rewrite using `[h0, smul_zero]`.
-/
private theorem constantCoeff_subst_of_zero_lemma_2 {τ : Type} [Finite τ] {a : τ → MvPowerSeries σ K}
    (ha : ∀ i, cc (a i) = 0) (f : MvPowerSeries τ K) : cc (MvPowerSeries.subst a f) = cc f := by
  classical
  have hA : MvPowerSeries.HasSubst a := hasSubst_of_cc_zero_lemma ha
  rw [MvPowerSeries.constantCoeff_subst hA, finsum_eq_single _ 0]
  · simp
  · intro d hd
    obtain ⟨i, hi⟩ : ∃ i, d i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hd (Finsupp.ext h)
    have h0 : cc (d.prod fun s e => a s ^ e) = 0 := by
      rw [Finsupp.prod, map_prod]
      apply Finset.prod_eq_zero (i := i) (Finsupp.mem_support_iff.mpr hi)
      rw [map_pow, ha, zero_pow hi]
    rw [h0, smul_zero]

/- English proof (translation)
Establish `hab0 : ∀ i, cc (![a, b] i) = 0`. Introduce `i`. Use `fin_cases i`. Conclude with `ha`. Conclude with `hb`.

Establish `habT : ∀ i, ![a, b] i ∈ TT W σ`. Introduce `i`. Use `fin_cases i`. Conclude with `haT`. Conclude with `hbT`.

Establish `hab : MvPowerSeries.HasSubst ![a, b]` using `hasSubst_of_cc_zero_lemma hab0`. Use `set φ : MvPowerSeries (Fin 2) K →ₐ[K] MvPowerSeries σ K := MvPowerSeries.substAlgHom hab with hφdef`. Establish `hφ : ∀ f, φ f = MvPowerSeries.subst ![a, b] f` using `fun f => by`. Rewrite using `[hφdef, MvPowerSeries.coe_substAlgHom]`. Establish `hX0 : φ (MvPowerSeries.X 0) = a` using `by simp [hφ, MvPowerSeries.subst_X hab]`.

Establish `hX1 : φ (MvPowerSeries.X 1) = b` using `by simp [hφ, MvPowerSeries.subst_X hab]`. Establish `hC : ∀ c : K, φ (MvPowerSeries.C c) = MvPowerSeries.C c` using `fun c => by`. Simplify `φ.commutes c` using `[MvPowerSeries.algebraMap_apply]`. Establish `hW : ∀ i : Fin 2, φ (Formalism.ELL.WeierstrassChordSeries.Wi w i) = w.subst (![a, b] i)` using `fun i => by`. Rewrite using `[hφ, Formalism.ELL.WeierstrassChordSeries.Wi, Formalism.ELL.WeierstrassSubstitution.mvsubst_psubst w _ (MvPowerSeries.constantCoeff_X i) _ hab, MvPowerSeries.subst_X hab]`.

Establish `hmem : ∀ f, f ∈ Formalism.ELL.WeierstrassChordSeries.T W → φ f ∈ TT W σ` using `fun f hf => by`. Rewrite using `[hφ]`. Conclude with `subst_mem hf habT hab0`. Take `⟨hAi, hDi, hAT, hDT⟩` from `chordCoeffCubic_inversionDenom_inv hw`. Use `⟨φ (Formalism.ELL.WeierstrassChordSeries.lam w), φ (Formalism.ELL.WeierstrassChordSeries.nu w), φ (Formalism.ELL.WeierstrassChordSeries.z3 W w), φ (Formalism.ELL.WeierstrassChordSeries.C3 W w)⁻¹, φ (Formalism.ELL.WeierstrassChordSeries.dd W w)⁻¹, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ? …` and prove the remaining obligations.

Establish `h` using `congrArg φ (Formalism.ELL.WeierstrassChordSeries.lam_mul w)`. Rewrite `h` using `[map_mul, map_sub, map_sub, hX0, hX1, hW, hW]`. Simplify using `using h`. Simplify using `[Formalism.ELL.WeierstrassChordSeries.nu, hW, hX0]`. Establish `h` using `congrArg φ hAi`.

Rewrite `h` using `[map_mul, map_one]`. Simplify `h` using `only [chordCoeffCubicAt, Formalism.ELL.WeierstrassChordSeries.C3, Formalism.ELL.WeierstrassChordSeries.c3, Formalism.ELL.WeierstrassChordSeries.ca, map_add, map_mul, map_pow, map_one, hC]`. Simplify using `only [Formalism.ELL.WeierstrassChordSeries.z3, chordCoeffQuadraticAt, Formalism.ELL.WeierstrassChordSeries.C2, Formalism.ELL.WeierstrassChordSeries.c2, Formalism.ELL.WeierstrassChordSeries.ca, map_sub, map_neg, map_add, map_mul, map_pow, map_ofNat, hC, hX0, hX1]`. Establish `h` using `congrArg φ hDi`. Rewrite `h` using `[map_mul, map_one]`.

Simplify `h` using `only [DDs, Formalism.ELL.WeierstrassChordSeries.dd, Formalism.ELL.WeierstrassChordSeries.w3, Formalism.ELL.WeierstrassChordSeries.ca, map_add, map_mul, map_neg, map_one, hC]`. Rewrite using `[← hφ, Formalism.ELL.WeierstrassChordSeries.F2, map_mul]`. Rewrite using `[hφ, constantCoeff_subst_of_zero_lemma_2 hab0, Formalism.ELL.WeierstrassChordSeries.lam_cc hw]`. Conclude with `hmem _ (Formalism.ELL.WeierstrassChordSeries.slope_mem_integralSeries hw)`. Conclude with `hmem _ hAT`.

Conclude with `hmem _ hDT`.
-/
lemma pair [Finite σ] (hw : WFixed W w) (a b : MvPowerSeries σ K) (ha : cc a = 0) (hb : cc b = 0)
    (haT : a ∈ TT W σ) (hbT : b ∈ TT W σ) :
    ∃ l n z A B : MvPowerSeries σ K,
      (b - a) * l = w.subst b - w.subst a ∧ n = w.subst a - l * a ∧
      chordCoeffCubicAt W l * A = 1 ∧ z = -a - b - chordCoeffQuadraticAt W l n * A ∧
      DDs W l n z * B = 1 ∧ MvPowerSeries.subst ![a, b] (F2 W w) = z * B ∧
      cc l = 0 ∧ l ∈ TT W σ ∧ A ∈ TT W σ ∧ B ∈ TT W σ := by
  have hab0 : ∀ i, cc (![a, b] i) = 0 := by
    intro i
    fin_cases i
    · exact ha
    · exact hb
  have habT : ∀ i, ![a, b] i ∈ TT W σ := by
    intro i
    fin_cases i
    · exact haT
    · exact hbT
  have hab : MvPowerSeries.HasSubst ![a, b] := hasSubst_of_cc_zero_lemma hab0
  set φ : MvPowerSeries (Fin 2) K →ₐ[K] MvPowerSeries σ K := MvPowerSeries.substAlgHom hab with hφdef
  have hφ : ∀ f, φ f = MvPowerSeries.subst ![a, b] f := fun f => by
    rw [hφdef, MvPowerSeries.coe_substAlgHom]
  have hX0 : φ (MvPowerSeries.X 0) = a := by simp [hφ, MvPowerSeries.subst_X hab]
  have hX1 : φ (MvPowerSeries.X 1) = b := by simp [hφ, MvPowerSeries.subst_X hab]
  have hC : ∀ c : K, φ (MvPowerSeries.C c) = MvPowerSeries.C c := fun c => by
    simpa [MvPowerSeries.algebraMap_apply] using φ.commutes c
  have hW : ∀ i : Fin 2, φ (Formalism.ELL.WeierstrassChordSeries.Wi w i) = w.subst (![a, b] i) := fun i => by
    rw [hφ, Formalism.ELL.WeierstrassChordSeries.Wi, Formalism.ELL.WeierstrassSubstitution.mvsubst_psubst w _ (MvPowerSeries.constantCoeff_X i) _ hab, MvPowerSeries.subst_X hab]
  have hmem : ∀ f, f ∈ Formalism.ELL.WeierstrassChordSeries.T W → φ f ∈ TT W σ := fun f hf => by
    rw [hφ]
    exact subst_mem hf habT hab0
  obtain ⟨hAi, hDi, hAT, hDT⟩ := chordCoeffCubic_inversionDenom_inv hw
  refine ⟨φ (Formalism.ELL.WeierstrassChordSeries.lam w), φ (Formalism.ELL.WeierstrassChordSeries.nu w), φ (Formalism.ELL.WeierstrassChordSeries.z3 W w), φ (Formalism.ELL.WeierstrassChordSeries.C3 W w)⁻¹,
    φ (Formalism.ELL.WeierstrassChordSeries.dd W w)⁻¹, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := congrArg φ (Formalism.ELL.WeierstrassChordSeries.lam_mul w)
    rw [map_mul, map_sub, map_sub, hX0, hX1, hW, hW] at h
    simpa using h
  · simp [Formalism.ELL.WeierstrassChordSeries.nu, hW, hX0]
  · have h := congrArg φ hAi
    rw [map_mul, map_one] at h
    simpa only [chordCoeffCubicAt, Formalism.ELL.WeierstrassChordSeries.C3, Formalism.ELL.WeierstrassChordSeries.c3, Formalism.ELL.WeierstrassChordSeries.ca, map_add, map_mul, map_pow,
      map_one, hC] using h
  · simp only [Formalism.ELL.WeierstrassChordSeries.z3, chordCoeffQuadraticAt, Formalism.ELL.WeierstrassChordSeries.C2, Formalism.ELL.WeierstrassChordSeries.c2, Formalism.ELL.WeierstrassChordSeries.ca, map_sub,
      map_neg, map_add, map_mul, map_pow, map_ofNat, hC, hX0, hX1]
  · have h := congrArg φ hDi
    rw [map_mul, map_one] at h
    simpa only [DDs, Formalism.ELL.WeierstrassChordSeries.dd, Formalism.ELL.WeierstrassChordSeries.w3, Formalism.ELL.WeierstrassChordSeries.ca, map_add, map_mul, map_neg, map_one,
      hC] using h
  · rw [← hφ, Formalism.ELL.WeierstrassChordSeries.F2, map_mul]
  · rw [hφ, constantCoeff_subst_of_zero_lemma_2 hab0, Formalism.ELL.WeierstrassChordSeries.lam_cc hw]
  · exact hmem _ (Formalism.ELL.WeierstrassChordSeries.slope_mem_integralSeries hw)
  · exact hmem _ hAT
  · exact hmem _ hDT

/- English proof (translation)
Establish `hX01 : (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K) ≠ MvPowerSeries.X 1`. Introduce `h`. Establish `h'` using `congrArg (MvPowerSeries.coeff (Finsupp.single (0 : Fin 3) 1)) h`. Rewrite `h'` using `[MvPowerSeries.coeff_X, MvPowerSeries.coeff_X, if_pos rfl, if_neg]`. Conclude with `one_ne_zero h'`.

Introduce `h2`. Conclude with `absurd ((Finsupp.single_left_inj one_ne_zero).mp h2) (by decide)`. Establish `hb0 : ∀ i, cc ((![MvPowerSeries.X 0, MvPowerSeries.X 1, 0] : Fin 3 → MvPowerSeries (Fin 2) K) i) = 0`. Introduce `i`. Apply the tactic sequence `fin_cases i <;> simp`.

Establish `ha0 : ∀ i, cc ((![MvPowerSeries.X 0, MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 3) K) i) = 0`. Introduce `i`. Apply the tactic sequence `fin_cases i <;> simp`. Establish `hb : MvPowerSeries.HasSubst (![MvPowerSeries.X 0, MvPowerSeries.X 1, 0] : Fin 3 → MvPowerSeries (Fin 2) K)` using `hasSubst_of_cc_zero_lemma hb0`. Establish `ha : MvPowerSeries.HasSubst (![MvPowerSeries.X 0, MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 3) K)` using `hasSubst_of_cc_zero_lemma ha0`.

Establish `hid : (fun i : Fin 2 => MvPowerSeries.subst (![MvPowerSeries.X 0, MvPowerSeries.X 1, 0] : Fin 3 → MvPowerSeries (Fin 2) K) ((![MvPowerSeries.X 0, MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 3) K) i)) = MvPowerSeries.X`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `fin_cases i <;> simp [MvPowerSeries.subst_X hb]`. Establish `key : MvPowerSeries.subst (![MvPowerSeries.X 0, MvPowerSeries.X 1, 0] : Fin 3 → MvPowerSeries (Fin 2) K) (MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 1] (Formalism.ELL.WeierstrassChordSeries.F2 W w)) = Formalism.ELL.WeierstrassChordSeries. …`. Rewrite using `[MvPowerSeries.subst_comp_subst_apply ha hb]`.

Rewrite using `[hid]`. Conclude with `congrFun MvPowerSeries.subst_self (Formalism.ELL.WeierstrassChordSeries.F2 W w)`. Establish `hF : Formalism.ELL.WeierstrassChordSeries.F2 W w ≠ 0` using `Formalism.ELL.WeierstrassChordSeries.ne_zero_of_L (i := 0) (by rw [Formalism.ELL.WeierstrassChordSeries.linearCoeff_formalSum hw]; exact one_ne_zero)`. Establish `hX2 : MvPowerSeries.subst (![MvPowerSeries.X 0, MvPowerSeries.X 1, 0] : Fin 3 → MvPowerSeries (Fin 2) K) (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K) = 0`. Simplify using `[MvPowerSeries.subst_X hb]`.

Use `⟨fun h => hF ?_, fun h => hF ?_, hX01⟩` and prove the remaining obligations. Rewrite using `[← key, h, ← MvPowerSeries.coe_substAlgHom hb, map_zero]`. Rewrite using `[← key, h, hX2]`.
-/
lemma lit_facts (hw : WFixed W w) :
    MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 1]
      (F2 W w) ≠ 0 ∧
    MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 1]
      (F2 W w) ≠ MvPowerSeries.X 2 ∧
    (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K) ≠ MvPowerSeries.X 1 := by
  classical
  have hX01 : (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K) ≠ MvPowerSeries.X 1 := by
    intro h
    have h' := congrArg (MvPowerSeries.coeff (Finsupp.single (0 : Fin 3) 1)) h
    rw [MvPowerSeries.coeff_X, MvPowerSeries.coeff_X, if_pos rfl, if_neg] at h'
    · exact one_ne_zero h'
    · intro h2
      exact absurd ((Finsupp.single_left_inj one_ne_zero).mp h2) (by decide)
  have hb0 : ∀ i, cc ((![MvPowerSeries.X 0, MvPowerSeries.X 1, 0] : Fin 3 → MvPowerSeries (Fin 2) K) i) = 0 := by
    intro i
    fin_cases i <;> simp
  have ha0 : ∀ i, cc ((![MvPowerSeries.X 0, MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 3) K) i) = 0 := by
    intro i
    fin_cases i <;> simp
  have hb : MvPowerSeries.HasSubst (![MvPowerSeries.X 0, MvPowerSeries.X 1, 0] : Fin 3 → MvPowerSeries (Fin 2) K) :=
    hasSubst_of_cc_zero_lemma hb0
  have ha : MvPowerSeries.HasSubst (![MvPowerSeries.X 0, MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 3) K) :=
    hasSubst_of_cc_zero_lemma ha0
  have hid : (fun i : Fin 2 => MvPowerSeries.subst
      (![MvPowerSeries.X 0, MvPowerSeries.X 1, 0] : Fin 3 → MvPowerSeries (Fin 2) K)
      ((![MvPowerSeries.X 0, MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 3) K) i)) = MvPowerSeries.X := by
    funext i
    fin_cases i <;> simp [MvPowerSeries.subst_X hb]
  have key : MvPowerSeries.subst (![MvPowerSeries.X 0, MvPowerSeries.X 1, 0] : Fin 3 → MvPowerSeries (Fin 2) K)
      (MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 1] (Formalism.ELL.WeierstrassChordSeries.F2 W w))
      = Formalism.ELL.WeierstrassChordSeries.F2 W w := by
    rw [MvPowerSeries.subst_comp_subst_apply ha hb]
    rw [hid]
    exact congrFun MvPowerSeries.subst_self (Formalism.ELL.WeierstrassChordSeries.F2 W w)
  have hF : Formalism.ELL.WeierstrassChordSeries.F2 W w ≠ 0 :=
    Formalism.ELL.WeierstrassChordSeries.ne_zero_of_L (i := 0) (by rw [Formalism.ELL.WeierstrassChordSeries.linearCoeff_formalSum hw]; exact one_ne_zero)
  have hX2 : MvPowerSeries.subst (![MvPowerSeries.X 0, MvPowerSeries.X 1, 0] : Fin 3 → MvPowerSeries (Fin 2) K)
      (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K) = 0 := by
    simp [MvPowerSeries.subst_X hb]
  refine ⟨fun h => hF ?_, fun h => hF ?_, hX01⟩
  · rw [← key, h, ← MvPowerSeries.coe_substAlgHom hb, map_zero]
  · rw [← key, h, hX2]

end Mser

end CubeThreeAlt
end Formalism.ELL

namespace Formalism.ELL

open CubeThreeAlt WeierstrassChordSeries

set_option maxHeartbeats 4000000 in
/- English proof (translation)
Introduce `K _ W w F hw hF0 hch`. Establish `hU` using `wSeriesSubstUnique_holds.{u}`. Establish `hwu` using `w_eq hw`. Establish `hu1` using `wU_cc hw`. Establish `hFF : F = F2 W w` using `WeierstrassCoordinateSubstitution.eq_of_xy hwu hu1 F (F2 W w) hF0 (constantCoeff_formalSum hw) (hch.1.trans (chord hU hw).1.symm) (hch.2.trans (chord hU hw).2.symm)`.

Substitute `hFF` using the available equality. Simplify using `only`. Establish `: IsDomain (MvPowerSeries (Fin 3) K)` using `NoZeroDivisors.to_isDomain _`. Establish `hUc : ∀ i : Fin 3, MvPowerSeries.constantCoeff ((wU w).subst (MvPowerSeries.X i : MvPowerSeries (Fin 3) K)) = 1`. Introduce `i`.

Rewrite using `[← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_subst_single]`. Simplify using `[hu1]`. Establish `hUV : ∀ i : Fin 3, (wU w).subst (MvPowerSeries.X i : MvPowerSeries (Fin 3) K) * ((wU w).subst (MvPowerSeries.X i : MvPowerSeries (Fin 3) K))⁻¹ = 1` using `fun i => MvPowerSeries.mul_inv_cancel _ (by rw [hUc]; exact one_ne_zero)`. Establish `hVc : ∀ i : Fin 3, MvPowerSeries.constantCoeff (((wU w).subst (MvPowerSeries.X i : MvPowerSeries (Fin 3) K))⁻¹) = 1`. Introduce `i`.

Rewrite using `[MvPowerSeries.constantCoeff_inv, hUc, inv_one]`. Establish `h3 : ∀ i : Fin 3, (MvPowerSeries.X i : MvPowerSeries (Fin 3) K) ^ 3 = ((wU w).subst (MvPowerSeries.X i : MvPowerSeries (Fin 3) K))⁻¹ * w.subst (MvPowerSeries.X i : MvPowerSeries (Fin 3) K)`. Introduce `i`. Rewrite using `[WeierstrassCoordinateSubstitution.subst_w hwu _ (by simp)]`. Take the linear combination `(-(MvPowerSeries.X i : MvPowerSeries (Fin 3) K) ^ 3) * hUV i`.

Establish `hdet` using `det_rows (fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 3) K)) (fun i => ((wU w).subst (MvPowerSeries.X i : MvPowerSeries (Fin 3) K))⁻¹) (fun i => w.subst (MvPowerSeries.X i : MvPowerSeries (Fin 3) K)) h3`. Rewrite using `[hdet]`. Establish `hV0c` using `hVc 0`. Establish `hV1c` using `hVc 1`. Establish `hV2c` using `hVc 2`.

Establish `hU0m : (wU w).subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K) ∈ TT W (Fin 3)` using `psubst_mem (wU_coeff_mem hw) (X_mem_TT 0) (by simp)`. Establish `hU1m : (wU w).subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K) ∈ TT W (Fin 3)` using `psubst_mem (wU_coeff_mem hw) (X_mem_TT 1) (by simp)`. Establish `hU2m : (wU w).subst (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K) ∈ TT W (Fin 3)` using `psubst_mem (wU_coeff_mem hw) (X_mem_TT 2) (by simp)`. Establish `hVm : ∀ i : Fin 3, (wU w).subst (MvPowerSeries.X i : MvPowerSeries (Fin 3) K) ∈ TT W (Fin 3) → ((wU w).subst (MvPowerSeries.X i : MvPowerSeries (Fin 3) K))⁻¹ ∈ TT W (Fin 3)` using `fun i h => inv_mem_TT h (by rw [hUc]; exact one_ne_zero) (by rw [hUc, inv_one]; exact Subalgebra.one_mem _)`. Establish `hV0m` using `hVm 0 hU0m`.

Establish `hV1m` using `hVm 1 hU1m`. Establish `hV2m` using `hVm 2 hU2m`. Take `⟨hsne, hsX2, hX01⟩` from `lit_facts hw`. Use `set X0 : MvPowerSeries (Fin 3) K := MvPowerSeries.X 0 with hX0`. Use `set X1 : MvPowerSeries (Fin 3) K := MvPowerSeries.X 1 with hX1`.

Use `set X2 : MvPowerSeries (Fin 3) K := MvPowerSeries.X 2 with hX2`. Use `set V0 := ((wU w).subst X0)⁻¹ with hV0`. Use `set V1 := ((wU w).subst X1)⁻¹ with hV1`. Use `set V2 := ((wU w).subst X2)⁻¹ with hV2`. Use `set w0 := w.subst X0 with hw0d`.

Use `set w1 := w.subst X1 with hw1d`. Use `set w2 := w.subst X2 with hw2d`. Establish `k0 : MvPowerSeries.constantCoeff X0 = 0` using `by simp [hX0]`. Establish `k1 : MvPowerSeries.constantCoeff X1 = 0` using `by simp [hX1]`. Establish `k2 : MvPowerSeries.constantCoeff X2 = 0` using `by simp [hX2]`.

Establish `m0 : X0 ∈ TT W (Fin 3)` using `X_mem_TT 0`. Establish `m1 : X1 ∈ TT W (Fin 3)` using `X_mem_TT 1`. Establish `m2 : X2 ∈ TT W (Fin 3)` using `X_mem_TT 2`. Establish `hX2ne : X2 ≠ 0` using `WeierstrassCoordinateSubstitution.X_ne_zero' 2`. Take `⟨mA1, mA2, mA3, mA4, mA6⟩` from `Ca_mem (W := W) (σ := Fin 3)`.

Establish `hUs` using `fun (s : MvPowerSeries (Fin 3) K) (hs : MvPowerSeries.constantCoeff s = 0) => hU K W w hw (Fin 3) s hs`. Establish `hGw : ∀ s, MvPowerSeries.constantCoeff s = 0 → GG W s (w.subst s) = 0` using `fun s hs => (weq_iff' W _ _).mp (hUs s hs).1`. Establish `huniq : ∀ s v, MvPowerSeries.constantCoeff s = 0 → MvPowerSeries.constantCoeff v = 0 → GG W s v = 0 → w.subst s = v` using `fun s v hs hv hG => ((hUs s hs).2 v hv ((weq_iff' W _ _).mpr hG)).symm`. Establish `hwcc : ∀ s : MvPowerSeries (Fin 3) K, MvPowerSeries.constantCoeff s = 0 → MvPowerSeries.constantCoeff (w.subst s) = 0` using `fun s hs => PowerSeries.constantCoeff_subst_eq_zero hs w hw.1`. Establish `hwm : ∀ s, s ∈ TT W (Fin 3) → MvPowerSeries.constantCoeff s = 0 → w.subst s ∈ TT W (Fin 3)` using `fun s h h0 => psubst_mem (w_coeff_mem hw) h h0`.

Establish `hw0c : MvPowerSeries.constantCoeff w0 = 0` using `hwcc X0 k0`. Establish `hw1c : MvPowerSeries.constantCoeff w1 = 0` using `hwcc X1 k1`. Establish `hw2c : MvPowerSeries.constantCoeff w2 = 0` using `hwcc X2 k2`. Establish `hG0 : GG W X0 w0 = 0` using `hGw X0 k0`. Establish `hG1 : GG W X1 w1 = 0` using `hGw X1 k1`.

Establish `hG2 : GG W X2 w2 = 0` using `hGw X2 k2`. Take `⟨l1, n1, u, A1, B1, hl1, hn1, hA1, hz1, hB1, hs1, hl1c, hl1m, hA1m, hB1m⟩` from `pair hw X0 X1 k0 k1 m0 m1`. Use `set s := MvPowerSeries.subst ![X0, X1] (F2 W w) with hsdef`. Establish `hn1c : MvPowerSeries.constantCoeff n1 = 0` using `by rw [hn1]; simp [hwcc X0 k0, hl1c, k0]`. Establish `hn1m : n1 ∈ TT W (Fin 3)`.

Rewrite using `[hn1]`. Conclude with `(TT W _).sub_mem (hwm X0 m0 k0) ((TT W _).mul_mem hl1m m0)`. Establish `huc : MvPowerSeries.constantCoeff u = 0`. Rewrite using `[hz1]`. Simplify using `[chordCoeffQuadraticAt, WeierstrassChordSeries.c2, hl1c, hn1c, k0, k1]`.

Establish `hum : u ∈ TT W (Fin 3)`. Rewrite using `[hz1]`. Conclude with `(TT W _).sub_mem ((TT W _).sub_mem ((TT W _).neg_mem m0) m1) ((TT W _).mul_mem (lineCoeffQuadratic_mem _ mA1 mA2 mA3 mA4 mA6 hl1m hn1m) hA1m)`. Establish `hsc : MvPowerSeries.constantCoeff s = 0` using `by rw [hs1]; simp [huc]`. Establish `hsm : s ∈ TT W (Fin 3)` using `by rw [hs1]; exact (TT W _).mul_mem hum hB1m`.

Establish `hw0 : w0 = l1 * X0 + n1` using `by rw [hn1]; ring`. Establish `hw1 : w1 = l1 * X1 + n1` using `by rw [hn1]; linear_combination -hl1`. Establish `he1 : chordCoeffCubicAt W l1 * (X0 + X1 + u) + chordCoeffQuadraticAt W l1 n1 = 0`. Rewrite using `[hz1]`. Take the linear combination `(-(chordCoeffQuadraticAt W l1 n1)) * hA1`.

Establish `line1` using `line_fact hX01 (by rw [← hw0]; exact hG0) (by rw [← hw1]; exact hG1) he1`. Establish `hGu : GG W u (l1 * u + n1) = 0`. Establish `h` using `line1 u`. Rewrite `h` using `[sub_self, mul_zero]`. Conclude with `h`.

Establish `huw : w.subst u = l1 * u + n1` using `huniq u _ huc (by simp [hl1c, huc, hn1c]) hGu`. Use `set dd1 := DDs W l1 n1 u with hdd1`. Establish `hdd1c : MvPowerSeries.constantCoeff dd1 = -1` using `by simp [hdd1, DDs, huc, hl1c, hn1c]`. Establish `hdd10 : dd1 ≠ 0` using `fun h => by simp [h] at hdd1c`. Establish `hsd : s * dd1 = u` using `by rw [hs1]; linear_combination u * hB1`.

Establish `hune : u ≠ 0` using `by rw [← hsd]; exact mul_ne_zero hsne hdd10`. Establish `hGs' : GG W s ((l1 * u + n1) * B1) = 0` using `G_inv hsd (by linear_combination (l1 * u + n1) * hB1) rfl hdd10 hGu`. Establish `hws : w.subst s = (l1 * u + n1) * B1` using `huniq s _ hsc (by simp [hl1c, huc, hn1c]) hGs'`. Use `set lam0 := u ^ 2 * (wU w).subst u with hlam0`. Establish `hlam0c : MvPowerSeries.constantCoeff lam0 = 0` using `by simp [hlam0, huc]`.

Establish `hlam0m : lam0 ∈ TT W (Fin 3)` using `(TT W _).mul_mem ((TT W _).pow_mem hum 2) (psubst_mem (wU_coeff_mem hw) hum huc)`. Establish `hl0 : l1 * u + n1 = lam0 * u`. Rewrite using `[← huw, WeierstrassCoordinateSubstitution.subst_w hwu u huc, hlam0]`. Expand and normalize the polynomial expressions, which then agree. Establish `hws' : w.subst s = lam0 * s`.

Rewrite using `[hws, hl0, hs1]`. Expand and normalize the polynomial expressions, which then agree. Establish `hq` using `q_fact (a2 := MvPowerSeries.C W.a₂) (a4 := MvPowerSeries.C W.a₄) (a6 := MvPowerSeries.C W.a₆) (c := X2) hune hdd10 hsd (by rw [hdd1, DDs, hl0]) (by rw [← hl0]; exact hGu)`. Take `⟨l2, n2, r, A2, B2, hl2, hn2, hA2, hz2, hB2, hs2, hl2c, hl2m, hA2m, hB2m⟩` from `pair hw s X2 hsc k2 hsm m2`. Use `set F3 := MvPowerSeries.subst ![s, X2] (F2 W w) with hF3`.

Establish `hwsc : MvPowerSeries.constantCoeff (w.subst s) = 0` using `hwcc s hsc`. Establish `hn2c : MvPowerSeries.constantCoeff n2 = 0` using `by rw [hn2]; simp [hwsc, hl2c, hsc]`. Establish `hn2m : n2 ∈ TT W (Fin 3)`. Rewrite using `[hn2]`. Conclude with `(TT W _).sub_mem (hwm s hsm hsc) ((TT W _).mul_mem hl2m hsm)`.

Establish `hrc : MvPowerSeries.constantCoeff r = 0`. Rewrite using `[hz2]`. Simplify using `[chordCoeffQuadraticAt, WeierstrassChordSeries.c2, hl2c, hn2c, hsc, k2]`. Establish `hrm : r ∈ TT W (Fin 3)`. Rewrite using `[hz2]`.

Conclude with `(TT W _).sub_mem ((TT W _).sub_mem ((TT W _).neg_mem hsm) m2) ((TT W _).mul_mem (lineCoeffQuadratic_mem _ mA1 mA2 mA3 mA4 mA6 hl2m hn2m) hA2m)`. Establish `hws2 : w.subst s = l2 * s + n2` using `by rw [hn2]; ring`. Establish `hw2 : w2 = l2 * X2 + n2` using `by rw [hn2]; linear_combination -hl2`. Establish `he2 : chordCoeffCubicAt W l2 * (s + X2 + r) + chordCoeffQuadraticAt W l2 n2 = 0`. Rewrite using `[hz2]`.

Take the linear combination `(-(chordCoeffQuadraticAt W l2 n2)) * hA2`. Establish `line2` using `line_fact hsX2 (by rw [← hws2]; exact hGw s hsc) (by rw [← hw2]; exact hG2) he2`. Use `set N := 1 - MvPowerSeries.C W.a₃ * n2 - MvPowerSeries.C W.a₆ * n2 ^ 2 with hN`. Establish `hv : n2 * N = chordCoeffCubicAt W l2 * s * X2 * r`. Establish `h` using `line2 0`.

Simplify using `only [G] at h`. Rewrite using `[hN]`. Unfold `chordCoeffCubicAt`. Take the linear combination `-h`. Use `set H1 := HHs W X2 (l1 * X2 + n1) w2 with hH1`.

Use `set H0 := HHs W X2 (lam0 * X2) w2 with hH0`. Establish `hE1 : (l1 * X2 + n1 - w2) * H1 = chordCoeffCubicAt W l1 * (X2 - X0) * (X2 - X1) * (X2 - u)`. Establish `h` using `G_sub (MvPowerSeries.C W.a₁) (MvPowerSeries.C W.a₂) (MvPowerSeries.C W.a₃) (MvPowerSeries.C W.a₄) (MvPowerSeries.C W.a₆) X2 (l1 * X2 + n1) w2`. Establish `hG2' : G (MvPowerSeries.C W.a₁) (MvPowerSeries.C W.a₂) (MvPowerSeries.C W.a₃) (MvPowerSeries.C W.a₄) (MvPowerSeries.C W.a₆) X2 w2 = 0` using `hG2`. Rewrite `h` using `[hG2', line1 X2, sub_zero]`.

Rewrite using `[hH1]`. Unfold `HHs chordCoeffCubicAt`. Conclude with `h.symm`. Establish `hE0 : (lam0 * X2 - w2) * H0 = X2 * chordCoeffCubicAt W lam0 * (X2 - u) * (X2 - s)`. Establish `h` using `G_sub (MvPowerSeries.C W.a₁) (MvPowerSeries.C W.a₂) (MvPowerSeries.C W.a₃) (MvPowerSeries.C W.a₄) (MvPowerSeries.C W.a₆) X2 (lam0 * X2) w2`.

Establish `hG2' : G (MvPowerSeries.C W.a₁) (MvPowerSeries.C W.a₂) (MvPowerSeries.C W.a₃) (MvPowerSeries.C W.a₄) (MvPowerSeries.C W.a₆) X2 w2 = 0` using `hG2`. Rewrite `h` using `[hG2', hq, sub_zero]`. Rewrite using `[hH0]`. Unfold `HHs chordCoeffCubicAt`. Conclude with `h.symm`.

Establish `hnu : (X2 - s) * n2 = s * (lam0 * X2 - w2)`. Take the linear combination `(X2 - s) * hn2 - s * hl2 + X2 * hws'`. Establish `hK : (X2 - s) * s * X2 * (chordCoeffCubicAt W l2 * r * H0 - chordCoeffCubicAt W lam0 * (X2 - u) * N) = 0`. Take the linear combination `(-(X2 - s) * H0) * hv + (N * H0) * hnu + (N * s) * hE0`. Establish `hK' : chordCoeffCubicAt W l2 * r * H0 = chordCoeffCubicAt W lam0 * (X2 - u) * N`.

Establish `hne : (X2 - s) * s * X2 ≠ 0` using `mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr (Ne.symm hsX2)) hsne) hX2ne`. Conclude with `sub_eq_zero.mp ((mul_eq_zero.mp hK).resolve_left hne)`. Use `set dd2 := DDs W l2 n2 r with hdd2`. Establish `hr : r = F3 * dd2` using `by rw [hs2]; linear_combination -r * hB2`. Establish `hH1c : MvPowerSeries.constantCoeff H1 = -1`.

Simplify using `[hH1, HHs, Hv, k2, hl1c, hn1c, hw2c]`. Establish `hH0c : MvPowerSeries.constantCoeff H0 = -1`. Simplify using `[hH0, HHs, Hv, k2, hlam0c, hw2c]`. Establish `hNc : MvPowerSeries.constantCoeff N = 1` using `by simp [hN, hn2c]`. Establish `hC30c : MvPowerSeries.constantCoeff (chordCoeffCubicAt W lam0) = 1` using `by simp [chordCoeffCubicAt, c3, hlam0c]`.

Establish `hPc : MvPowerSeries.constantCoeff (H1 * chordCoeffCubicAt W lam0 * N) = -1`. Simplify using `[hH1c, hC30c, hNc]`. Use `set Y := (H1 * chordCoeffCubicAt W lam0 * N)⁻¹ with hYd`. Establish `hY : H1 * chordCoeffCubicAt W lam0 * N * Y = 1` using `MvPowerSeries.mul_inv_cancel _ (by rw [hPc]; exact neg_ne_zero.mpr one_ne_zero)`. Establish `hPm : H1 * chordCoeffCubicAt W lam0 * N ∈ TT W (Fin 3)`.

Use `(TT W _).mul_mem ((TT W _).mul_mem ?_ (lineCoeffCubic_mem _ mA2 mA4 mA6 hlam0m)) ?_` and prove the remaining obligations. Conclude with `Hv_mem _ mA1 mA2 mA3 mA4 mA6 m2 ((TT W _).add_mem ((TT W _).mul_mem hl1m m2) hn1m) (hwm X2 m2 k2)`. Conclude with `(TT W _).sub_mem ((TT W _).sub_mem (TT W _).one_mem ((TT W _).mul_mem mA3 hn2m)) ((TT W _).mul_mem mA6 ((TT W _).pow_mem hn2m 2))`. Establish `hYm : Y ∈ TT W (Fin 3)` using `inv_mem_TT hPm (by rw [hPc]; exact neg_ne_zero.mpr one_ne_zero) (by rw [hPc, inv_neg, inv_one]; exact Subalgebra.neg_mem _ (Subalgebra.one_mem _))`. Establish `hC31c : MvPowerSeries.constantCoeff (chordCoeffCubicAt W l1) = 1` using `by simp [chordCoeffCubicAt, c3, hl1c]`.

Establish `hC32c : MvPowerSeries.constantCoeff (chordCoeffCubicAt W l2) = 1` using `by simp [chordCoeffCubicAt, c3, hl2c]`. Establish `hdd2c : MvPowerSeries.constantCoeff dd2 = -1` using `by simp [hdd2, DDs, hrc, hl2c, hn2c]`. Use `⟨V0 * V1 * V2 * chordCoeffCubicAt W l1 * chordCoeffCubicAt W l2 * dd2 * H0 * Y, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `hm : V0 * V1 * V2 * chordCoeffCubicAt W l1 * chordCoeffCubicAt W l2 * dd2 * H0 * Y ∈ TT W (Fin 3)`. Use `(TT W _).mul_mem ((TT W _).mul_mem ((TT W _).mul_mem ((TT W _).mul_mem ((TT W _).mul_mem ((TT W _).mul_mem ((TT W _).mul_mem hV0m hV1m) hV2m) (lineCoeffCubic_mem _ mA2 mA4 mA6 hl1m)) (lineCoeffCubic_mem _ mA2 mA4 mA6 hl2m)) ?_) ?_) hYm` and prove the remaining obligations.

Simplify using `only [hdd2, DDs]`. Conclude with `(TT W _).add_mem ((TT W _).add_mem ((TT W _).neg_mem (TT W _).one_mem) ((TT W _).mul_mem mA1 hrm)) ((TT W _).mul_mem mA3 ((TT W _).add_mem ((TT W _).mul_mem hl2m hrm) hn2m))`. Conclude with `Hv_mem _ mA1 mA2 mA3 mA4 mA6 m2 ((TT W _).mul_mem hlam0m m2) (hwm X2 m2 k2)`. Conclude with `mem_TT.mp hm`. Rewrite using `[hYd]`.

Simplify using `only [map_mul, hV0c, hV1c, hV2c, hC31c, hC32c, hdd2c, hH0c, MvPowerSeries.constantCoeff_inv, hPc]`. Evaluate the numerical expressions. Establish `step1 : -(V0 * V1 * V2) * ((w1 - w0) * (X2 - X0) - (w2 - w0) * (X1 - X0)) = -(V0 * V1 * V2) * (X1 - X0) * (l1 * X2 + n1 - w2)`. Rewrite using `[hw0, hw1]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[step1]`. Take the linear combination `(V0 * V1 * V2 * (X1 - X0) * (l1 * X2 + n1 - w2)) * hY + (-Y * (V0 * V1 * V2) * (X1 - X0) * chordCoeffCubicAt W lam0 * N) * hE1 + (Y * (V0 * V1 * V2) * (X1 - X0) * chordCoeffCubicAt W l1 * (X2 - X0) * (X2 - X1)) * hK' + (-Y * (V0 * V1 * V2) * (X1 - X0) * chordCoeffCubicAt W l1 * ( …`.
-/
theorem chordDeterminantFactor_holds : CubeThree.{u} := by
  intro K _ W w F hw hF0 hch
  have hU := wSeriesSubstUnique_holds.{u}
  have hwu := w_eq hw
  have hu1 := wU_cc hw
  have hFF : F = F2 W w := WeierstrassCoordinateSubstitution.eq_of_xy hwu hu1 F (F2 W w) hF0 (constantCoeff_formalSum hw)
    (hch.1.trans (chord hU hw).1.symm) (hch.2.trans (chord hU hw).2.symm)
  subst hFF
  dsimp only
  have : IsDomain (MvPowerSeries (Fin 3) K) := NoZeroDivisors.to_isDomain _
  have hUc : ∀ i : Fin 3, MvPowerSeries.constantCoeff
      ((wU w).subst (MvPowerSeries.X i : MvPowerSeries (Fin 3) K)) = 1 := by
    intro i
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_subst_single]
    simp [hu1]
  have hUV : ∀ i : Fin 3, (wU w).subst (MvPowerSeries.X i : MvPowerSeries (Fin 3) K) *
      ((wU w).subst (MvPowerSeries.X i : MvPowerSeries (Fin 3) K))⁻¹ = 1 :=
    fun i => MvPowerSeries.mul_inv_cancel _ (by rw [hUc]; exact one_ne_zero)
  have hVc : ∀ i : Fin 3, MvPowerSeries.constantCoeff
      (((wU w).subst (MvPowerSeries.X i : MvPowerSeries (Fin 3) K))⁻¹) = 1 := by
    intro i; rw [MvPowerSeries.constantCoeff_inv, hUc, inv_one]
  have h3 : ∀ i : Fin 3, (MvPowerSeries.X i : MvPowerSeries (Fin 3) K) ^ 3 =
      ((wU w).subst (MvPowerSeries.X i : MvPowerSeries (Fin 3) K))⁻¹ *
        w.subst (MvPowerSeries.X i : MvPowerSeries (Fin 3) K) := by
    intro i
    rw [WeierstrassCoordinateSubstitution.subst_w hwu _ (by simp)]
    linear_combination (-(MvPowerSeries.X i : MvPowerSeries (Fin 3) K) ^ 3) * hUV i
  have hdet := det_rows (fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 3) K))
    (fun i => ((wU w).subst (MvPowerSeries.X i : MvPowerSeries (Fin 3) K))⁻¹)
    (fun i => w.subst (MvPowerSeries.X i : MvPowerSeries (Fin 3) K)) h3
  rw [hdet]
  have hV0c := hVc 0
  have hV1c := hVc 1
  have hV2c := hVc 2
  have hU0m : (wU w).subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K) ∈ TT W (Fin 3) :=
    psubst_mem (wU_coeff_mem hw) (X_mem_TT 0) (by simp)
  have hU1m : (wU w).subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K) ∈ TT W (Fin 3) :=
    psubst_mem (wU_coeff_mem hw) (X_mem_TT 1) (by simp)
  have hU2m : (wU w).subst (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K) ∈ TT W (Fin 3) :=
    psubst_mem (wU_coeff_mem hw) (X_mem_TT 2) (by simp)
  have hVm : ∀ i : Fin 3, (wU w).subst (MvPowerSeries.X i : MvPowerSeries (Fin 3) K) ∈ TT W (Fin 3) →
      ((wU w).subst (MvPowerSeries.X i : MvPowerSeries (Fin 3) K))⁻¹ ∈ TT W (Fin 3) :=
    fun i h => inv_mem_TT h (by rw [hUc]; exact one_ne_zero)
      (by rw [hUc, inv_one]; exact Subalgebra.one_mem _)
  have hV0m := hVm 0 hU0m
  have hV1m := hVm 1 hU1m
  have hV2m := hVm 2 hU2m
  obtain ⟨hsne, hsX2, hX01⟩ := lit_facts hw
  set X0 : MvPowerSeries (Fin 3) K := MvPowerSeries.X 0 with hX0
  set X1 : MvPowerSeries (Fin 3) K := MvPowerSeries.X 1 with hX1
  set X2 : MvPowerSeries (Fin 3) K := MvPowerSeries.X 2 with hX2
  set V0 := ((wU w).subst X0)⁻¹ with hV0
  set V1 := ((wU w).subst X1)⁻¹ with hV1
  set V2 := ((wU w).subst X2)⁻¹ with hV2
  set w0 := w.subst X0 with hw0d
  set w1 := w.subst X1 with hw1d
  set w2 := w.subst X2 with hw2d
  have k0 : MvPowerSeries.constantCoeff X0 = 0 := by simp [hX0]
  have k1 : MvPowerSeries.constantCoeff X1 = 0 := by simp [hX1]
  have k2 : MvPowerSeries.constantCoeff X2 = 0 := by simp [hX2]
  have m0 : X0 ∈ TT W (Fin 3) := X_mem_TT 0
  have m1 : X1 ∈ TT W (Fin 3) := X_mem_TT 1
  have m2 : X2 ∈ TT W (Fin 3) := X_mem_TT 2
  have hX2ne : X2 ≠ 0 := WeierstrassCoordinateSubstitution.X_ne_zero' 2
  obtain ⟨mA1, mA2, mA3, mA4, mA6⟩ := Ca_mem (W := W) (σ := Fin 3)
  have hUs := fun (s : MvPowerSeries (Fin 3) K) (hs : MvPowerSeries.constantCoeff s = 0) =>
    hU K W w hw (Fin 3) s hs
  have hGw : ∀ s, MvPowerSeries.constantCoeff s = 0 → GG W s (w.subst s) = 0 :=
    fun s hs => (weq_iff' W _ _).mp (hUs s hs).1
  have huniq : ∀ s v, MvPowerSeries.constantCoeff s = 0 → MvPowerSeries.constantCoeff v = 0 →
      GG W s v = 0 → w.subst s = v :=
    fun s v hs hv hG => ((hUs s hs).2 v hv ((weq_iff' W _ _).mpr hG)).symm
  have hwcc : ∀ s : MvPowerSeries (Fin 3) K, MvPowerSeries.constantCoeff s = 0 →
      MvPowerSeries.constantCoeff (w.subst s) = 0 :=
    fun s hs => PowerSeries.constantCoeff_subst_eq_zero hs w hw.1
  have hwm : ∀ s, s ∈ TT W (Fin 3) → MvPowerSeries.constantCoeff s = 0 →
      w.subst s ∈ TT W (Fin 3) := fun s h h0 => psubst_mem (w_coeff_mem hw) h h0
  have hw0c : MvPowerSeries.constantCoeff w0 = 0 := hwcc X0 k0
  have hw1c : MvPowerSeries.constantCoeff w1 = 0 := hwcc X1 k1
  have hw2c : MvPowerSeries.constantCoeff w2 = 0 := hwcc X2 k2
  have hG0 : GG W X0 w0 = 0 := hGw X0 k0
  have hG1 : GG W X1 w1 = 0 := hGw X1 k1
  have hG2 : GG W X2 w2 = 0 := hGw X2 k2

  obtain ⟨l1, n1, u, A1, B1, hl1, hn1, hA1, hz1, hB1, hs1, hl1c, hl1m, hA1m, hB1m⟩ :=
    pair hw X0 X1 k0 k1 m0 m1
  set s := MvPowerSeries.subst ![X0, X1] (F2 W w) with hsdef
  have hn1c : MvPowerSeries.constantCoeff n1 = 0 := by rw [hn1]; simp [hwcc X0 k0, hl1c, k0]
  have hn1m : n1 ∈ TT W (Fin 3) := by
    rw [hn1]; exact (TT W _).sub_mem (hwm X0 m0 k0) ((TT W _).mul_mem hl1m m0)
  have huc : MvPowerSeries.constantCoeff u = 0 := by
    rw [hz1]; simp [chordCoeffQuadraticAt, WeierstrassChordSeries.c2, hl1c, hn1c, k0, k1]
  have hum : u ∈ TT W (Fin 3) := by
    rw [hz1]
    exact (TT W _).sub_mem ((TT W _).sub_mem ((TT W _).neg_mem m0) m1)
      ((TT W _).mul_mem (lineCoeffQuadratic_mem _ mA1 mA2 mA3 mA4 mA6 hl1m hn1m) hA1m)
  have hsc : MvPowerSeries.constantCoeff s = 0 := by rw [hs1]; simp [huc]
  have hsm : s ∈ TT W (Fin 3) := by rw [hs1]; exact (TT W _).mul_mem hum hB1m
  have hw0 : w0 = l1 * X0 + n1 := by rw [hn1]; ring
  have hw1 : w1 = l1 * X1 + n1 := by rw [hn1]; linear_combination -hl1
  have he1 : chordCoeffCubicAt W l1 * (X0 + X1 + u) + chordCoeffQuadraticAt W l1 n1 = 0 := by
    rw [hz1]; linear_combination (-(chordCoeffQuadraticAt W l1 n1)) * hA1
  have line1 := line_fact hX01 (by rw [← hw0]; exact hG0) (by rw [← hw1]; exact hG1) he1
  have hGu : GG W u (l1 * u + n1) = 0 := by
    have h := line1 u; rw [sub_self, mul_zero] at h; exact h
  have huw : w.subst u = l1 * u + n1 :=
    huniq u _ huc (by simp [hl1c, huc, hn1c]) hGu
  set dd1 := DDs W l1 n1 u with hdd1
  have hdd1c : MvPowerSeries.constantCoeff dd1 = -1 := by simp [hdd1, DDs, huc, hl1c, hn1c]
  have hdd10 : dd1 ≠ 0 := fun h => by simp [h] at hdd1c
  have hsd : s * dd1 = u := by rw [hs1]; linear_combination u * hB1
  have hune : u ≠ 0 := by rw [← hsd]; exact mul_ne_zero hsne hdd10
  have hGs' : GG W s ((l1 * u + n1) * B1) = 0 :=
    G_inv hsd (by linear_combination (l1 * u + n1) * hB1) rfl hdd10 hGu
  have hws : w.subst s = (l1 * u + n1) * B1 :=
    huniq s _ hsc (by simp [hl1c, huc, hn1c]) hGs'
  set lam0 := u ^ 2 * (wU w).subst u with hlam0
  have hlam0c : MvPowerSeries.constantCoeff lam0 = 0 := by simp [hlam0, huc]
  have hlam0m : lam0 ∈ TT W (Fin 3) :=
    (TT W _).mul_mem ((TT W _).pow_mem hum 2) (psubst_mem (wU_coeff_mem hw) hum huc)
  have hl0 : l1 * u + n1 = lam0 * u := by
    rw [← huw, WeierstrassCoordinateSubstitution.subst_w hwu u huc, hlam0]; ring
  have hws' : w.subst s = lam0 * s := by
    rw [hws, hl0, hs1]; ring

  have hq := q_fact (a2 := MvPowerSeries.C W.a₂) (a4 := MvPowerSeries.C W.a₄)
    (a6 := MvPowerSeries.C W.a₆) (c := X2) hune hdd10 hsd
    (by rw [hdd1, DDs, hl0]) (by rw [← hl0]; exact hGu)

  obtain ⟨l2, n2, r, A2, B2, hl2, hn2, hA2, hz2, hB2, hs2, hl2c, hl2m, hA2m, hB2m⟩ :=
    pair hw s X2 hsc k2 hsm m2
  set F3 := MvPowerSeries.subst ![s, X2] (F2 W w) with hF3
  have hwsc : MvPowerSeries.constantCoeff (w.subst s) = 0 := hwcc s hsc
  have hn2c : MvPowerSeries.constantCoeff n2 = 0 := by rw [hn2]; simp [hwsc, hl2c, hsc]
  have hn2m : n2 ∈ TT W (Fin 3) := by
    rw [hn2]; exact (TT W _).sub_mem (hwm s hsm hsc) ((TT W _).mul_mem hl2m hsm)
  have hrc : MvPowerSeries.constantCoeff r = 0 := by
    rw [hz2]; simp [chordCoeffQuadraticAt, WeierstrassChordSeries.c2, hl2c, hn2c, hsc, k2]
  have hrm : r ∈ TT W (Fin 3) := by
    rw [hz2]
    exact (TT W _).sub_mem ((TT W _).sub_mem ((TT W _).neg_mem hsm) m2)
      ((TT W _).mul_mem (lineCoeffQuadratic_mem _ mA1 mA2 mA3 mA4 mA6 hl2m hn2m) hA2m)
  have hws2 : w.subst s = l2 * s + n2 := by rw [hn2]; ring
  have hw2 : w2 = l2 * X2 + n2 := by rw [hn2]; linear_combination -hl2
  have he2 : chordCoeffCubicAt W l2 * (s + X2 + r) + chordCoeffQuadraticAt W l2 n2 = 0 := by
    rw [hz2]; linear_combination (-(chordCoeffQuadraticAt W l2 n2)) * hA2
  have line2 := line_fact hsX2 (by rw [← hws2]; exact hGw s hsc) (by rw [← hw2]; exact hG2) he2
  set N := 1 - MvPowerSeries.C W.a₃ * n2 - MvPowerSeries.C W.a₆ * n2 ^ 2 with hN
  have hv : n2 * N = chordCoeffCubicAt W l2 * s * X2 * r := by
    have h := line2 0
    simp only [G] at h
    rw [hN]; unfold chordCoeffCubicAt
    linear_combination -h
  set H1 := HHs W X2 (l1 * X2 + n1) w2 with hH1
  set H0 := HHs W X2 (lam0 * X2) w2 with hH0
  have hE1 : (l1 * X2 + n1 - w2) * H1 = chordCoeffCubicAt W l1 * (X2 - X0) * (X2 - X1) * (X2 - u) := by
    have h := G_sub (MvPowerSeries.C W.a₁) (MvPowerSeries.C W.a₂) (MvPowerSeries.C W.a₃)
      (MvPowerSeries.C W.a₄) (MvPowerSeries.C W.a₆) X2 (l1 * X2 + n1) w2
    have hG2' : G (MvPowerSeries.C W.a₁) (MvPowerSeries.C W.a₂) (MvPowerSeries.C W.a₃)
      (MvPowerSeries.C W.a₄) (MvPowerSeries.C W.a₆) X2 w2 = 0 := hG2
    rw [hG2', line1 X2, sub_zero] at h
    rw [hH1]; unfold HHs chordCoeffCubicAt; exact h.symm
  have hE0 : (lam0 * X2 - w2) * H0 = X2 * chordCoeffCubicAt W lam0 * (X2 - u) * (X2 - s) := by
    have h := G_sub (MvPowerSeries.C W.a₁) (MvPowerSeries.C W.a₂) (MvPowerSeries.C W.a₃)
      (MvPowerSeries.C W.a₄) (MvPowerSeries.C W.a₆) X2 (lam0 * X2) w2
    have hG2' : G (MvPowerSeries.C W.a₁) (MvPowerSeries.C W.a₂) (MvPowerSeries.C W.a₃)
      (MvPowerSeries.C W.a₄) (MvPowerSeries.C W.a₆) X2 w2 = 0 := hG2
    rw [hG2', hq, sub_zero] at h
    rw [hH0]; unfold HHs chordCoeffCubicAt; exact h.symm
  have hnu : (X2 - s) * n2 = s * (lam0 * X2 - w2) := by
    linear_combination (X2 - s) * hn2 - s * hl2 + X2 * hws'
  have hK : (X2 - s) * s * X2 * (chordCoeffCubicAt W l2 * r * H0 - chordCoeffCubicAt W lam0 * (X2 - u) * N) = 0 := by
    linear_combination (-(X2 - s) * H0) * hv + (N * H0) * hnu + (N * s) * hE0
  have hK' : chordCoeffCubicAt W l2 * r * H0 = chordCoeffCubicAt W lam0 * (X2 - u) * N := by
    have hne : (X2 - s) * s * X2 ≠ 0 :=
      mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr (Ne.symm hsX2)) hsne) hX2ne
    exact sub_eq_zero.mp ((mul_eq_zero.mp hK).resolve_left hne)
  set dd2 := DDs W l2 n2 r with hdd2
  have hr : r = F3 * dd2 := by rw [hs2]; linear_combination -r * hB2

  have hH1c : MvPowerSeries.constantCoeff H1 = -1 := by
    simp [hH1, HHs, Hv, k2, hl1c, hn1c, hw2c]
  have hH0c : MvPowerSeries.constantCoeff H0 = -1 := by
    simp [hH0, HHs, Hv, k2, hlam0c, hw2c]
  have hNc : MvPowerSeries.constantCoeff N = 1 := by simp [hN, hn2c]
  have hC30c : MvPowerSeries.constantCoeff (chordCoeffCubicAt W lam0) = 1 := by simp [chordCoeffCubicAt, c3, hlam0c]
  have hPc : MvPowerSeries.constantCoeff (H1 * chordCoeffCubicAt W lam0 * N) = -1 := by
    simp [hH1c, hC30c, hNc]
  set Y := (H1 * chordCoeffCubicAt W lam0 * N)⁻¹ with hYd
  have hY : H1 * chordCoeffCubicAt W lam0 * N * Y = 1 :=
    MvPowerSeries.mul_inv_cancel _ (by rw [hPc]; exact neg_ne_zero.mpr one_ne_zero)
  have hPm : H1 * chordCoeffCubicAt W lam0 * N ∈ TT W (Fin 3) := by
    refine (TT W _).mul_mem ((TT W _).mul_mem ?_ (lineCoeffCubic_mem _ mA2 mA4 mA6 hlam0m)) ?_
    · exact Hv_mem _ mA1 mA2 mA3 mA4 mA6 m2 ((TT W _).add_mem ((TT W _).mul_mem hl1m m2) hn1m)
        (hwm X2 m2 k2)
    · exact (TT W _).sub_mem ((TT W _).sub_mem (TT W _).one_mem ((TT W _).mul_mem mA3 hn2m))
        ((TT W _).mul_mem mA6 ((TT W _).pow_mem hn2m 2))
  have hYm : Y ∈ TT W (Fin 3) :=
    inv_mem_TT hPm (by rw [hPc]; exact neg_ne_zero.mpr one_ne_zero)
      (by rw [hPc, inv_neg, inv_one]; exact Subalgebra.neg_mem _ (Subalgebra.one_mem _))
  have hC31c : MvPowerSeries.constantCoeff (chordCoeffCubicAt W l1) = 1 := by simp [chordCoeffCubicAt, c3, hl1c]
  have hC32c : MvPowerSeries.constantCoeff (chordCoeffCubicAt W l2) = 1 := by simp [chordCoeffCubicAt, c3, hl2c]
  have hdd2c : MvPowerSeries.constantCoeff dd2 = -1 := by simp [hdd2, DDs, hrc, hl2c, hn2c]
  refine ⟨V0 * V1 * V2 * chordCoeffCubicAt W l1 * chordCoeffCubicAt W l2 * dd2 * H0 * Y, ?_, ?_, ?_⟩
  · have hm : V0 * V1 * V2 * chordCoeffCubicAt W l1 * chordCoeffCubicAt W l2 * dd2 * H0 * Y ∈ TT W (Fin 3) := by
      refine (TT W _).mul_mem ((TT W _).mul_mem ((TT W _).mul_mem ((TT W _).mul_mem
        ((TT W _).mul_mem ((TT W _).mul_mem ((TT W _).mul_mem hV0m hV1m) hV2m)
        (lineCoeffCubic_mem _ mA2 mA4 mA6 hl1m)) (lineCoeffCubic_mem _ mA2 mA4 mA6 hl2m)) ?_) ?_) hYm
      · simp only [hdd2, DDs]
        exact (TT W _).add_mem ((TT W _).add_mem ((TT W _).neg_mem (TT W _).one_mem)
          ((TT W _).mul_mem mA1 hrm)) ((TT W _).mul_mem mA3
            ((TT W _).add_mem ((TT W _).mul_mem hl2m hrm) hn2m))
      · exact Hv_mem _ mA1 mA2 mA3 mA4 mA6 m2 ((TT W _).mul_mem hlam0m m2) (hwm X2 m2 k2)
    exact mem_TT.mp hm
  · rw [hYd]
    simp only [map_mul, hV0c, hV1c, hV2c, hC31c, hC32c, hdd2c, hH0c,
      MvPowerSeries.constantCoeff_inv, hPc]
    norm_num
  · have step1 : -(V0 * V1 * V2) * ((w1 - w0) * (X2 - X0) - (w2 - w0) * (X1 - X0))
        = -(V0 * V1 * V2) * (X1 - X0) * (l1 * X2 + n1 - w2) := by
      rw [hw0, hw1]; ring
    rw [step1]
    linear_combination (V0 * V1 * V2 * (X1 - X0) * (l1 * X2 + n1 - w2)) * hY
      + (-Y * (V0 * V1 * V2) * (X1 - X0) * chordCoeffCubicAt W lam0 * N) * hE1
      + (Y * (V0 * V1 * V2) * (X1 - X0) * chordCoeffCubicAt W l1 * (X2 - X0) * (X2 - X1)) * hK'
      + (-Y * (V0 * V1 * V2) * (X1 - X0) * chordCoeffCubicAt W l1 * (X2 - X0) * (X2 - X1) * chordCoeffCubicAt W l2 * H0) * hr

end Formalism.ELL
