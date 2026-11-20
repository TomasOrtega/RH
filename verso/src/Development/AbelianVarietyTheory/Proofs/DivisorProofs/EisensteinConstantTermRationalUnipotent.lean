import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransv

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT)

namespace GlobalTheory.EisCTMid

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

/- English proof (translation)
Rewrite using `[map_mul, Units.val_mul, Matrix.mul_assoc, hq, Matrix.mul_smul, hp, smul_smul, mul_comm]`.
-/
theorem stab_mul {x : Matrix (Fin n) (Fin 1) E} {p q : GAd σ J} {l l' : AF F ⊗[F] E}
    (hp : (matHom _ σ J p).1 * adMat F x = l • adMat F x) (hq : (matHom _ σ J q).1 * adMat F x = l' • adMat F x) :
    (matHom _ σ J (p * q)).1 * adMat F x = (l * l') • adMat F x := by
  rw [map_mul, Units.val_mul, Matrix.mul_assoc, hq, Matrix.mul_smul, hp, smul_smul, mul_comm]

/- English proof (translation)
Use `congrArg (fun z => l⁻¹.1 • ((matHom _ σ J p⁻¹).1 * z)) hp` as an intermediate fact. Simplify using `only [← Matrix.mul_assoc, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mul, Matrix.mul_smul, smul_smul] at this`. Simplify using `using this.symm`.
-/
theorem stab_inv {x : Matrix (Fin n) (Fin 1) E} {p : GAd σ J} {l : (AF F ⊗[F] E)ˣ}
    (hp : (matHom _ σ J p).1 * adMat F x = l.1 • adMat F x) :
    (matHom _ σ J p⁻¹).1 * adMat F x = l⁻¹.1 • adMat F x := by
  have := congrArg (fun z => l⁻¹.1 • ((matHom _ σ J p⁻¹).1 * z)) hp
  simp only [← Matrix.mul_assoc, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mul,
    Matrix.mul_smul, smul_smul] at this
  simpa using this.symm

/- English proof (translation)
Take `⟨p', l', hp', k, hk, rfl⟩` from `hI.1 m`. Establish `e : (matHom _ σ J (p * p')).1 * adMat F x = (l * l').1 • adMat F x`. Rewrite using `[Units.val_mul]`. Conclude with `stab_mul hp hp'`. Rewrite using `[← mul_assoc, hI.2 _ _ e k hk, hI.2 p' l' hp' k hk, map_mul, NNReal.coe_mul]`.
-/
theorem ht_mul {x : Matrix (Fin n) (Fin 1) E} {L : Submodule (𝓞 E) (Fin n → E)} {a : GL (Fin n) (AF F ⊗[F] E)}
    {h : GAd σ J → ℝ} (hI : IsIwaHtG σ J x L a h) {p : GAd σ J} {l : (AF F ⊗[F] E)ˣ}
    (hp : (matHom _ σ J p).1 * adMat F x = l.1 • adMat F x) (m : GAd σ J) :
    h (p * m) = (absE F E l : ℝ) * h m := by
  obtain ⟨p', l', hp', k, hk, rfl⟩ := hI.1 m
  have e : (matHom _ σ J (p * p')).1 * adMat F x = (l * l').1 • adMat F x := by
    rw [Units.val_mul]; exact stab_mul hp hp'
  rw [← mul_assoc, hI.2 _ _ e k hk, hI.2 p' l' hp' k hk, map_mul, NNReal.coe_mul]

/- English proof (translation)
Take `⟨q, -, hq⟩` from `Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hr)`. Establish `hM : (matHom _ σ J p).1 = adMat F q.1` using `by first`. Consider the case `(change ((show HR (AF F) σ J from p) : GL (Fin n) (AF F ⊗[F] E)).1 = _; rw [← hq]; rfl)`. Consider the case `(rw [matHom_apply]; unfold HA.mat; rw [← hq]; rfl)`. Rewrite `hp` using `[hM, ← Matrix.map_mul]`.

Choose the witnesses or unpack the hypotheses as in `⟨i, j, hij⟩ : ∃ i j, x i j ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `hx (Matrix.ext hc)`. Establish `e` using `congrFun (congrFun hp i) j`.

Simplify using `only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at e`. Distinguish the cases in `hy : (q.1 * x) i j = 0`. Establish `hu : IsUnit (l.1 * inclR (F` using `F) (AF F) (x i j)) := l.isUnit.mul ((isUnit_iff_ne_zero.2 hij).map _)`. Rewrite `hu` using `[← e, hy, map_zero, isUnit_zero_iff]`. Use `haveI := subsingleton_of_zero_eq_one hu`.

Rewrite using `[Subsingleton.elim l 1, map_one]`. Establish `hl : l = Units.map (inclR (F` using `F) (AF F)).toMonoidHom (Units.mk0 ((q.1 * x) i j * (x i j)⁻¹) (mul_ne_zero hy (inv_ne_zero hij))) := by`. Use `ext`. Simplify using `only [Units.coe_map, Units.val_mk0, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]`. Rewrite using `[map_mul, e, mul_assoc, ← map_mul, mul_inv_cancel₀ hij, map_one, mul_one]`.

Rewrite using `[hl]`. Conclude with `GlobalTheory.Doubling.absE_inclR _`.
-/
theorem absE_rat {x : Matrix (Fin n) (Fin 1) E} (hx : x ≠ 0) {p : GAd σ J} (hr : p ∈ ratPts σ J)
    {l : (AF F ⊗[F] E)ˣ} (hp : (matHom _ σ J p).1 * adMat F x = l.1 • adMat F x) : absE F E l = 1 := by
  obtain ⟨q, -, hq⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hr)
  have hM : (matHom _ σ J p).1 = adMat F q.1 := by
    first
      | (change ((show HR (AF F) σ J from p) : GL (Fin n) (AF F ⊗[F] E)).1 = _; rw [← hq]; rfl)
      | (rw [matHom_apply]; unfold HA.mat; rw [← hq]; rfl)
  rw [hM, ← Matrix.map_mul] at hp
  obtain ⟨i, j, hij⟩ : ∃ i j, x i j ≠ 0 := by
    by_contra hc; push_neg at hc; exact hx (Matrix.ext hc)
  have e := congrFun (congrFun hp i) j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at e
  by_cases hy : (q.1 * x) i j = 0
  · have hu : IsUnit (l.1 * inclR (F := F) (AF F) (x i j)) := l.isUnit.mul ((isUnit_iff_ne_zero.2 hij).map _)
    rw [← e, hy, map_zero, isUnit_zero_iff] at hu
    haveI := subsingleton_of_zero_eq_one hu
    rw [Subsingleton.elim l 1, map_one]
  · have hl : l = Units.map (inclR (F := F) (AF F)).toMonoidHom (Units.mk0 ((q.1 * x) i j * (x i j)⁻¹)
        (mul_ne_zero hy (inv_ne_zero hij))) := by
      ext
      simp only [Units.coe_map, Units.val_mk0, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
      rw [map_mul, e, mul_assoc, ← map_mul, mul_inv_cancel₀ hij, map_one, mul_one]
    rw [hl]; exact GlobalTheory.Doubling.absE_inclR _

/- English proof (translation)
Introduce `h0`. Establish `h` using `congrFun (congrFun hW.xy 0) 0`. Establish `hX : ∀ m, X m 0 = 0` using `fun m => by simpa [col0] using congrFun (congrFun h0 m) 0`. Simplify using `[Matrix.mul_apply, cT, hX] at h`.
-/
theorem witt_frame_first_column_ne_zero {r : ℕ} {X Y : Matrix (Fin n) (Fin (r + 1)) E} (hW : IsWittFrame σ J X Y) : col0 X ≠ 0 := by
  intro h0
  have h := congrFun (congrFun hW.xy 0) 0
  have hX : ∀ m, X m 0 = 0 := fun m => by simpa [col0] using congrFun (congrFun h0 m) 0
  simp [Matrix.mul_apply, cT, hX] at h

/- English proof (translation)
Establish `hinv : ∀ a : GAd σ J, (matHom _ σ J a⁻¹).1 * (matHom _ σ J a).1 = 1 ∧ (matHom _ σ J a).1 * (matHom _ σ J a⁻¹).1 = 1` using `fun a => by`. Simplify using `only [← Units.val_mul, ← map_mul, inv_mul_cancel, mul_inv_cancel, map_one, Units.val_one, and_self]`. Set `S : Subgroup (GAd σ J)` to `{ carrier := {g | (matHom _ σ J g).1 * adMat F C = adMat F C ∧ adMat F (cT (σ : E →+* E) C * J) * (matHom _ σ J g).1 = adMat F (cT (σ : E →+* E) C * J)} one_mem' := by simp mul_mem' := fun {a b} ha hb => by`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, Units.val_mul, Matrix.mul_assoc, hb.1, ha.1]`.

Rewrite using `[map_mul, Units.val_mul, ← Matrix.mul_assoc, ha.2, hb.2]`. Use the proof step `inv_mem' := fun {a} ha => by`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `conv_lhs => rw [← ha.1, ← Matrix.mul_assoc, (hinv a).1, Matrix.one_mul]`. Use `conv_lhs => rw [← ha.2, Matrix.mul_assoc, (hinv a).2, Matrix.mul_one] }`.

Use `(Subgroup.closure_le S).2 ?_ hν` and prove the remaining obligations. Introduce `g hg`. Take `⟨h1, h2, -⟩` from `hg`. Conclude with `⟨by rw [Matrix.sub_mul, sub_eq_zero, Matrix.one_mul] at h1; exact h1, by rw [Matrix.mul_sub, sub_eq_zero, Matrix.mul_one] at h2; exact h2⟩`.
-/
theorem unip_fix {r : ℕ} {C : Matrix (Fin n) (Fin r) E} {ν : GAd σ J} (hν : ν ∈ unipRad σ J C) :
    (matHom _ σ J ν).1 * adMat F C = adMat F C ∧
      adMat F (cT (σ : E →+* E) C * J) * (matHom _ σ J ν).1 = adMat F (cT (σ : E →+* E) C * J) := by
  have hinv : ∀ a : GAd σ J, (matHom _ σ J a⁻¹).1 * (matHom _ σ J a).1 = 1 ∧
      (matHom _ σ J a).1 * (matHom _ σ J a⁻¹).1 = 1 := fun a => by
    simp only [← Units.val_mul, ← map_mul, inv_mul_cancel, mul_inv_cancel, map_one, Units.val_one, and_self]
  let S : Subgroup (GAd σ J) :=
    { carrier := {g | (matHom _ σ J g).1 * adMat F C = adMat F C ∧
        adMat F (cT (σ : E →+* E) C * J) * (matHom _ σ J g).1 = adMat F (cT (σ : E →+* E) C * J)}
      one_mem' := by simp
      mul_mem' := fun {a b} ha hb => by
        refine ⟨?_, ?_⟩
        · rw [map_mul, Units.val_mul, Matrix.mul_assoc, hb.1, ha.1]
        · rw [map_mul, Units.val_mul, ← Matrix.mul_assoc, ha.2, hb.2]
      inv_mem' := fun {a} ha => by
        refine ⟨?_, ?_⟩
        · conv_lhs => rw [← ha.1, ← Matrix.mul_assoc, (hinv a).1, Matrix.one_mul]
        · conv_lhs => rw [← ha.2, Matrix.mul_assoc, (hinv a).2, Matrix.mul_one] }
  refine (Subgroup.closure_le S).2 ?_ hν
  intro g hg
  obtain ⟨h1, h2, -⟩ := hg
  exact ⟨by rw [Matrix.sub_mul, sub_eq_zero, Matrix.one_mul] at h1; exact h1,
    by rw [Matrix.mul_sub, sub_eq_zero, Matrix.mul_one] at h2; exact h2⟩

end GlobalTheory.EisCTMid

namespace GlobalTheory.EisCTMid

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {x : Matrix (Fin n) (Fin 1) E} {T : Set (ratPts σ J)}

def rep (hT : GlobalTheory.EisCT.IsTransv σ J x T) (γ : ratPts σ J) : ratPts σ J := (hT γ).exists.choose

/- English proof (translation)
The claim follows from `(hT γ).exists.choose_spec`.
-/
theorem rep_spec (hT : GlobalTheory.EisCT.IsTransv σ J x T) (γ : ratPts σ J) :
    rep hT γ ∈ T ∧ GlobalTheory.EisCT.StabL σ J x (γ * (rep hT γ)⁻¹ : ratPts σ J).1 :=
  (hT γ).exists.choose_spec

/- English proof (translation)
Take `⟨hmem, l, hl⟩` from `rep_spec hT (t * μ)`. Take `⟨hfix, -⟩` from `unip_fix (inv_mem hμ)`. Take `⟨-, hJi⟩` from `unip_fix (inv_mem hμ)`. Use `⟨hmem, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨l', hl'⟩`.

Apply `ht.2.1` to reduce the goal to its premises. Use `⟨l * l', ?_⟩` and prove the remaining obligations. Establish `e : (t : GAd σ J) = ((t * μ * (rep hT (t * μ))⁻¹ : ratPts σ J) : GAd σ J) * (rep hT (t * μ) : GAd σ J) * (μ : GAd σ J)⁻¹` using `by simp [mul_assoc]`. Establish `hμi : (matHom _ σ J (μ : GAd σ J)⁻¹).1 * adMat F x = (1 : AF F ⊗[F] E) • adMat F x`. Rewrite using `[one_smul]`.

Conclude with `hfix`. Use `stab_mul (stab_mul hl hl') hμi` as an intermediate fact. Rewrite using `[e, Units.val_mul]`. Simplify using `using this`. Unfold `GlobalTheory.EisCT.OrthL`.

Establish `e : ((rep hT (t * μ) : GAd σ J))⁻¹ = (μ : GAd σ J)⁻¹ * (t : GAd σ J)⁻¹ * ((t * μ * (rep hT (t * μ))⁻¹ : ratPts σ J) : GAd σ J)` using `by simp [mul_assoc]`. Establish `e2 : (matHom _ σ J ((μ : GAd σ J)⁻¹ * (t : GAd σ J)⁻¹ * ((t * μ * (rep hT (t * μ))⁻¹ : ratPts σ J) : GAd σ J))).1 * adMat F x = l.1 • ((matHom _ σ J (μ : GAd σ J)⁻¹).1 * ((matHom _ σ J (t : GAd σ J)⁻¹).1 * adMat F x))`. Simplify using `only [map_mul, Units.val_mul, Matrix.mul_assoc]`. Rewrite using `[hl, Matrix.mul_smul, Matrix.mul_smul]`. Establish `h0` using `ht.2.2`.

Unfold `GlobalTheory.EisCT.OrthL at h0`. Rewrite using `[e, Matrix.mul_assoc, e2, Matrix.mul_smul, ← Matrix.mul_assoc, hJi, ← Matrix.mul_assoc, h0, smul_zero]`.
-/
theorem rep_mid (hT : GlobalTheory.EisCT.IsTransv σ J x T) {μ : ratPts σ J} (hμ : (μ : GAd σ J) ∈ unipRad σ J x)
    {t : ratPts σ J} (ht : t ∈ GlobalTheory.EisCT.midSet σ J x T) : rep hT (t * μ) ∈ GlobalTheory.EisCT.midSet σ J x T := by
  obtain ⟨hmem, l, hl⟩ := rep_spec hT (t * μ)
  obtain ⟨hfix, -⟩ := unip_fix (inv_mem hμ)
  obtain ⟨-, hJi⟩ := unip_fix (inv_mem hμ)
  refine ⟨hmem, ?_, ?_⟩
  · rintro ⟨l', hl'⟩
    apply ht.2.1
    refine ⟨l * l', ?_⟩
    have e : (t : GAd σ J) = ((t * μ * (rep hT (t * μ))⁻¹ : ratPts σ J) : GAd σ J) * (rep hT (t * μ) : GAd σ J) *
        (μ : GAd σ J)⁻¹ := by simp [mul_assoc]
    have hμi : (matHom _ σ J (μ : GAd σ J)⁻¹).1 * adMat F x = (1 : AF F ⊗[F] E) • adMat F x := by
      rw [one_smul]; exact hfix
    have := stab_mul (stab_mul hl hl') hμi
    rw [e, Units.val_mul]; simpa using this
  · unfold GlobalTheory.EisCT.OrthL
    have e : ((rep hT (t * μ) : GAd σ J))⁻¹ = (μ : GAd σ J)⁻¹ * (t : GAd σ J)⁻¹ *
        ((t * μ * (rep hT (t * μ))⁻¹ : ratPts σ J) : GAd σ J) := by simp [mul_assoc]
    have e2 : (matHom _ σ J ((μ : GAd σ J)⁻¹ * (t : GAd σ J)⁻¹ *
        ((t * μ * (rep hT (t * μ))⁻¹ : ratPts σ J) : GAd σ J))).1 * adMat F x =
        l.1 • ((matHom _ σ J (μ : GAd σ J)⁻¹).1 * ((matHom _ σ J (t : GAd σ J)⁻¹).1 * adMat F x)) := by
      simp only [map_mul, Units.val_mul, Matrix.mul_assoc]
      rw [hl, Matrix.mul_smul, Matrix.mul_smul]
    have h0 := ht.2.2
    unfold GlobalTheory.EisCT.OrthL at h0
    rw [e, Matrix.mul_assoc, e2, Matrix.mul_smul, ← Matrix.mul_assoc, hJi, ← Matrix.mul_assoc, h0, smul_zero]

/- English proof (translation)
Take `⟨-, l, hl⟩` from `rep_spec hT (t * μ)`. Establish `e : (t : GAd σ J) * ((μ : GAd σ J) * g) = ((t * μ * (rep hT (t * μ))⁻¹ : ratPts σ J) : GAd σ J) * ((rep hT (t * μ) : GAd σ J) * g)` using `by simp [mul_assoc]`. Rewrite using `[e, ht_mul hI hl, absE_rat hx (SetLike.coe_mem _) hl, NNReal.coe_one, one_mul]`.
-/
theorem rep_ht {L : Submodule (𝓞 E) (Fin n → E)} {a : GL (Fin n) (AF F ⊗[F] E)} {h : GAd σ J → ℝ}
    (hI : IsIwaHtG σ J x L a h) (hx : x ≠ 0) (hT : GlobalTheory.EisCT.IsTransv σ J x T) (μ t : ratPts σ J) (g : GAd σ J) :
    h ((t : GAd σ J) * ((μ : GAd σ J) * g)) = h ((rep hT (t * μ) : GAd σ J) * g) := by
  obtain ⟨-, l, hl⟩ := rep_spec hT (t * μ)
  have e : (t : GAd σ J) * ((μ : GAd σ J) * g) = ((t * μ * (rep hT (t * μ))⁻¹ : ratPts σ J) : GAd σ J) *
      ((rep hT (t * μ) : GAd σ J) * g) := by simp [mul_assoc]
  rw [e, ht_mul hI hl, absE_rat hx (SetLike.coe_mem _) hl, NNReal.coe_one, one_mul]

/- English proof (translation)
Take `⟨-, l, hl⟩` from `rep_spec hT (t * μ)`. Use `(hT (rep hT (t * μ) * μ⁻¹)).unique (rep_spec hT _) ⟨ht, l⁻¹, ?_⟩` and prove the remaining obligations. Establish `e : ((rep hT (t * μ) * μ⁻¹ * t⁻¹ : ratPts σ J) : GAd σ J) = ((t * μ * (rep hT (t * μ))⁻¹ : ratPts σ J) : GAd σ J)⁻¹` using `by simp [mul_assoc]`. Rewrite using `[e]`. Conclude with `stab_inv hl`.
-/
theorem rep_rep (hT : GlobalTheory.EisCT.IsTransv σ J x T) (μ : ratPts σ J) {t : ratPts σ J} (ht : t ∈ T) :
    rep hT (rep hT (t * μ) * μ⁻¹) = t := by
  obtain ⟨-, l, hl⟩ := rep_spec hT (t * μ)
  refine (hT (rep hT (t * μ) * μ⁻¹)).unique (rep_spec hT _) ⟨ht, l⁻¹, ?_⟩
  have e : ((rep hT (t * μ) * μ⁻¹ * t⁻¹ : ratPts σ J) : GAd σ J) =
      ((t * μ * (rep hT (t * μ))⁻¹ : ratPts σ J) : GAd σ J)⁻¹ := by simp [mul_assoc]
  rw [e]; exact stab_inv hl

def midEquiv (hT : GlobalTheory.EisCT.IsTransv σ J x T) (μ : ratPts σ J) (hμ : (μ : GAd σ J) ∈ unipRad σ J x) :
    GlobalTheory.EisCT.midSet σ J x T ≃ GlobalTheory.EisCT.midSet σ J x T where
  toFun t := ⟨rep hT (t.1 * μ), rep_mid hT hμ t.2⟩
  invFun t := ⟨rep hT (t.1 * μ⁻¹), rep_mid hT (by simpa using inv_mem hμ) t.2⟩
  left_inv t := Subtype.ext (rep_rep hT μ t.2.1)
  right_inv t := Subtype.ext (by simpa using rep_rep hT μ⁻¹ t.2.1)

end GlobalTheory.EisCTMid

open GlobalTheory.EisCTMid in

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n J r X Y L a h hS T hT ν hνr hνu s g`. Establish `hx` using `witt_frame_first_column_ne_zero hS.2.2.2.2.1`. Establish `hI` using `hS.2.2.2.2.2.2`. Set `μ : ratPts σ J` to `⟨ν, hνr⟩`. Unfold `GlobalTheory.EisCT.midSum`.

Use `(tsum_congr fun t => ?_).trans ((midEquiv hT μ hνu).tsum_eq (fun t => GlobalTheory.EisCT.fs σ J h s (t.1.1 * g)))` and prove the remaining obligations. Unfold `GlobalTheory.EisCT.fs`. Rewrite using `[show ν = (μ : GAd σ J) from rfl, rep_ht hI hx hT μ t.1 g]`. Both sides reduce to the same expression.
-/
theorem GlobalTheory.EisCTMid.midSum_left_invariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E))
    (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), HidaSetting σ J X Y L a h →
    ∀ T, GlobalTheory.EisCT.IsTransv σ J (col0 X) T → ∀ ν ∈ ratPts σ J, ν ∈ unipRad σ J (col0 X) → ∀ (s : ℂ) (g : GAd σ J),
    GlobalTheory.EisCT.midSum σ J (col0 X) T h s (ν * g) = GlobalTheory.EisCT.midSum σ J (col0 X) T h s g := by
  intro F E _ _ _ _ _ σ n J r X Y L a h hS T hT ν hνr hνu s g
  have hx := witt_frame_first_column_ne_zero hS.2.2.2.2.1
  have hI := hS.2.2.2.2.2.2
  let μ : ratPts σ J := ⟨ν, hνr⟩
  unfold GlobalTheory.EisCT.midSum
  refine (tsum_congr fun t => ?_).trans ((midEquiv hT μ hνu).tsum_eq (fun t => GlobalTheory.EisCT.fs σ J h s (t.1.1 * g)))
  unfold GlobalTheory.EisCT.fs
  rw [show ν = (μ : GAd σ J) from rfl, rep_ht hI hx hT μ t.1 g]
  rfl
