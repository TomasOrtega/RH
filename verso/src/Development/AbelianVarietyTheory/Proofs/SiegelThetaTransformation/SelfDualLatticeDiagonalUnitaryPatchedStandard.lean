import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.Patch

open GlobalTheory.SW.Base

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Establish `ex : ∃ a : ℕ, 0 < a ∧ (a : 𝓞 E) ∈ 𝔞` using `⟨Ideal.absNorm 𝔞, Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff]), Ideal.absNorm_mem 𝔞⟩`. Take `⟨ha0, ha⟩` from `Nat.find_spec ex`. Use `⟨Nat.find ex, ha0, ?_, ha⟩` and prove the remaining obligations. Take `⟨x, hx, y, hy, hxy⟩` from `Ideal.isCoprime_iff_exists.1 h`. Take `⟨z, rfl⟩` from `Ideal.mem_span_singleton'.1 hy`.

Take `⟨a', ha'⟩` from `Nat.gcd_dvd_left (Nat.find ex) M`. Take `⟨m', hm'⟩` from `Nat.gcd_dvd_right (Nat.find ex) M`. Use `set g := Nat.gcd (Nat.find ex) M with hg`. Establish `hpos : 0 < a'` using `Nat.pos_of_ne_zero (by rintro rfl; omega)`. Establish `hmem : (a' : 𝓞 E) ∈ 𝔞`.

Establish `e : (a' : 𝓞 E) = a' * x + (z * m') * (Nat.find ex : ℕ)`. Establish `e1 : (M : 𝓞 E) = g * m'` using `by exact_mod_cast congrArg (Nat.cast : ℕ → 𝓞 E) hm'`. Establish `e2 : ((Nat.find ex : ℕ) : 𝓞 E) = g * a'` using `by exact_mod_cast congrArg (Nat.cast : ℕ → 𝓞 E) ha'`. Rewrite using `[e2]`. Rewrite `hxy` using `[e1]`.

Take the linear combination `(-(a' : 𝓞 E)) * hxy`. Rewrite using `[e]`. Conclude with `𝔞.add_mem (𝔞.mul_mem_left _ hx) (𝔞.mul_mem_left _ ha)`. Establish `hle : Nat.find ex ≤ a'` using `Nat.find_min' ex ⟨hpos, hmem⟩`. Establish `hg0 : 0 < g` using `Nat.pos_of_ne_zero (by intro h; rw [h] at ha'; omega)`.

Establish `: g ≤ 1`. Assume the negation of the conclusion as `hc`. Establish `: 2 * a' ≤ g * a'` using `Nat.mul_le_mul_right _ (by omega)`. Use linear arithmetic over natural numbers and integers. Use `show g = 1`.

Use linear arithmetic over natural numbers and integers.
-/
theorem exists_nat_coprime (𝔞 : Ideal (𝓞 E)) (M : ℕ) (h0 : 𝔞 ≠ ⊥)
    (h : IsCoprime 𝔞 (Ideal.span {(M : 𝓞 E)})) : ∃ a : ℕ, 0 < a ∧ a.Coprime M ∧ (a : 𝓞 E) ∈ 𝔞 := by
  have ex : ∃ a : ℕ, 0 < a ∧ (a : 𝓞 E) ∈ 𝔞 :=
    ⟨Ideal.absNorm 𝔞, Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff]), Ideal.absNorm_mem 𝔞⟩
  obtain ⟨ha0, ha⟩ := Nat.find_spec ex
  refine ⟨Nat.find ex, ha0, ?_, ha⟩
  obtain ⟨x, hx, y, hy, hxy⟩ := Ideal.isCoprime_iff_exists.1 h
  obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  obtain ⟨a', ha'⟩ := Nat.gcd_dvd_left (Nat.find ex) M
  obtain ⟨m', hm'⟩ := Nat.gcd_dvd_right (Nat.find ex) M
  set g := Nat.gcd (Nat.find ex) M with hg
  have hpos : 0 < a' := Nat.pos_of_ne_zero (by rintro rfl; omega)
  have hmem : (a' : 𝓞 E) ∈ 𝔞 := by
    have e : (a' : 𝓞 E) = a' * x + (z * m') * (Nat.find ex : ℕ) := by
      have e1 : (M : 𝓞 E) = g * m' := by exact_mod_cast congrArg (Nat.cast : ℕ → 𝓞 E) hm'
      have e2 : ((Nat.find ex : ℕ) : 𝓞 E) = g * a' := by exact_mod_cast congrArg (Nat.cast : ℕ → 𝓞 E) ha'
      rw [e2]
      rw [e1] at hxy
      linear_combination (-(a' : 𝓞 E)) * hxy
    rw [e]
    exact 𝔞.add_mem (𝔞.mul_mem_left _ hx) (𝔞.mul_mem_left _ ha)
  have hle : Nat.find ex ≤ a' := Nat.find_min' ex ⟨hpos, hmem⟩
  have hg0 : 0 < g := Nat.pos_of_ne_zero (by intro h; rw [h] at ha'; omega)
  have : g ≤ 1 := by
    by_contra hc
    have : 2 * a' ≤ g * a' := Nat.mul_le_mul_right _ (by omega)
    omega
  show g = 1
  omega

omit [NumberField E] in
/- English proof (translation)
The claim follows from `e ▸ h`.
-/
theorem int_congr {x y : E} (h : IsIntegral ℤ x) (e : y = x) : IsIntegral ℤ y := e ▸ h

omit [NumberField E] in
/- English proof (translation)
The claim follows from `(Ideal.mul_le_inf h).1`.
-/
theorem mem_left {J J' : Ideal (𝓞 E)} {j : 𝓞 E} (h : j ∈ J * J') : j ∈ J := (Ideal.mul_le_inf h).1

omit [NumberField E] in
/- English proof (translation)
The claim follows from `(Ideal.mul_le_inf h).2`.
-/
theorem mem_right {J J' : Ideal (𝓞 E)} {j : 𝓞 E} (h : j ∈ J * J') : j ∈ J' := (Ideal.mul_le_inf h).2

variable [IsCMField E] {n : ℕ}

/- English proof (translation)
Simplify using `[Base.herm_one, Finset.mul_sum, _root_.mul_assoc]`.
-/
theorem herm_smul_left (c : E) (x y : Fin n → E) : herm 1 (c • x) y = c * herm 1 x y := by
  simp [Base.herm_one, Finset.mul_sum, _root_.mul_assoc]

/- English proof (translation)
Simplify using `[Base.herm_one, Finset.mul_sum, cc, mul_left_comm]`.
-/
theorem herm_nat_right (c : ℕ) (x y : Fin n → E) : herm 1 x ((c : E) • y) = c * herm 1 x y := by
  simp [Base.herm_one, Finset.mul_sum, cc, mul_left_comm]

omit [IsCMField E] in
/- English proof (translation)
Use `mem_of_coprime (stdL E 1) h (v := fun _ => x) ((mem_stdL _).2 fun _ => h1) ((mem_stdL _).2 fun _ => h2)` as an intermediate fact. Conclude with `(mem_stdL _).1 this 0`.
-/
theorem int_of_coprime {a b : ℕ} (h : a.Coprime b) {x : E} (h1 : IsIntegral ℤ ((a : E) * x))
    (h2 : IsIntegral ℤ ((b : E) * x)) : IsIntegral ℤ x := by
  have := mem_of_coprime (stdL E 1) h (v := fun _ => x) ((mem_stdL _).2 fun _ => h1)
    ((mem_stdL _).2 fun _ => h2)
  exact (mem_stdL _).1 this 0

/- English proof (translation)
Take `⟨hS, hSsd, -⟩` from `Base.stdL_mem_Vset (E := E) n M`. Establish `k1 : ∀ v ∈ A, (M : E) • (t : E) • v ∈ stdL E n` using `fun v hv => by simpa using h1 _ hJ v hv`. Establish `k2 : ∀ v ∈ stdL E n, (M : E) • (t : E) • v ∈ A` using `fun v hv => by simpa using h2 _ hJ' v hv`. Set `C : Lt E n` to `{ carrier := {v | (M : E) • v ∈ A ∧ (t : E) • v ∈ stdL E n} add_mem' := fun ha hb => ⟨by rw [smul_add]; exact A.add_mem ha.1 hb.1, by rw [smul_add]; exact (stdL E n).add_mem ha.2 hb.2⟩ zero_mem' := ⟨by simp, by simp⟩ smul_mem' := fun c v hv => ⟨by rw [smul_comm]; exact A.smul_mem …`. Establish `mC : ∀ v, v ∈ C ↔ (M : E) • v ∈ A ∧ (t : E) • v ∈ stdL E n` using `fun v => Iff.rfl`.

Establish `cA : ∀ v ∈ A, (M : E) • v ∈ C` using `fun v hv => (mC _).2 ⟨nat_smul_mem _ _ (nat_smul_mem _ _ hv), by rw [smul_comm]; exact k1 v hv⟩`. Establish `cS : ∀ v ∈ stdL E n, (t : E) • v ∈ C` using `fun v hv => (mC _).2 ⟨k2 v hv, nat_smul_mem _ _ (nat_smul_mem _ _ hv)⟩`. Use `⟨C, ⟨?_, fun x => ⟨fun hx y hy => ?_, fun hx => ?_⟩, t, ht, htM, fun v hv => hv.2, cS⟩, ?_, ?_⟩` and prove the remaining obligations. Establish `hle : C ≤ A ⊔ stdL E n` using `fun v hv => mem_of_coprime _ htM (Submodule.mem_sup_right hv.2) (Submodule.mem_sup_left hv.1) haveI := isNoetherian_of_fg_of_noetherian _ (hA.sup hS) haveI := isNoetherian_of_le hle`. Conclude with `Module.Finite.iff_fg.1 inferInstance`.

Establish `a1` using `(hsd _).1 hx.1 _ hy.1`. Establish `a2` using `(hSsd _).1 hx.2 _ hy.2`. Rewrite `a1`, `a2` using `[herm_smul_left, herm_nat_right, ← _root_.mul_assoc, ← Nat.cast_mul]`. Conclude with `int_of_coprime (Nat.Coprime.mul_left (htM.mul_right htM) (htM.mul_right htM)) a2 a1`. Use `(mC _).2 ⟨(hsd _).2 fun y hy => ?_, (hSsd _).2 fun y hy => ?_⟩` and prove the remaining obligations.

Rewrite using `[herm_smul_left, ← herm_nat_right]`. Conclude with `hx _ (cA y hy)`. Rewrite using `[herm_smul_left, ← herm_nat_right]`. Conclude with `hx _ (cS y hy)`. Use `Submodule.smul_le.2 fun j hj v hv => (mC _).2 ⟨nat_smul_mem _ _ (A.smul_mem j hv), ?_⟩` and prove the remaining obligations.

Rewrite using `[smul_comm (t : E) j v]`. Conclude with `h1 j (mem_left hj) v hv`. Use `Submodule.smul_le.2 fun j hj v hv => ?_` and prove the remaining obligations. Use `mem_of_coprime A (s := t * t) (R := M) (Nat.Coprime.mul_left htM htM) ?_ ?_` and prove the remaining obligations. Use `h2 j (mem_right hj) _ ((mC v).1 hv).2` as an intermediate fact.

Rewrite using `[smul_comm _ j v, Nat.cast_mul, mul_smul]`. Conclude with `this`. Rewrite using `[smul_comm _ j v]`. Conclude with `A.smul_mem j ((mC v).1 hv).1`.
-/
theorem patch {M t : ℕ} (ht : 0 < t) (htM : t.Coprime M) (J J' : Ideal (𝓞 E)) (hJ : (M : 𝓞 E) ∈ J)
    (hJ' : (M : 𝓞 E) ∈ J') (A : Lt E n) (hA : A.FG) (hsd : ∀ x, x ∈ A ↔ ∀ y ∈ A, IsIntegral ℤ (herm 1 x y))
    (h1 : ∀ j ∈ J, ∀ v ∈ A, (j : E) • (t : E) • v ∈ stdL E n)
    (h2 : ∀ j ∈ J', ∀ v ∈ stdL E n, (j : E) • (t : E) • v ∈ A) :
    ∃ C ∈ Vset E n M, (J * J') • A ≤ C ∧ (J * J') • C ≤ A := by
  obtain ⟨hS, hSsd, -⟩ := Base.stdL_mem_Vset (E := E) n M
  have k1 : ∀ v ∈ A, (M : E) • (t : E) • v ∈ stdL E n := fun v hv => by simpa using h1 _ hJ v hv
  have k2 : ∀ v ∈ stdL E n, (M : E) • (t : E) • v ∈ A := fun v hv => by simpa using h2 _ hJ' v hv
  let C : Lt E n :=
    { carrier := {v | (M : E) • v ∈ A ∧ (t : E) • v ∈ stdL E n}
      add_mem' := fun ha hb => ⟨by rw [smul_add]; exact A.add_mem ha.1 hb.1,
        by rw [smul_add]; exact (stdL E n).add_mem ha.2 hb.2⟩
      zero_mem' := ⟨by simp, by simp⟩
      smul_mem' := fun c v hv => ⟨by rw [smul_comm]; exact A.smul_mem c hv.1,
        by rw [smul_comm]; exact (stdL E n).smul_mem c hv.2⟩ }
  have mC : ∀ v, v ∈ C ↔ (M : E) • v ∈ A ∧ (t : E) • v ∈ stdL E n := fun v => Iff.rfl
  have cA : ∀ v ∈ A, (M : E) • v ∈ C := fun v hv =>
    (mC _).2 ⟨nat_smul_mem _ _ (nat_smul_mem _ _ hv), by rw [smul_comm]; exact k1 v hv⟩
  have cS : ∀ v ∈ stdL E n, (t : E) • v ∈ C := fun v hv =>
    (mC _).2 ⟨k2 v hv, nat_smul_mem _ _ (nat_smul_mem _ _ hv)⟩
  refine ⟨C, ⟨?_, fun x => ⟨fun hx y hy => ?_, fun hx => ?_⟩, t, ht, htM, fun v hv => hv.2, cS⟩, ?_, ?_⟩
  · have hle : C ≤ A ⊔ stdL E n := fun v hv =>
      mem_of_coprime _ htM (Submodule.mem_sup_right hv.2) (Submodule.mem_sup_left hv.1)
    haveI := isNoetherian_of_fg_of_noetherian _ (hA.sup hS)
    haveI := isNoetherian_of_le hle
    exact Module.Finite.iff_fg.1 inferInstance
  · have a1 := (hsd _).1 hx.1 _ hy.1
    have a2 := (hSsd _).1 hx.2 _ hy.2
    rw [herm_smul_left, herm_nat_right, ← _root_.mul_assoc, ← Nat.cast_mul] at a1 a2
    exact int_of_coprime (Nat.Coprime.mul_left (htM.mul_right htM) (htM.mul_right htM)) a2 a1
  · refine (mC _).2 ⟨(hsd _).2 fun y hy => ?_, (hSsd _).2 fun y hy => ?_⟩
    · rw [herm_smul_left, ← herm_nat_right]; exact hx _ (cA y hy)
    · rw [herm_smul_left, ← herm_nat_right]; exact hx _ (cS y hy)
  · refine Submodule.smul_le.2 fun j hj v hv => (mC _).2 ⟨nat_smul_mem _ _ (A.smul_mem j hv), ?_⟩
    rw [smul_comm (t : E) j v]; exact h1 j (mem_left hj) v hv
  · refine Submodule.smul_le.2 fun j hj v hv => ?_
    refine mem_of_coprime A (s := t * t) (R := M) (Nat.Coprime.mul_left htM htM) ?_ ?_
    · have := h2 j (mem_right hj) _ ((mC v).1 hv).2
      rw [smul_comm _ j v, Nat.cast_mul, mul_smul]; exact this
    · rw [smul_comm _ j v]; exact A.smul_mem j ((mC v).1 hv).1

/- English proof (translation)
Simplify using `[cc]`.
-/
theorem cc_mul (x y : E) : cc (x * y) = cc x * cc y := by simp [cc]

/- English proof (translation)
Set `g : (Fin n → E) →ₗ[𝓞 E] (Fin n → E)` to `(Matrix.mulVecLin (Matrix.diagonal d)).restrictScalars (𝓞 E)`. Establish `hg : ∀ v, g v = fun k => d k * v k` using `fun v => by`. Use extensionality with `k`. Simplify using `[g, Matrix.mulVec_diagonal]`. Establish `mA : ∀ v, v ∈ Λ.map g ↔ (fun k => cc (d k) * v k) ∈ Λ` using `fun v => by`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, hw, rfl⟩`. Establish `: (fun k => cc (d k) * g w k) = w`. Use extensionality with `k`. Rewrite using `[hg]`.

Simplify using `only`. Rewrite using `[← _root_.mul_assoc, hd, _root_.one_mul]`. Rewrite using `[this]`. Conclude with `hw`. Introduce `hv`.

Use `⟨_, hv, ?_⟩` and prove the remaining obligations. Use extensionality with `k`. Rewrite using `[hg]`. Simplify using `only`. Rewrite using `[← _root_.mul_assoc, mul_comm (d k), hd, _root_.one_mul]`.

Establish `hh : ∀ x y : Fin n → E, herm 1 (fun k => cc (d k) * x k) y = herm 1 x (g y)` using `fun x y => by`. Rewrite using `[hg, Base.herm_one, Base.herm_one]`. Conclude with `Finset.sum_congr rfl fun k _ => by rw [cc_mul]; ring`. Use `⟨Λ.map g, hfg.map g, fun x => ?_, mA⟩` and prove the remaining obligations. Rewrite using `[mA, hsd]`.

Simplify using `only [hh]`. Conclude with `⟨by rintro h _ ⟨y, hy, rfl⟩; exact h y hy, fun h y hy => h _ ⟨y, hy, rfl⟩⟩`.
-/
theorem moved (d : Fin n → E) (hd : ∀ k, cc (d k) * d k = 1) (Λ : Lt E n) (hfg : Λ.FG)
    (hsd : ∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) :
    ∃ A : Lt E n, A.FG ∧ (∀ x, x ∈ A ↔ ∀ y ∈ A, IsIntegral ℤ (herm 1 x y)) ∧
      ∀ v, v ∈ A ↔ (fun k => cc (d k) * v k) ∈ Λ := by
  let g : (Fin n → E) →ₗ[𝓞 E] (Fin n → E) := (Matrix.mulVecLin (Matrix.diagonal d)).restrictScalars (𝓞 E)
  have hg : ∀ v, g v = fun k => d k * v k := fun v => by
    ext k; simp [g, Matrix.mulVec_diagonal]
  have mA : ∀ v, v ∈ Λ.map g ↔ (fun k => cc (d k) * v k) ∈ Λ := fun v => by
    constructor
    · rintro ⟨w, hw, rfl⟩
      have : (fun k => cc (d k) * g w k) = w := by
        ext k; rw [hg]; simp only; rw [← _root_.mul_assoc, hd, _root_.one_mul]
      rw [this]; exact hw
    · intro hv
      refine ⟨_, hv, ?_⟩
      ext k; rw [hg]; simp only; rw [← _root_.mul_assoc, mul_comm (d k), hd, _root_.one_mul]
  have hh : ∀ x y : Fin n → E, herm 1 (fun k => cc (d k) * x k) y = herm 1 x (g y) := fun x y => by
    rw [hg, Base.herm_one, Base.herm_one]
    exact Finset.sum_congr rfl fun k _ => by rw [cc_mul]; ring
  refine ⟨Λ.map g, hfg.map g, fun x => ?_, mA⟩
  rw [mA, hsd]
  simp only [hh]
  exact ⟨by rintro h _ ⟨y, hy, rfl⟩; exact h y hy, fun h y hy => h _ ⟨y, hy, rfl⟩⟩

/- English proof (translation)
Introduce `E _ _ _ n r M 𝔍 𝔞 α hM hMJ _ hα hsp hco h hh`. Establish `hα' : (α : E) ≠ 0` using `by exact_mod_cast hα`. Establish `hcα : cc (α : E) ≠ 0` using `by simpa [cc] using hα'`. Use `set d : Fin n → E := fun k : Fin n => if (k : ℕ) < r then 1 else cc (α : E) / (α : E) with hdd`. Establish `hcd : ∀ k, cc (d k) = if (k : ℕ) < r then 1 else (α : E) / cc (α : E)` using `fun k => by`.

Apply the tactic sequence `simp only [hdd]; split_ifs <;> simp [cc]`. Establish `hd : ∀ k, cc (d k) * d k = 1` using `fun k => by`. Rewrite using `[hcd]`. Simplify using `only [hdd]`. Use `split_ifs`.

Simplify using the standard rewrite rules. Clear the denominators using the available nonvanishing facts. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Substitute `hh` using the available equality.

Rewrite using `[Matrix.mul_diagonal]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using `[ccT, hd]`. Simplify using `[ccT, Matrix.one_apply, hij, Matrix.diagonal_apply, Ne.symm hij, cc]`.

Introduce and unpack `Λ ⟨hfg, hsd, s, hs, hsM, hΛS, hSΛ⟩`. Take `⟨A, hA, hAsd, mA⟩` from `moved d hd Λ hfg hsd`. Establish `h𝔞 : 𝔞 ≠ ⊥`. Introduce and unpack `rfl`. Rewrite `hsp` using `[Ideal.mul_bot, Ideal.span_singleton_eq_bot]`.

Conclude with `hα hsp`. Take `⟨a, ha0, haM, ha⟩` from `exists_nat_coprime 𝔞 M h𝔞 hco`. Establish `cnat : ∀ k : ℕ, IsIntegral ℤ (k : E)` using `fun k => by`. Simplify using `using isIntegral_algebraMap (R := ℤ) (A := E) (x := (k : ℤ))`. Establish `q1 : ∀ j ∈ 𝔍, IsIntegral ℤ ((j : E) * a / α)` using `fun j hj => by`.

Establish `: j * a ∈ Ideal.span {α}` using `hsp ▸ Ideal.mul_mem_mul hj ha`. Take `⟨z, hz⟩` from `Ideal.mem_span_singleton'.1 this`. Establish `e : (j : E) * a / α = z`. Rewrite using `[div_eq_iff hα']`. Conclude with `congrArg (fun u : 𝓞 E => (u : E)) hz.symm` after adjusting the coercions.

Rewrite using `[e]`. Conclude with `z.isIntegral_coe`. Establish `q2 : ∀ j ∈ conjI 𝔍, IsIntegral ℤ ((j : E) * a / cc (α : E))` using `fun j hj => by`. Proceed by induction on `hj using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨b, hb, e⟩` from `hx`. Use `isIntegral_cc (q1 b hb)` as an intermediate fact. Rewrite using `[e]`. Simplify `this` using `[cc]`. Consider the case `zero => simpa using isIntegral_zero`.

Consider the case `add x y _ _ hx hy`. Use `int_congr (hx.add hy) ?_` and prove the remaining obligations. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Consider the case `smul c x _ hx`.

Use `int_congr (c.isIntegral_coe.mul hx) ?_` and prove the remaining obligations. Rewrite using `[smul_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `p1 : ∀ j ∈ 𝔍, ∀ k, IsIntegral ℤ ((j : E) * a * d k)` using `fun j hj k => by`.

Simplify using `only [hdd]`. Use `split_ifs`. Rewrite using `[_root_.mul_one]`. Conclude with `j.isIntegral_coe.mul (cnat a)`. Use `int_congr ((q1 j hj).mul (isIntegral_cc α.isIntegral_coe)) ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree. Establish `p2 : ∀ j ∈ conjI 𝔍, ∀ k, IsIntegral ℤ ((j : E) * a * cc (d k))` using `fun j hj k => by`. Rewrite using `[hcd]`. Use `split_ifs`. Rewrite using `[_root_.mul_one]`.

Conclude with `j.isIntegral_coe.mul (cnat a)`. Use `int_congr ((q2 j hj).mul α.isIntegral_coe) ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `hMJ' : (M : 𝓞 E) ∈ conjI 𝔍` using `Ideal.subset_span ⟨M, hMJ, by simp [cc]⟩`. Establish `h1 : ∀ j ∈ 𝔍, ∀ v ∈ A, (j : E) • ((s * a : ℕ) : E) • v ∈ stdL E n` using `fun j hj v hv => by`.

Use `(mem_stdL _).1 (hΛS _ ((mA v).1 hv))` as an intermediate fact. Use `(mem_stdL _).2 fun k => ?_` and prove the remaining obligations. Use `int_congr ((p1 j hj k).mul (this k)) ?_` and prove the remaining obligations. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Use `push_cast`.

Take the linear combination `(-((j : E) * a * s * v k)) * hd k`. Establish `h2 : ∀ j ∈ conjI 𝔍, ∀ v ∈ stdL E n, (j : E) • ((s * a : ℕ) : E) • v ∈ A` using `fun j hj v hv => by`. Use `hSΛ (fun k => (j : E) * a * cc (d k) * v k) ((mem_stdL _).2 fun k => (p2 j hj k).mul ((mem_stdL _).1 hv k))` as an intermediate fact. Rewrite using `[mA]`. Use `this using 1` and compare the differences between its conclusion and the goal.

Use extensionality with `k`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `ht : 0 < s * a` using `Nat.mul_pos hs ha0`.

Take `⟨C, hC, c1, c2⟩` from `patch ht (Nat.Coprime.mul_left hsM haM) 𝔍 (conjI 𝔍) hMJ hMJ' A hA hAsd h1 h2`. Use `⟨C, hC, A, ⟨hA, hAsd, M * (s * a), Nat.mul_pos hM ht, Nat.coprime_one_right _, fun v hv => ?_, fun v hv => ?_⟩, fun v => ?_, c1, c2⟩` and prove the remaining obligations. Rewrite using `[Nat.cast_mul, mul_smul]`. Simplify using `using h1 _ hMJ v hv`. Rewrite using `[Nat.cast_mul, mul_smul]`.

Simplify using `using h2 _ hMJ' v hv`. Rewrite using `[mA, hh]`. Establish `: (fun k => cc (d k) * (Matrix.diagonal d *ᵥ v) k) = v`. Use extensionality with `k`. Rewrite using `[Matrix.mulVec_diagonal, ← _root_.mul_assoc, hd, _root_.one_mul]`.

Rewrite using `[this]`.
-/
theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n r M : ℕ) (𝔍 𝔞 : Ideal (𝓞 E)) (α : 𝓞 E), 0 < M → (M : 𝓞 E) ∈ 𝔍 → IsCoprime 𝔍 (conjI 𝔍) → α ≠ 0 → Ideal.span {α} = 𝔍 * 𝔞 → IsCoprime 𝔞 (Ideal.span {(M : 𝓞 E)}) → ∀ h : Matrix (Fin n) (Fin n) E, h = Matrix.diagonal (fun k : Fin n => if (k : ℕ) < r then 1 else cc (α : E) / (α : E)) → ccT h * h = 1 ∧ ∀ Λ ∈ Vset E n M, ∃ Λ' ∈ Vset E n M, ∃ Λ'' ∈ Vset E n 1, Moves h Λ Λ'' ∧ (𝔍 * conjI 𝔍) • Λ'' ≤ Λ' ∧ (𝔍 * conjI 𝔍) • Λ' ≤ Λ'' := by
  intro E _ _ _ n r M 𝔍 𝔞 α hM hMJ _ hα hsp hco h hh
  have hα' : (α : E) ≠ 0 := by exact_mod_cast hα
  have hcα : cc (α : E) ≠ 0 := by simpa [cc] using hα'
  set d : Fin n → E := fun k : Fin n => if (k : ℕ) < r then 1 else cc (α : E) / (α : E) with hdd
  have hcd : ∀ k, cc (d k) = if (k : ℕ) < r then 1 else (α : E) / cc (α : E) := fun k => by
    simp only [hdd]; split_ifs <;> simp [cc]
  have hd : ∀ k, cc (d k) * d k = 1 := fun k => by
    rw [hcd]; simp only [hdd]; split_ifs
    · simp
    · field_simp
  refine ⟨?_, ?_⟩
  · ext i j
    subst hh
    rw [Matrix.mul_diagonal]
    by_cases hij : i = j
    · subst hij; simp [ccT, hd]
    · simp [ccT, Matrix.one_apply, hij, Matrix.diagonal_apply, Ne.symm hij, cc]
  rintro Λ ⟨hfg, hsd, s, hs, hsM, hΛS, hSΛ⟩
  obtain ⟨A, hA, hAsd, mA⟩ := moved d hd Λ hfg hsd
  have h𝔞 : 𝔞 ≠ ⊥ := by
    rintro rfl
    rw [Ideal.mul_bot, Ideal.span_singleton_eq_bot] at hsp
    exact hα hsp
  obtain ⟨a, ha0, haM, ha⟩ := exists_nat_coprime 𝔞 M h𝔞 hco
  have cnat : ∀ k : ℕ, IsIntegral ℤ (k : E) := fun k => by
    simpa using isIntegral_algebraMap (R := ℤ) (A := E) (x := (k : ℤ))
  have q1 : ∀ j ∈ 𝔍, IsIntegral ℤ ((j : E) * a / α) := fun j hj => by
    have : j * a ∈ Ideal.span {α} := hsp ▸ Ideal.mul_mem_mul hj ha
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 this
    have e : (j : E) * a / α = z := by
      rw [div_eq_iff hα']; exact_mod_cast congrArg (fun u : 𝓞 E => (u : E)) hz.symm
    rw [e]; exact z.isIntegral_coe
  have q2 : ∀ j ∈ conjI 𝔍, IsIntegral ℤ ((j : E) * a / cc (α : E)) := fun j hj => by
    induction hj using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, hb, e⟩ := hx
      have := isIntegral_cc (q1 b hb)
      rw [e]; simpa [cc] using this
    | zero => simpa using isIntegral_zero
    | add x y _ _ hx hy =>
      refine int_congr (hx.add hy) ?_
      push_cast; ring
    | smul c x _ hx =>
      refine int_congr (c.isIntegral_coe.mul hx) ?_
      rw [smul_eq_mul]; push_cast; ring
  have p1 : ∀ j ∈ 𝔍, ∀ k, IsIntegral ℤ ((j : E) * a * d k) := fun j hj k => by
    simp only [hdd]; split_ifs
    · rw [_root_.mul_one]; exact j.isIntegral_coe.mul (cnat a)
    · refine int_congr ((q1 j hj).mul (isIntegral_cc α.isIntegral_coe)) ?_
      ring
  have p2 : ∀ j ∈ conjI 𝔍, ∀ k, IsIntegral ℤ ((j : E) * a * cc (d k)) := fun j hj k => by
    rw [hcd]; split_ifs
    · rw [_root_.mul_one]; exact j.isIntegral_coe.mul (cnat a)
    · refine int_congr ((q2 j hj).mul α.isIntegral_coe) ?_
      ring
  have hMJ' : (M : 𝓞 E) ∈ conjI 𝔍 := Ideal.subset_span ⟨M, hMJ, by simp [cc]⟩
  have h1 : ∀ j ∈ 𝔍, ∀ v ∈ A, (j : E) • ((s * a : ℕ) : E) • v ∈ stdL E n := fun j hj v hv => by
    have := (mem_stdL _).1 (hΛS _ ((mA v).1 hv))
    refine (mem_stdL _).2 fun k => ?_
    refine int_congr ((p1 j hj k).mul (this k)) ?_
    simp only [Pi.smul_apply, smul_eq_mul]; push_cast
    linear_combination (-((j : E) * a * s * v k)) * hd k
  have h2 : ∀ j ∈ conjI 𝔍, ∀ v ∈ stdL E n, (j : E) • ((s * a : ℕ) : E) • v ∈ A := fun j hj v hv => by
    have := hSΛ (fun k => (j : E) * a * cc (d k) * v k)
      ((mem_stdL _).2 fun k => (p2 j hj k).mul ((mem_stdL _).1 hv k))
    rw [mA]
    convert this using 1
    ext k
    simp only [Pi.smul_apply, smul_eq_mul]; push_cast; ring
  have ht : 0 < s * a := Nat.mul_pos hs ha0
  obtain ⟨C, hC, c1, c2⟩ := patch ht (Nat.Coprime.mul_left hsM haM) 𝔍 (conjI 𝔍) hMJ hMJ' A hA hAsd h1 h2
  refine ⟨C, hC, A, ⟨hA, hAsd, M * (s * a), Nat.mul_pos hM ht, Nat.coprime_one_right _, fun v hv => ?_,
    fun v hv => ?_⟩, fun v => ?_, c1, c2⟩
  · rw [Nat.cast_mul, mul_smul]; simpa using h1 _ hMJ v hv
  · rw [Nat.cast_mul, mul_smul]; simpa using h2 _ hMJ' v hv
  · rw [mA, hh]
    have : (fun k => cc (d k) * (Matrix.diagonal d *ᵥ v) k) = v := by
      ext k; rw [Matrix.mulVec_diagonal, ← _root_.mul_assoc, hd, _root_.one_mul]
    rw [this]

end GlobalTheory.Dict.Patch
