import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.InclEquiv
import Development.AbelianVarietyTheory.Definitions.Divisors.IntegralBound

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial

namespace GlobalTheory.HSShort.ShiftMono

variable {F : Type} [Field F] [NumberField F] (G : Geo F)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem shift_apply_zero (u : Fin G.N → F) (x : Tot G) : shift G u x 0 = 0 := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem shift_apply_succ (u : Fin G.N → F) (x : Tot G) (j : ℕ) : shift G u x (j + 1) = G.mulW j u (x j) := rfl

/- English proof (translation)
Simplify using `only [G.mulW_apply]`. Use `tw_ext (isLB_tens G.K.isLB G.isLBA) G.isLB fun c k y hy hc hk => ?_` and prove the remaining obligations. Rewrite using `[germ_mulSec _ _ _ _ _ _ _ _ _ hc hk, germ_mulSec _ _ _ _ _ _ _ _ _ hc hk, germ_mulSec _ _ _ _ _ _ _ _ _ hc hk, germ_mulSec _ _ _ _ _ _ _ _ _ hc hk]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mulW_comm (j : ℕ) (u v : Fin G.N → F) (m : G.Sec j) :
    G.mulW (j + 1) u (G.mulW j v m) = G.mulW (j + 1) v (G.mulW j u m) := by
  simp only [G.mulW_apply]
  refine tw_ext (isLB_tens G.K.isLB G.isLBA) G.isLB fun c k y hy hc hk => ?_
  rw [germ_mulSec _ _ _ _ _ _ _ _ _ hc hk, germ_mulSec _ _ _ _ _ _ _ _ _ hc hk,
    germ_mulSec _ _ _ _ _ _ _ _ _ hc hk, germ_mulSec _ _ _ _ _ _ _ _ _ hc hk]
  ring

/- English proof (translation)
Use `LinearMap.ext fun x => funext fun j => ?_` and prove the remaining obligations. Break down `j with _ | _ | j` into its components or cases. Both sides reduce to the same expression. Use `show G.mulW 0 u (shift G v x 0) = G.mulW 0 v (shift G u x 0)`. Rewrite using `[shift_apply_zero, shift_apply_zero, map_zero, map_zero]`.

Conclude with `mulW_comm G j u v (x j)`.
-/
theorem shift_comm (u v : Fin G.N → F) : shift G u * shift G v = shift G v * shift G u := by
  refine LinearMap.ext fun x => funext fun j => ?_
  rcases j with _ | _ | j
  · rfl
  · show G.mulW 0 u (shift G v x 0) = G.mulW 0 v (shift G u x 0)
    rw [shift_apply_zero, shift_apply_zero, map_zero, map_zero]
  · exact mulW_comm G j u v (x j)

/- English proof (translation)
Use function extensionality and compare the values at `k`. Break down `k with _ | k` into its components or cases. Rewrite using `[shift_apply_zero, Pi.single_eq_of_ne (by omega)]`. Rewrite using `[shift_apply_succ]`. Distinguish the cases in `hk : k = j`.

Substitute `hk` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[Pi.single_eq_of_ne hk, Pi.single_eq_of_ne (by omega), map_zero]`.
-/
theorem shift_single (j : ℕ) (u : Fin G.N → F) (m : G.Sec j) :
    shift G u (Pi.single j m) = Pi.single (j + 1) (G.mulW j u m) := by
  funext k
  rcases k with _ | k
  · rw [shift_apply_zero, Pi.single_eq_of_ne (by omega)]
  · rw [shift_apply_succ]
    by_cases hk : k = j
    · subst hk; simp
    · rw [Pi.single_eq_of_ne hk, Pi.single_eq_of_ne (by omega), map_zero]

variable (s : Fin G.D → Fin G.N → F)

def mono (α : Fin G.D →₀ ℕ) {j l : ℕ} (h : j + α.degree = l) : G.Sec j →ₗ[F] G.Sec l :=
  mulMono (isLB_tens G.K.isLB G.isLBA) G.isLB (G.sec s) (⟨α, rfl⟩ : MonoDeg (Fin G.D) α.degree)
    ((Nat.cast_add j _).symm.trans (congrArg _ h))

/- English proof (translation)
Substitute `e` using the available equality. Unfold `mono`. Use `tw_ext (isLB_tens G.K.isLB G.isLBA) G.isLB fun c k y hy hc hk => ?_` and prove the remaining obligations. Rewrite using `[germ_mulMono _ _ _ _ _ _ _ _ _ _ hc hk, germ_mulMono _ _ _ _ _ _ _ _ _ _ hc hk, germ_mulMono _ _ _ _ _ _ _ _ _ _ hc hk]`. Simplify using `only [monoVal_add]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem mono_add (α β γ : Fin G.D →₀ ℕ) (e : γ = α + β) {j l' l : ℕ} (h : j + γ.degree = l)
    (h₂ : j + β.degree = l') (h₁ : l' + α.degree = l) (m : G.Sec j) :
    mono G s γ h m = mono G s α h₁ (mono G s β h₂ m) := by
  subst e
  unfold mono
  refine tw_ext (isLB_tens G.K.isLB G.isLBA) G.isLB fun c k y hy hc hk => ?_
  rw [germ_mulMono _ _ _ _ _ _ _ _ _ _ hc hk, germ_mulMono _ _ _ _ _ _ _ _ _ _ hc hk,
    germ_mulMono _ _ _ _ _ _ _ _ _ _ hc hk]
  simp only [monoVal_add]
  ring

/- English proof (translation)
Substitute `e` using the available equality. Unfold `mono`. Use `tw_ext (isLB_tens G.K.isLB G.isLBA) G.isLB fun c k y hy hc hk => ?_` and prove the remaining obligations. Rewrite using `[germ_mulMono _ _ _ _ _ _ _ _ _ _ hc hk]`. Simplify using `only [monoVal_zero, one_mul]`.
-/
theorem mono_zero (α : Fin G.D →₀ ℕ) (e : α = 0) {j : ℕ} (h : j + α.degree = j) (m : G.Sec j) :
    mono G s α h m = m := by
  subst e
  unfold mono
  refine tw_ext (isLB_tens G.K.isLB G.isLBA) G.isLB fun c k y hy hc hk => ?_
  rw [germ_mulMono _ _ _ _ _ _ _ _ _ _ hc hk]
  simp only [monoVal_zero, one_mul]

/- English proof (translation)
Rewrite using `[G.mulW_apply]`. Unfold `mono`. Use `tw_ext (isLB_tens G.K.isLB G.isLBA) G.isLB fun c k y hy hc hk => ?_` and prove the remaining obligations. Rewrite using `[germ_mulMono _ _ _ _ _ _ _ _ _ _ hc hk, germ_mulSec _ _ _ _ _ _ _ _ _ hc hk]`. Simplify using `only [monoVal_single, pow_one]`.
-/
theorem mono_single (i : Fin G.D) {j : ℕ} (h : j + (Finsupp.single i 1).degree = j + 1) (m : G.Sec j) :
    mono G s (Finsupp.single i 1) h m = G.mulW j (s i) m := by
  rw [G.mulW_apply]
  unfold mono
  refine tw_ext (isLB_tens G.K.isLB G.isLBA) G.isLB fun c k y hy hc hk => ?_
  rw [germ_mulMono _ _ _ _ _ _ _ _ _ _ hc hk, germ_mulSec _ _ _ _ _ _ _ _ _ hc hk]
  simp only [monoVal_single, pow_one]

def Acts (E : Module.End F (Tot G)) (α : Fin G.D →₀ ℕ) : Prop :=
  ∀ (j l : ℕ) (h : j + α.degree = l) (m : G.Sec j), E (Pi.single j m) = Pi.single l (mono G s α h m)

/- English proof (translation)
Introduce `j l h m` and use `by obtain rfl : j = l := by simpa using h rw [mono_zero G s 0 rfl h m]; rfl`.
-/
theorem acts_one : Acts G s 1 0 := fun j l h m => by
  obtain rfl : j = l := by simpa using h
  rw [mono_zero G s 0 rfl h m]; rfl

/- English proof (translation)
Introduce `j l h m` and use `by have h' : j + α₂.degree + α₁.degree = l := by rw [map_add] at h; omega rw [Module.End.mul_apply, h₂ j (j + α₂.degree) rfl m, h₁ (j + α₂.degree) l h', ← mono_add G s α₁ α₂ (α₁ + α₂) rfl]`.
-/
theorem acts_mul {E₁ E₂ : Module.End F (Tot G)} {α₁ α₂ : Fin G.D →₀ ℕ} (h₁ : Acts G s E₁ α₁) (h₂ : Acts G s E₂ α₂) :
    Acts G s (E₁ * E₂) (α₁ + α₂) := fun j l h m => by
  have h' : j + α₂.degree + α₁.degree = l := by rw [map_add] at h; omega
  rw [Module.End.mul_apply, h₂ j (j + α₂.degree) rfl m, h₁ (j + α₂.degree) l h',
    ← mono_add G s α₁ α₂ (α₁ + α₂) rfl]

/- English proof (translation)
Introduce `j l h m` and use `by obtain rfl : l = j + 1 := by simpa using h.symm rw [shift_single, mono_single]`.
-/
theorem acts_shift (i : Fin G.D) : Acts G s (shift G (s i)) (Finsupp.single i 1) := fun j l h m => by
  obtain rfl : l = j + 1 := by simpa using h.symm
  rw [shift_single, mono_single]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simpa using acts_one G s`. Consider the case `succ k ih`. Rewrite using `[pow_succ, show Finsupp.single i (k + 1) = Finsupp.single i k + Finsupp.single i 1 by simp]`. Conclude with `acts_mul G s ih (acts_shift G s i)`.
-/
theorem acts_pow (i : Fin G.D) (k : ℕ) : Acts G s (shift G (s i) ^ k) (Finsupp.single i k) := by
  induction k with
  | zero => simpa using acts_one G s
  | succ k ih =>
    rw [pow_succ, show Finsupp.single i (k + 1) = Finsupp.single i k + Finsupp.single i 1 by simp]
    exact acts_mul G s ih (acts_shift G s i)

/- English proof (translation)
The claim follows from `| 0, E, g, _ => by simpa using acts_one G s | n + 1, E, g, hE => by rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ] exact acts_mul G s (hE 0) (acts_list n _ _ fun i => hE i.succ)`.
-/
theorem acts_list : ∀ (n : ℕ) (E : Fin n → Module.End F (Tot G)) (g : Fin n → Fin G.D →₀ ℕ),
    (∀ i, Acts G s (E i) (g i)) → Acts G s (List.ofFn E).prod (∑ i, g i)
  | 0, E, g, _ => by simpa using acts_one G s
  | n + 1, E, g, hE => by
    rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ]
    exact acts_mul G s (hE 0) (acts_list n _ _ fun i => hE i.succ)

/- English proof (translation)
Use `acts_list G s G.D (fun i => shift G (s i) ^ α i) (fun i => Finsupp.single i (α i)) fun i => acts_pow G s i (α i)` as an intermediate fact. Rewrite `this` using `[Finsupp.univ_sum_single]`. Then use the resulting hypothesis.
-/
theorem acts_pw (α : Fin G.D →₀ ℕ) : Acts G s (HSShort.pw (shift G) s α) α := by
  have := acts_list G s G.D (fun i => shift G (s i) ^ α i) (fun i => Finsupp.single i (α i))
    fun i => acts_pow G s i (α i)
  rwa [Finsupp.univ_sum_single] at this

end GlobalTheory.HSShort.ShiftMono

namespace GlobalTheory.HSShort

/- English proof (translation)
Introduce `F _ _ G`. Use `⟨ShiftMono.shift_comm G, ShiftMono.shift_single G, fun s a j l h α m => ?_⟩` and prove the remaining obligations. Take `⟨α, rfl⟩` from `α`. Conclude with `ShiftMono.acts_pw G s α j l h m`.
-/
theorem shift_comm_single_mono : ∀ (F : Type) [Field F] [NumberField F] (G : Geo F),
    (∀ u v, shift G u * shift G v = shift G v * shift G u) ∧ (∀ (j : ℕ) u (m : G.Sec j), shift G u (Pi.single j m) = Pi.single (j + 1) (G.mulW j u m)) ∧ ∀ (s : Fin G.D → Fin G.N → F) (a j l : ℕ) (h : j + a = l) (α : MonoDeg (Fin G.D) a) (m : G.Sec j), pw (shift G) s α.1 (Pi.single j m) = Pi.single l (mulPow G s h α m) := by
  intro F _ _ G
  refine ⟨ShiftMono.shift_comm G, ShiftMono.shift_single G, fun s a j l h α m => ?_⟩
  obtain ⟨α, rfl⟩ := α
  exact ShiftMono.acts_pw G s α j l h m

end GlobalTheory.HSShort
