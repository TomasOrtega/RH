import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.CarrierRow
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.SkewSolve
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RelativeEquivalence.DCRelEquivAllHolds

noncomputable section

open scoped Classical

namespace PI.TermsAtPtFiniteW

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef

section Int

variable {E : Type} [Field E] [NumberField E]

def IntE (x : E) : Prop := ∃ o : 𝓞 E, (o : E) = x

/- English proof (translation)
Take `⟨a, rfl⟩` from `hx`. Take `⟨b, rfl⟩` from `hy`. Conclude with `⟨a + b, map_add (algebraMap (𝓞 E) E) a b⟩`.
-/
theorem IntE.add {x y : E} (hx : IntE x) (hy : IntE y) : IntE (x + y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a + b, map_add (algebraMap (𝓞 E) E) a b⟩
/- English proof (translation)
Take `⟨a, rfl⟩` from `hx`. Take `⟨b, rfl⟩` from `hy`. Conclude with `⟨a * b, map_mul (algebraMap (𝓞 E) E) a b⟩`.
-/
theorem IntE.mul {x y : E} (hx : IntE x) (hy : IntE y) : IntE (x * y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a * b, map_mul (algebraMap (𝓞 E) E) a b⟩
/- English proof (translation)
Take `⟨a, rfl⟩` from `hx`. Conclude with `⟨-a, map_neg (algebraMap (𝓞 E) E) a⟩`.
-/
theorem IntE.neg {x : E} (hx : IntE x) : IntE (-x) := by
  obtain ⟨a, rfl⟩ := hx
  exact ⟨-a, map_neg (algebraMap (𝓞 E) E) a⟩
/- English proof (translation)
Take `⟨a, rfl⟩` from `hx`. Take `⟨b, rfl⟩` from `hy`. Conclude with `⟨a - b, map_sub (algebraMap (𝓞 E) E) a b⟩`.
-/
theorem IntE.sub {x y : E} (hx : IntE x) (hy : IntE y) : IntE (x - y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a - b, map_sub (algebraMap (𝓞 E) E) a b⟩
/- English proof (translation)
Assemble the required witnesses or components as `⟨n, map_natCast (algebraMap (𝓞 E) E) n⟩`.
-/
theorem IntE.nat (n : ℕ) : IntE (n : E) := ⟨n, map_natCast (algebraMap (𝓞 E) E) n⟩
/- English proof (translation)
Assemble the required witnesses or components as `⟨0, map_zero (algebraMap (𝓞 E) E)⟩`.
-/
theorem IntE.zero : IntE (0 : E) := ⟨0, map_zero (algebraMap (𝓞 E) E)⟩
/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Rewrite using `[Finset.sum_empty]`. Conclude with `IntE.zero`. Consider the case `@insert a s ha ih`.

Rewrite using `[Finset.sum_insert ha]`. Conclude with `IntE.add (h a (Finset.mem_insert_self a s)) (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))`.
-/
theorem IntE.sum {ι : Type*} (s : Finset ι) (g : ι → E) (h : ∀ i ∈ s, IntE (g i)) : IntE (∑ i ∈ s, g i) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    exact IntE.zero
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact IntE.add (h a (Finset.mem_insert_self a s)) (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

end Int

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

def piL (e f : Fin r → S.V) : S.V →ₗ[E] S.V := LinearMap.id - ∑ c, (S.hT (f c)).smulRight (e c)

/- English proof (translation)
Simplify using `[piL, LinearMap.smulRight_apply]`.
-/
theorem piL_apply (e f : Fin r → S.V) (x : S.V) : piL e f x = x - ∑ c, S.hT (f c) x • e c := by
  simp [piL, LinearMap.smulRight_apply]

/- English proof (translation)
Conclude with `S.herm.eq x y`.
-/
theorem herm_star (x y : S.V) : star (S.hT x y) = S.hT y x := by
  exact S.herm.eq x y

/- English proof (translation)
Use `set e := F.fl.e with he_def`. Establish `hee : ∀ a b, S.hT (e a) (e b) = 0` using `F.fl.e_iso`. Establish `hfe : ∀ a b, S.hT (f a) (e b) = if a = b then 1 else 0` using `fun a b => by`. Rewrite using `[← herm_star, hef b a]`. Distinguish the cases in `h : b = a`.

Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h, Ne.symm h]`. Establish `hpi_e : ∀ a x, S.hT (e a) (piL e f x) = S.hT (e a) x` using `fun a x => by`. Simplify using `[piL_apply, map_sub, map_sum, hee]`.

Establish `hpi_f : ∀ a x, S.hT (f a) (piL e f x) = 0` using `fun a x => by`. Simplify using `[piL_apply, map_sub, map_sum, hfe]`. Establish `hmemE : ∀ (x : E) (w : S.V), IntE x → w ∈ Λ → x • w ∈ Λ`. Introduce and unpack `x w ⟨o, rfl⟩ hw`. Use `show (algebraMap (𝓞 E) E o) • w ∈ Λ`.

Rewrite using `[algebraMap_smul]`. Conclude with `Λ.smul_mem o hw`. Establish `hnat : ∀ (k : ℕ) (w : S.V), w ∈ Λ → (k : E) • w ∈ Λ` using `fun k w hw => hmemE _ w (IntE.nat k) hw`. Use `choose lam hlam hδeq using hδ`. Set `P : Fin (r + 1) → S.V` to `fun b => (nd : E) • piL e f (lam b)`.

Establish `hP : ∀ b, P b ∈ Λ`. Introduce `b`. Establish `: P b = (nd : E) • lam b - ∑ c, ((nd : E) * S.hT (f c) (lam b)) • e c`. Simplify using `only [P, piL_apply, smul_sub, Finset.smul_sum, smul_smul]`. Rewrite using `[this]`.

Use `Λ.sub_mem (hnat nd _ (hlam b)) (Λ.sum_mem fun c _ => hmemE _ _ (hfint _ (hlam b) c) (he c))` and prove the remaining obligations. Set `δ : Fin (r + 1) → S.V` to `fun b => frame y2 b - frame y1 b`. Set `ρ : Fin (r + 1) → S.V` to `fun b => piL e f (δ b)`. Establish `hδe : ∀ c b, S.hT (e c) (δ b) = 0` using `fun c b => by simp [δ, map_sub, hβ1, hβ2]`. Establish `hρe : ∀ c b, S.hT (e c) (ρ b) = 0` using `fun c b => by simp only [ρ, hpi_e, hδe]`.

Establish `hρsum : ∑ b, v b • ρ b = 0`. Establish `: ∑ b, v b • ρ b = piL e f (∑ b, v b • frame y2 b) - piL e f (∑ b, v b • frame y1 b)`. Simplify using `only [ρ, δ, map_sum, map_smul, map_sub, smul_sub, Finset.sum_sub_distrib]`. Rewrite using `[this, ← hι, sub_self]`. Take `⟨qo, hqo⟩ : ∃ qo : Fin (r + 1) → Fin r → 𝓞 E, ∀ b c, (qo b c : E) = (nQ : E) * Q b c` from `⟨fun b c => (hQint b c).choose, fun b c => (hQint b c).choose_spec⟩`.

Set `a' : Fin r → S.V` to `fun c => ∑ b, (qo b c : E) • P b`. Set `a : Fin r → S.V` to `fun c => ∑ b, Q b c • ρ b`. Establish `ha' : ∀ c, a' c ∈ Λ` using `fun c => Λ.sum_mem fun b _ => hmemE _ _ ⟨qo b c, rfl⟩ (hP b)`. Establish `haa' : ∀ c, a c = ((nd * nQ : ℕ) : E) • a' c`. Introduce `c`.

Simplify using `only [a, a', ρ, P, Finset.smul_sum, smul_smul]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[show δ b = (((nd * nQ) ^ 2 : ℕ) : E) • lam b from hδeq b, map_smul, smul_smul, hqo]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `ha : ∀ c, a c ∈ Λ` using `fun c => by rw [haa']; exact hnat _ _ (ha' c)`. Establish `hea : ∀ c d, S.hT (e c) (a d) = 0` using `fun c d => by simp [a, map_sum, hρe]`. Set `s : Matrix (Fin r) (Fin r) E` to `fun c d => if c < d then -S.hT (a c) (a d) else if c = d then -((θ : E) * S.hT (a c) (a c)) else 0`. Establish `hs : ∀ c d, s c d + star (s d c) = -S.hT (a c) (a d)`.

Introduce `c d`. Break down `lt_trichotomy c d with h | h | h` into its components or cases. Simplify using `[s, h, not_lt.2 h.le, h.ne']`. Substitute `h` using the available equality. Establish `hh : star (S.hT (a c) (a c)) = S.hT (a c) (a c)` using `herm_star _ _`.

Simplify using `only [s, lt_irrefl, if_false, if_true, star_neg, star_mul', hh]`. Take the linear combination `(-(S.hT (a c) (a c))) * hθ`. Simplify using `[s, h, not_lt.2 h.le, h.ne, h.ne', herm_star]`. Establish `haa : ∀ c d, S.hT (a c) (a d) = (((nd * nQ) ^ 2 : ℕ) : E) * S.hT (a' c) (a' d)`. Introduce `c d`.

Rewrite using `[haa', haa', map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply]`. Simplify using `only [starRingEnd_apply, star_natCast, smul_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Set `s' : Matrix (Fin r) (Fin r) E` to `fun c d => if c < d then -S.hT (a' c) (a' d) else if c = d then -((θ : E) * S.hT (a' c) (a' c)) else 0`.

Establish `hss' : ∀ c d, s c d = (((nd * nQ) ^ 2 : ℕ) : E) * s' c d`. Introduce `c d`. Simplify using `only [s, s', haa]`. Apply the tactic sequence `split_ifs <;> ring`. Establish `hs'int : ∀ c d, IntE (s' c d)`.

Introduce `c d`. Simplify using `only [s']`. Use `split_ifs`. Conclude with `(IntE.neg (hint _ (ha' c) _ (ha' d)))`. Conclude with `IntE.neg (IntE.mul (show IntE (θ : E) from ⟨θ, rfl⟩) (hint _ (ha' c) _ (ha' c)))`.

Conclude with `IntE.zero`. Establish `hsint : ∀ c d, ∃ o : 𝓞 E, (o : E) = s c d` using `fun c d => by`. Rewrite using `[hss']`. Conclude with `(IntE.nat _).mul (hs'int c d)`. Take `⟨n1, hn1, hn1act⟩` from `hH E S r T Λ F a s hint he ha hea hsint hs`.

Simplify using `only [← he_def] at hn1act`. Establish `hiso1 : ∀ x y, S.hT (n1 x) (n1 y) = S.hT x y` using `hn1.1.1`. Establish `hn1e : ∀ c, n1 (e c) = e c`. Introduce `c`. Rewrite using `[hn1act, heisFun]`.

Establish `: ∀ c', S.hT (a c') (e c) = 0` using `fun c' => by rw [← herm_star, hea]; simp`. Simplify using `[hee, this]`. Establish `hrow : ∀ c b, S.hT (e c) (n1 (frame y1 b)) = β c b` using `fun c b => by`. Rewrite using `[← hn1e c, hiso1, hβ1]`. Establish `hsum_a : ∀ b, ∑ c, S.hT (e c) (frame y1 b) • a c = ρ b`.

Introduce `b`. Simplify using `only [a, hβ1, Finset.smul_sum, smul_smul]`. Rewrite using `[Finset.sum_comm]`. Establish `: ∀ d, ∑ c, (β c b * Q d c) • ρ d = ((Q * β) d b) • ρ d` using `fun d => by`. Rewrite using `[← Finset.sum_smul, Matrix.mul_apply]`.

Use `congr 1`. Conclude with `Finset.sum_congr rfl fun c _ => mul_comm _ _`. Simplify using `only [this, hQβ, sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Establish `h2 : ∑ d, (v d * l b) • ρ d = l b • ∑ d, v d • ρ d`. Rewrite using `[Finset.smul_sum]`.

Conclude with `Finset.sum_congr rfl fun d _ => by rw [smul_smul, mul_comm]`. Rewrite using `[h2, hρsum, smul_zero, sub_zero]`. Set `x' : Matrix (Fin r) (Fin (r + 1)) E` to `fun c b => S.hT (f c) (δ b) + S.hT (a c) (frame y1 b) - ∑ d, s c d * β d b`. Establish `hk : ∀ b, frame y2 b = n1 (frame y1 b) + ∑ c, x' c b • e c`. Introduce `b`.

Establish `hy2 : frame y2 b = frame y1 b + ρ b + ∑ c, S.hT (f c) (δ b) • e c`. Simplify using `only [ρ, piL_apply, δ]`. Normalize the expressions using the abelian group laws. Rewrite using `[hn1act, heisFun, hsum_a, hy2]`. Simplify using `only [x', add_smul, sub_smul, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_smul, hβ1]`.

Normalize the expressions using the abelian group laws. Establish `hcol : ∀ d a0, S.hT (n1 (frame y1 a0)) (e d) = star (β d a0)` using `fun d a0 => by`. Rewrite using `[← herm_star, hrow]`. Establish `hid : ∀ a0 b, ∑ c, (star (β c a0) * x' c b + star (x' c a0) * β c b) = 0`. Introduce `a0 b`.

Establish `h` using `hgram a0 b`. Rewrite `h` using `[hk a0, hk b, ← hiso1 (frame y1 a0) (frame y1 b)]`. Simplify using `only [map_add, LinearMap.add_apply, map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hee, mul_zero, Finset.sum_const_zero, add_zero, hrow, hcol, starRingEnd_apply] at h`. Rewrite using `[Finset.sum_add_distrib]`. Establish `e1 : ∑ c, star (β c a0) * x' c b = ∑ c, x' c b * star (β c a0)` using `Finset.sum_congr rfl fun _ _ => mul_comm _ _`.

Rewrite using `[e1]`. Take the linear combination `h`. Take `⟨hskew, hfact⟩` from `hSk E r β x' Q v l hind hβQ hv hQβ hid`. Establish `hfd : ∀ c b, S.hT (f c) (δ b) = (((nd * nQ) ^ 2 : ℕ) : E) * S.hT (f c) (lam b)` using `fun c b => by show S.hT (f c) (frame y2 b - frame y1 b) = _`. Rewrite using `[hδeq b, map_smul, smul_eq_mul]`.

Establish `hac : ∀ c b, S.hT (a c) (frame y1 b) = ((nd * nQ : ℕ) : E) * S.hT (a' c) (frame y1 b)` using `fun c b => by`. Rewrite using `[haa', LinearMap.map_smulₛₗ, LinearMap.smul_apply, starRingEnd_apply, star_natCast, smul_eq_mul]`. Set `w : Matrix (Fin r) (Fin (r + 1)) E` to `fun c b => ((nd * nQ : ℕ) : E) * ((nd : E) * S.hT (f c) (lam b)) + (nd : E) * S.hT (a' c) (frame y1 b) - ∑ d, ((nd ^ 2 * nQ : ℕ) : E) * s' c d * β d b`. Establish `hw : ∀ c b, IntE (w c b)`. Introduce `c b`.

Use `((IntE.nat _).mul (hfint _ (hlam b) c)).add ((IntE.nat _).mul (hint _ (ha' c) _ (hy1 b))) |>.sub (IntE.sum _ _ fun d _ => ((IntE.nat _).mul (hs'int c d)).mul ?_)` and prove the remaining obligations. Rewrite using `[← hβ1]`. Conclude with `hint _ (he d) _ (hy1 b)`. Establish `hxw : ∀ c b, x' c b = (nQ : E) * w c b`. Introduce `c b`.

Simplify using `only [x', w, hfd, hac, hss']`. Establish `hsum : ∑ x, (((nd * nQ) ^ 2 : ℕ) : E) * s' c x * β x b = (nQ : E) * ∑ d, ((nd ^ 2 * nQ : ℕ) : E) * s' c d * β d b`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hsum]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hSint : ∀ c d, ∃ o : 𝓞 E, (o : E) = (x' * Q) c d`.

Introduce `c d`. Establish `: (x' * Q) c d = ∑ b, w c b * ((nQ : E) * Q b d)`. Rewrite using `[Matrix.mul_apply]`. Conclude with `Finset.sum_congr rfl fun b _ => by rw [hxw]; ring`. Rewrite using `[this]`.

Conclude with `IntE.sum _ _ fun b _ => (hw c b).mul (hQint b d)`. Take `⟨n2, hn2, hn2act⟩` from `hH E S r T Λ F 0 (x' * Q) hint he (fun _ => Λ.zero_mem) (by simp) hSint (by intro c d; simp [hskew c d])`. Simplify using `only [← he_def] at hn2act`. Establish `hfin2 : ∀ b, n2 (n1 (frame y1 b)) = frame y2 b`. Introduce `b`.

Rewrite using `[hn2act, heisFun, hk b]`. Simplify using `only [Pi.zero_apply, smul_zero, Finset.sum_const_zero, map_zero, LinearMap.zero_apply, zero_smul, add_zero, sub_zero, hrow]`. Use `congr 1`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_smul]`.

Use `congr 1`. Use `conv_rhs => rw [hfact]`. Rewrite using `[Matrix.mul_apply]`. Use `⟨n2 * n1, PI.DCRelEquiv.UnitaryGroupMassFormula.nlam_mul hn2 hn1, 1, one_mem_NLam Λ y1, fun b => ?_, ?_⟩` and prove the remaining obligations. Simplify using `[hfin2]`.

Rewrite using `[hzt2, hzt1]`. Simplify using `[hfin2]`.
-/
theorem related_gen (hH : HeisOp) (hSk : SkewSolve) {T T' : E} (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T)
    (f : Fin r → S.V)
    (hint : ∀ x ∈ Λ, ∀ y ∈ Λ, ∃ o : 𝓞 E, (o : E) = S.hT x y)
    (he : ∀ c, F.fl.e c ∈ Λ)
    (hef : ∀ a b, S.hT (F.fl.e a) (f b) = if a = b then 1 else 0)
    (θ : 𝓞 E) (hθ : (θ : E) + star (θ : E) = 1)
    (nd nQ : ℕ) (hfint : ∀ x ∈ Λ, ∀ c, IntE ((nd : E) * S.hT (f c) x))
    (β : Matrix (Fin r) (Fin (r + 1)) E) (Q : Matrix (Fin (r + 1)) (Fin r) E) (v l : Fin (r + 1) → E)
    (hind : ∀ u : Fin r → E, (∀ b, ∑ c, u c * β c b = 0) → u = 0)
    (hβQ : β * Q = 1) (hv : ∀ c, ∑ b, β c b * v b = 0)
    (hQβ : ∀ i j, (Q * β) i j = (if i = j then 1 else 0) - v i * l j)
    (hQint : ∀ b c, IntE ((nQ : E) * Q b c))
    (y1 y2 : LFlag S r T')
    (hzt1 : y1.zt = frame y1 (Fin.last r)) (hzt2 : y2.zt = frame y2 (Fin.last r))
    (hy1 : ∀ b, frame y1 b ∈ Λ)
    (hβ1 : ∀ c b, S.hT (F.fl.e c) (frame y1 b) = β c b) (hβ2 : ∀ c b, S.hT (F.fl.e c) (frame y2 b) = β c b)
    (hgram : ∀ a b, S.hT (frame y2 a) (frame y2 b) = S.hT (frame y1 a) (frame y1 b))
    (hδ : ∀ b, ∃ lam ∈ Λ, frame y2 b - frame y1 b = (((nd * nQ) ^ 2 : ℕ) : E) • lam)
    (hι : piL F.fl.e f (∑ b, v b • frame y1 b) = piL F.fl.e f (∑ b, v b • frame y2 b)) :
    DCRel Λ F y1 y2 := by
  set e := F.fl.e with he_def
  have hee : ∀ a b, S.hT (e a) (e b) = 0 := F.fl.e_iso
  have hfe : ∀ a b, S.hT (f a) (e b) = if a = b then 1 else 0 := fun a b => by
    rw [← herm_star, hef b a]
    by_cases h : b = a
    · subst h; simp
    · simp [h, Ne.symm h]
  have hpi_e : ∀ a x, S.hT (e a) (piL e f x) = S.hT (e a) x := fun a x => by
    simp [piL_apply, map_sub, map_sum, hee]
  have hpi_f : ∀ a x, S.hT (f a) (piL e f x) = 0 := fun a x => by
    simp [piL_apply, map_sub, map_sum, hfe]
  have hmemE : ∀ (x : E) (w : S.V), IntE x → w ∈ Λ → x • w ∈ Λ := by
    rintro x w ⟨o, rfl⟩ hw
    show (algebraMap (𝓞 E) E o) • w ∈ Λ
    rw [algebraMap_smul]
    exact Λ.smul_mem o hw
  have hnat : ∀ (k : ℕ) (w : S.V), w ∈ Λ → (k : E) • w ∈ Λ := fun k w hw => hmemE _ w (IntE.nat k) hw
  choose lam hlam hδeq using hδ

  let P : Fin (r + 1) → S.V := fun b => (nd : E) • piL e f (lam b)
  have hP : ∀ b, P b ∈ Λ := by
    intro b
    have : P b = (nd : E) • lam b - ∑ c, ((nd : E) * S.hT (f c) (lam b)) • e c := by
      simp only [P, piL_apply, smul_sub, Finset.smul_sum, smul_smul]
    rw [this]
    refine Λ.sub_mem (hnat nd _ (hlam b)) (Λ.sum_mem fun c _ => hmemE _ _ (hfint _ (hlam b) c) (he c))
  let δ : Fin (r + 1) → S.V := fun b => frame y2 b - frame y1 b
  let ρ : Fin (r + 1) → S.V := fun b => piL e f (δ b)
  have hδe : ∀ c b, S.hT (e c) (δ b) = 0 := fun c b => by simp [δ, map_sub, hβ1, hβ2]
  have hρe : ∀ c b, S.hT (e c) (ρ b) = 0 := fun c b => by simp only [ρ, hpi_e, hδe]
  have hρsum : ∑ b, v b • ρ b = 0 := by
    have : ∑ b, v b • ρ b = piL e f (∑ b, v b • frame y2 b) - piL e f (∑ b, v b • frame y1 b) := by
      simp only [ρ, δ, map_sum, map_smul, map_sub, smul_sub, Finset.sum_sub_distrib]
    rw [this, ← hι, sub_self]
  obtain ⟨qo, hqo⟩ : ∃ qo : Fin (r + 1) → Fin r → 𝓞 E, ∀ b c, (qo b c : E) = (nQ : E) * Q b c :=
    ⟨fun b c => (hQint b c).choose, fun b c => (hQint b c).choose_spec⟩
  let a' : Fin r → S.V := fun c => ∑ b, (qo b c : E) • P b
  let a : Fin r → S.V := fun c => ∑ b, Q b c • ρ b
  have ha' : ∀ c, a' c ∈ Λ := fun c => Λ.sum_mem fun b _ => hmemE _ _ ⟨qo b c, rfl⟩ (hP b)
  have haa' : ∀ c, a c = ((nd * nQ : ℕ) : E) • a' c := by
    intro c
    simp only [a, a', ρ, P, Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [show δ b = (((nd * nQ) ^ 2 : ℕ) : E) • lam b from hδeq b, map_smul, smul_smul, hqo]
    congr 1
    push_cast
    ring
  have ha : ∀ c, a c ∈ Λ := fun c => by rw [haa']; exact hnat _ _ (ha' c)
  have hea : ∀ c d, S.hT (e c) (a d) = 0 := fun c d => by simp [a, map_sum, hρe]

  let s : Matrix (Fin r) (Fin r) E := fun c d =>
    if c < d then -S.hT (a c) (a d) else if c = d then -((θ : E) * S.hT (a c) (a c)) else 0
  have hs : ∀ c d, s c d + star (s d c) = -S.hT (a c) (a d) := by
    intro c d
    rcases lt_trichotomy c d with h | h | h
    · simp [s, h, not_lt.2 h.le, h.ne']
    · subst h
      have hh : star (S.hT (a c) (a c)) = S.hT (a c) (a c) := herm_star _ _
      simp only [s, lt_irrefl, if_false, if_true, star_neg, star_mul', hh]
      linear_combination (-(S.hT (a c) (a c))) * hθ
    · simp [s, h, not_lt.2 h.le, h.ne, h.ne', herm_star]
  have haa : ∀ c d, S.hT (a c) (a d) = (((nd * nQ) ^ 2 : ℕ) : E) * S.hT (a' c) (a' d) := by
    intro c d
    rw [haa', haa', map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply]
    simp only [starRingEnd_apply, star_natCast, smul_eq_mul]
    push_cast
    ring
  let s' : Matrix (Fin r) (Fin r) E := fun c d =>
    if c < d then -S.hT (a' c) (a' d) else if c = d then -((θ : E) * S.hT (a' c) (a' c)) else 0
  have hss' : ∀ c d, s c d = (((nd * nQ) ^ 2 : ℕ) : E) * s' c d := by
    intro c d
    simp only [s, s', haa]
    split_ifs <;> ring
  have hs'int : ∀ c d, IntE (s' c d) := by
    intro c d
    simp only [s']
    split_ifs
    · exact (IntE.neg (hint _ (ha' c) _ (ha' d)))
    · exact IntE.neg (IntE.mul (show IntE (θ : E) from ⟨θ, rfl⟩) (hint _ (ha' c) _ (ha' c)))
    · exact IntE.zero
  have hsint : ∀ c d, ∃ o : 𝓞 E, (o : E) = s c d := fun c d => by
    rw [hss']; exact (IntE.nat _).mul (hs'int c d)
  obtain ⟨n1, hn1, hn1act⟩ := hH E S r T Λ F a s hint he ha hea hsint hs
  simp only [← he_def] at hn1act
  have hiso1 : ∀ x y, S.hT (n1 x) (n1 y) = S.hT x y := hn1.1.1
  have hn1e : ∀ c, n1 (e c) = e c := by
    intro c
    rw [hn1act, heisFun]
    have : ∀ c', S.hT (a c') (e c) = 0 := fun c' => by rw [← herm_star, hea]; simp
    simp [hee, this]
  have hrow : ∀ c b, S.hT (e c) (n1 (frame y1 b)) = β c b := fun c b => by
    rw [← hn1e c, hiso1, hβ1]

  have hsum_a : ∀ b, ∑ c, S.hT (e c) (frame y1 b) • a c = ρ b := by
    intro b
    simp only [a, hβ1, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    have : ∀ d, ∑ c, (β c b * Q d c) • ρ d = ((Q * β) d b) • ρ d := fun d => by
      rw [← Finset.sum_smul, Matrix.mul_apply]
      congr 1
      exact Finset.sum_congr rfl fun c _ => mul_comm _ _
    simp only [this, hQβ, sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have h2 : ∑ d, (v d * l b) • ρ d = l b • ∑ d, v d • ρ d := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun d _ => by rw [smul_smul, mul_comm]
    rw [h2, hρsum, smul_zero, sub_zero]
  let x' : Matrix (Fin r) (Fin (r + 1)) E := fun c b =>
    S.hT (f c) (δ b) + S.hT (a c) (frame y1 b) - ∑ d, s c d * β d b
  have hk : ∀ b, frame y2 b = n1 (frame y1 b) + ∑ c, x' c b • e c := by
    intro b
    have hy2 : frame y2 b = frame y1 b + ρ b + ∑ c, S.hT (f c) (δ b) • e c := by
      simp only [ρ, piL_apply, δ]
      abel
    rw [hn1act, heisFun, hsum_a, hy2]
    simp only [x', add_smul, sub_smul, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_smul, hβ1]
    abel

  have hcol : ∀ d a0, S.hT (n1 (frame y1 a0)) (e d) = star (β d a0) := fun d a0 => by
    rw [← herm_star, hrow]
  have hid : ∀ a0 b, ∑ c, (star (β c a0) * x' c b + star (x' c a0) * β c b) = 0 := by
    intro a0 b
    have h := hgram a0 b
    rw [hk a0, hk b, ← hiso1 (frame y1 a0) (frame y1 b)] at h
    simp only [map_add, LinearMap.add_apply, map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ,
      LinearMap.smul_apply, smul_eq_mul, hee, mul_zero, Finset.sum_const_zero, add_zero, hrow, hcol,
      starRingEnd_apply] at h
    rw [Finset.sum_add_distrib]
    have e1 : ∑ c, star (β c a0) * x' c b = ∑ c, x' c b * star (β c a0) :=
      Finset.sum_congr rfl fun _ _ => mul_comm _ _
    rw [e1]
    linear_combination h
  obtain ⟨hskew, hfact⟩ := hSk E r β x' Q v l hind hβQ hv hQβ hid

  have hfd : ∀ c b, S.hT (f c) (δ b) = (((nd * nQ) ^ 2 : ℕ) : E) * S.hT (f c) (lam b) := fun c b => by
    show S.hT (f c) (frame y2 b - frame y1 b) = _
    rw [hδeq b, map_smul, smul_eq_mul]
  have hac : ∀ c b, S.hT (a c) (frame y1 b) = ((nd * nQ : ℕ) : E) * S.hT (a' c) (frame y1 b) := fun c b => by
    rw [haa', LinearMap.map_smulₛₗ, LinearMap.smul_apply, starRingEnd_apply, star_natCast, smul_eq_mul]
  let w : Matrix (Fin r) (Fin (r + 1)) E := fun c b =>
    ((nd * nQ : ℕ) : E) * ((nd : E) * S.hT (f c) (lam b)) + (nd : E) * S.hT (a' c) (frame y1 b) -
      ∑ d, ((nd ^ 2 * nQ : ℕ) : E) * s' c d * β d b
  have hw : ∀ c b, IntE (w c b) := by
    intro c b
    refine ((IntE.nat _).mul (hfint _ (hlam b) c)).add ((IntE.nat _).mul (hint _ (ha' c) _ (hy1 b))) |>.sub
      (IntE.sum _ _ fun d _ => ((IntE.nat _).mul (hs'int c d)).mul ?_)
    rw [← hβ1]
    exact hint _ (he d) _ (hy1 b)
  have hxw : ∀ c b, x' c b = (nQ : E) * w c b := by
    intro c b
    simp only [x', w, hfd, hac, hss']
    have hsum : ∑ x, (((nd * nQ) ^ 2 : ℕ) : E) * s' c x * β x b =
        (nQ : E) * ∑ d, ((nd ^ 2 * nQ : ℕ) : E) * s' c d * β d b := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun d _ => ?_
      push_cast
      ring
    rw [hsum]
    push_cast
    ring
  have hSint : ∀ c d, ∃ o : 𝓞 E, (o : E) = (x' * Q) c d := by
    intro c d
    have : (x' * Q) c d = ∑ b, w c b * ((nQ : E) * Q b d) := by
      rw [Matrix.mul_apply]
      exact Finset.sum_congr rfl fun b _ => by rw [hxw]; ring
    rw [this]
    exact IntE.sum _ _ fun b _ => (hw c b).mul (hQint b d)
  obtain ⟨n2, hn2, hn2act⟩ := hH E S r T Λ F 0 (x' * Q) hint he (fun _ => Λ.zero_mem) (by simp) hSint
    (by intro c d; simp [hskew c d])
  simp only [← he_def] at hn2act
  have hfin2 : ∀ b, n2 (n1 (frame y1 b)) = frame y2 b := by
    intro b
    rw [hn2act, heisFun, hk b]
    simp only [Pi.zero_apply, smul_zero, Finset.sum_const_zero, map_zero, LinearMap.zero_apply, zero_smul,
      add_zero, sub_zero, hrow]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.sum_smul]
    congr 1
    conv_rhs => rw [hfact]
    rw [Matrix.mul_apply]
  refine ⟨n2 * n1, PI.DCRelEquiv.UnitaryGroupMassFormula.nlam_mul hn2 hn1, 1, one_mem_NLam Λ y1, fun b => ?_, ?_⟩
  · simp [hfin2]
  · rw [hzt2, hzt1]
    simp [hfin2]

end Gen

end PI.TermsAtPtFiniteW
