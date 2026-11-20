import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StLineNormalForm
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PIdealClassesFinite
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PLineCoeffsFG
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PLinePairOrbitsFinite
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsCommonMultiple

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module

noncomputable section

namespace LineNormalForm

section Denominators

variable {E : Type*} [Field E] [NumberField E]

omit [NumberField E] in

/- English proof (translation)
Establish `: IsIntegral ℤ (n : E)`. Simplify using `using isIntegral_algebraMap (R := ℤ) (A := E) (x := (n : ℤ))`. Conclude with `this.mul hx`.
-/
theorem isIntegral_natCast_mul {n : ℕ} {x : E} (hx : IsIntegral ℤ x) :
    IsIntegral ℤ ((n : E) * x) := by
  have : IsIntegral ℤ (n : E) := by
    simpa using isIntegral_algebraMap (R := ℤ) (A := E) (x := (n : ℤ))
  exact this.mul hx

omit [NumberField E] in

/- English proof (translation)
Take `⟨k, rfl⟩` from `hab`. Establish `: ((a * k : ℕ) : E) * x = (k : E) * ((a : E) * x)` using `by push_cast; ring`. Rewrite using `[this]`. Conclude with `isIntegral_natCast_mul hx`.
-/
theorem isIntegral_mul_of_dvd {a b : ℕ} {x : E} (hx : IsIntegral ℤ ((a : E) * x)) (hab : a ∣ b) :
    IsIntegral ℤ ((b : E) * x) := by
  obtain ⟨k, rfl⟩ := hab
  have : ((a * k : ℕ) : E) * x = (k : E) * ((a : E) * x) := by push_cast; ring
  rw [this]
  exact isIntegral_natCast_mul hx

/- English proof (translation)
Take `⟨y, hy, hyx⟩` from `exists_integral_multiples ℤ ℚ (L := E) {x}`. Establish `hyx` using `hyx x (Finset.mem_singleton_self x)`. Use `⟨y.natAbs, Int.natAbs_pos.2 hy, ?_⟩` and prove the remaining obligations. Rewrite `hyx` using `[zsmul_eq_mul]`. Establish `hc : ((y.natAbs : ℕ) : E) = ((y.natAbs : ℤ) : E)` using `(Int.cast_natCast _).symm`.

Rewrite using `[hc]`. Break down `Int.natAbs_eq y with h | h` into its components or cases. Rewrite using `[← h]` and apply the resulting hypothesis. Establish `h' : (y.natAbs : ℤ) = -y` using `by omega`. Rewrite using `[h', Int.cast_neg, neg_mul]`.

Conclude with `hyx.neg`.
-/
theorem exists_nat_mul_isIntegral (x : E) : ∃ n : ℕ, 0 < n ∧ IsIntegral ℤ ((n : E) * x) := by
  obtain ⟨y, hy, hyx⟩ := exists_integral_multiples ℤ ℚ (L := E) {x}
  have hyx := hyx x (Finset.mem_singleton_self x)
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy, ?_⟩
  rw [zsmul_eq_mul] at hyx
  have hc : ((y.natAbs : ℕ) : E) = ((y.natAbs : ℤ) : E) := (Int.cast_natCast _).symm
  rw [hc]
  rcases Int.natAbs_eq y with h | h
  · rwa [← h]
  · have h' : (y.natAbs : ℤ) = -y := by omega
    rw [h', Int.cast_neg, neg_mul]
    exact hyx.neg

omit [Field E] [NumberField E] in

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.Qm7.exists_common_multiple s P hP hex`.
-/
theorem exists_common_multiple {ι : Type*} (s : Finset ι) (P : ι → ℕ → Prop)
    (hP : ∀ i a b, P i a → a ∣ b → P i b) (hex : ∀ i ∈ s, ∃ a, 0 < a ∧ P i a) :
    ∃ d, 0 < d ∧ ∀ i ∈ s, P i d :=
  _root_.UpperTheory.Reformulated.B.Qm7.exists_common_multiple s P hP hex

/- English proof (translation)
Take `⟨S, rfl⟩` from `hJ`. Take `⟨d, hd, hS⟩` from `exists_common_multiple S (fun s n => IsIntegral ℤ ((n : E) * s)) (fun _ _ _ h hab => isIntegral_mul_of_dvd h hab) (fun s _ => exists_nat_mul_isIntegral s)`. Use `⟨d, hd, fun j hj => ?_⟩` and prove the remaining obligations. Proceed by induction on `hj using AddSubgroup.closure_induction with`. Consider the case `mem x hx => exact hS x hx`.

Consider the case `zero => rw [mul_zero]`. Conclude with `isIntegral_zero`. Consider the case `add x y _ _ hx hy => rw [mul_add]`. Conclude with `hx.add hy`. Consider the case `neg x _ hx => rw [mul_neg]`.

Conclude with `hx.neg`.
-/
theorem exists_den_of_fg {J : AddSubgroup E} (hJ : J.FG) :
    ∃ d : ℕ, 0 < d ∧ ∀ j ∈ J, IsIntegral ℤ ((d : E) * j) := by
  obtain ⟨S, rfl⟩ := hJ
  obtain ⟨d, hd, hS⟩ := exists_common_multiple S (fun s n => IsIntegral ℤ ((n : E) * s))
    (fun _ _ _ h hab => isIntegral_mul_of_dvd h hab) (fun s _ => exists_nat_mul_isIntegral s)
  refine ⟨d, hd, fun j hj => ?_⟩
  induction hj using AddSubgroup.closure_induction with
  | mem x hx => exact hS x hx
  | zero => rw [mul_zero]; exact isIntegral_zero
  | add x y _ _ hx hy => rw [mul_add]; exact hx.add hy
  | neg x _ hx => rw [mul_neg]; exact hx.neg

variable (E) in

def intMultiples (N : ℕ) : AddSubgroup E :=
  (integralClosure ℤ E).toSubring.toAddSubgroup.comap (AddMonoidHom.mulLeft ((N : E)⁻¹))

omit [NumberField E] in
/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_intMultiples {N : ℕ} {x : E} : x ∈ intMultiples E N ↔ IsIntegral ℤ ((N : E)⁻¹ * x) :=
  Iff.rfl

end Denominators

end LineNormalForm

open LineNormalForm

section NormalForm

variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]

/- English proof (translation)
Introduce `D`. Use `set B := h.toSesq`. Establish `cc : ∀ a : E, conjHom F E (conjHom F E a) = a` using `fun a => conj_conj (F := F) a`. Establish `ci : ∀ a : E, IsIntegral ℤ a → IsIntegral ℤ (conjHom F E a)` using `fun a ha => ha.map (conjHom F E).toIntAlgHom`. Establish `cn : ∀ N : ℕ, conjHom F E (N : E) = N` using `fun N => map_natCast _ N`.

Establish `hsym : ∀ x y, conjHom F E (B x y) = B y x` using `fun x y => h.isSymm.eq x y`. Establish `hsmul : ∀ (a : E) x y, B (a • x) y = conjHom F E a * B x y`. Introduce `a x y`. Rewrite using `[LinearMap.map_smulₛₗ₂, smul_eq_mul]`. Take `⟨T, hT, hTJ⟩` from `IdealClassesFinite.proof E`.

Take `⟨d, hd, hdT⟩` from `exists_common_multiple hT.toFinset (fun J n => J.FG → J ≠ ⊥ → (∀ j ∈ J, IsIntegral ℤ ((n : E) * j)) ∧ ∃ j₀ ∈ J, j₀ ≠ 0 ∧ IsIntegral ℤ ((n : E) * j₀⁻¹)) (fun J a b hJ hab hfg hne => by`. Take `⟨h1, j₀, hj₀, hj₀0, h2⟩` from `hJ hfg hne`. Conclude with `⟨fun j hj => isIntegral_mul_of_dvd (h1 j hj) hab, j₀, hj₀, hj₀0, isIntegral_mul_of_dvd h2 hab⟩)`. Use the proof step `(fun J _ => by`. Distinguish the cases in `hfg : J.FG`.

Distinguish the cases in `hne : J = ⊥`. Conclude with `⟨1, one_pos, fun _ h => absurd hne h⟩`. Take `⟨a, ha, haJ⟩` from `exists_den_of_fg hfg`. Choose the witnesses or unpack the hypotheses as in `⟨j₀, hj₀, hj₀0⟩ : ∃ j₀ ∈ J, j₀ ≠ 0 := by`. Assume the negation of the conclusion as `hc`.

Use `push Not at hc`. Conclude with `hne ((AddSubgroup.eq_bot_iff_forall J).2 hc)`. Take `⟨b, hb, hbj⟩` from `exists_nat_mul_isIntegral j₀⁻¹`. Conclude with `⟨a * b, Nat.mul_pos ha hb, fun _ _ => ⟨fun j hj => isIntegral_mul_of_dvd (haJ j hj) (dvd_mul_right a b), j₀, hj₀, hj₀0, isIntegral_mul_of_dvd hbj (dvd_mul_left b a)⟩⟩`. Conclude with `⟨1, one_pos, fun h _ => absurd h hfg⟩)`.

Use `set m := D.factorial with hm_def`. Establish `hm : 0 < m` using `Nat.factorial_pos D`. Establish `hmd : 0 < m * d` using `Nat.mul_pos hm hd`. Use `set k := 2 * m * d ^ 3 with hk_def`. Establish `hk : 0 < k` using `by positivity`.

Establish `hm0 : (m : E) ≠ 0` using `Nat.cast_ne_zero.2 hm.ne'`. Establish `hd0 : (d : E) ≠ 0` using `Nat.cast_ne_zero.2 hd.ne'`. Establish `hk0 : (k : E) ≠ 0` using `Nat.cast_ne_zero.2 hk.ne'`. Use `⟨{A | intMultiples E (m * d) ≤ A ∧ (∀ x ∈ A, (m * d * d) • x ∈ intMultiples E (m * d)) ∧ A.FG} ×ˢ {A | intMultiples E k ≤ A ∧ (∀ x ∈ A, (k * d) • x ∈ intMultiples E k) ∧ A.FG}, (finite_sandwich _ (by positivity)).prod (finite_sandwich _ (by positivity)), k * d, Nat.mul_pos hk hd, …` and prove the remaining obligations. Introduce `La l hD hl`.

Establish `hLat` using `hD.isLattice`. Establish `hint : ∀ x ∈ La, ∀ y ∈ La, IsIntegral ℤ (B x y)` using `fun x hx y hy => (mem_integralClosure_iff ℤ E).1 (hD.integral x hx y hy)`. Establish `hsm : ∀ {a : E}, IsIntegral ℤ a → ∀ {x}, x ∈ La → a • x ∈ La` using `fun ha _ hx => hLat.smul_mem ⟨_, ha⟩ _ hx`. Establish `hdual : ∀ y, (∀ x ∈ La, IsIntegral ℤ (B y x)) → (m : E) • y ∈ La`. Introduce `y hy`.

Establish `hy' : y ∈ dualLattice h La` using `fun x hx => (mem_integralClosure_iff ℤ E).2 (hy x hx)`. Take `⟨t, ht⟩ : La.relIndex (dualLattice h La) ∣ m` from `Nat.dvd_factorial (Nat.pos_of_ne_zero hD.index_ne_zero) hD.index_le`. Rewrite using `[Nat.cast_smul_eq_nsmul, ht, mul_nsmul]`. Conclude with `La.nsmul_mem (La.nsmul_relIndex_mem hy') t`. Choose the witnesses or unpack the hypotheses as in `⟨v₁, hv₁l, hv₁0⟩ : ∃ v₁ ∈ l, v₁ ≠ 0 := by`.

Use `Submodule.exists_mem_ne_zero_of_ne_bot fun h0 => ?_` and prove the remaining obligations. Use `hl.1` as an intermediate fact. Rewrite `this` using `[h0, finrank_bot]`. Conclude with `zero_ne_one this`. Use `set J₁ := La.map (B v₁).toAddMonoidHom with hJ₁_def`.

Establish `hJ₁fg : J₁.FG` using `fg_map_of_fg hLat.fg _`. Establish `hJ₁ne : J₁ ≠ ⊥`. Introduce `h0`. Apply `hv₁0` to reduce the goal to its premises. Apply `h.nonsingular.1` to reduce the goal to its premises.

Rewrite using `[map_zero]`. Use `LinearMap.ext_on hLat.span_eq_top (fun x hx => ?_)` and prove the remaining obligations. Establish `: B v₁ x ∈ J₁` using `⟨x, hx, rfl⟩`. Rewrite `this` using `[h0, AddSubgroup.mem_bot]`. Simplify using `using this`.

Establish `hJ₁st : ∀ a : 𝓞 E, ∀ x ∈ J₁, (a : E) * x ∈ J₁`. Introduce and unpack `a _ ⟨x, hx, rfl⟩`. Conclude with `⟨(a : E) • x, hLat.smul_mem a x hx, by simp⟩`. Take `⟨J, hJT, c, hc, hJ₁⟩` from `hTJ J₁ hJ₁fg hJ₁ne hJ₁st`. Establish `hJfg : J.FG`.

Use `fg_of_le_fg (fun j hj => ?_) (fg_map_of_fg hJ₁fg (AddMonoidHom.mulLeft c⁻¹))` and prove the remaining obligations. Use `⟨c * j, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hJ₁]`. Conclude with `⟨j, hj, rfl⟩`. Simplify using `[← mul_assoc, inv_mul_cancel₀ hc]`.

Establish `hJne : J ≠ ⊥`. Introduce `h0`. Conclude with `hJ₁ne (by rw [hJ₁, h0, AddSubgroup.map_bot])`. Take `⟨hdJ, j₀, hj₀J, hj₀0, hdj₀⟩` from `hdT J (hT.mem_toFinset.2 hJT) hJfg hJne`. Use `set v := conjHom F E c⁻¹ • v₁ with hv_def`.

Establish `hBv : ∀ x, B v x = c⁻¹ * B v₁ x`. Introduce `x`. Rewrite using `[hv_def, hsmul, cc]`. Establish `hvJ : ∀ x ∈ La, B v x ∈ J`. Introduce `x hx`.

Establish `: B v₁ x ∈ J₁` using `⟨x, hx, rfl⟩`. Rewrite `this` using `[hJ₁]`. Take `⟨j, hj, hjx⟩` from `this`. Rewrite using `[hBv, ← hjx]`. Simplify `hj` using `[← mul_assoc, inv_mul_cancel₀ hc]`.

Establish `hJv : ∀ j ∈ J, ∃ x ∈ La, B v x = j`. Introduce `j hj`. Establish `: c * j ∈ J₁` using `by rw [hJ₁]; exact ⟨j, hj, rfl⟩`. Take `⟨x, hx, hxj⟩` from `this`. Use `⟨x, hx, ?_⟩` and prove the remaining obligations.

Rewrite using `[hBv]`. Establish `hxj' : B v₁ x = c * j` using `hxj`. Rewrite using `[hxj', ← mul_assoc, inv_mul_cancel₀ hc, one_mul]`. Establish `hv0 : v ≠ 0` using `smul_ne_zero ((map_ne_zero _).2 (inv_ne_zero hc)) hv₁0`. Establish `hvl : v ∈ l` using `l.smul_mem _ hv₁l`.

Establish `hvv : B v v = 0` using `hl.2 v hvl v hvl`. Establish `hdvx : ∀ x ∈ La, IsIntegral ℤ ((d : E) * B v x)` using `fun x hx => hdJ _ (hvJ x hx)`. Take `⟨x₁, hx₁, hx₁j⟩` from `hJv j₀ hj₀J`. Establish `hcj₀ : conjHom F E j₀ ≠ 0` using `(map_ne_zero _).2 hj₀0`. Establish `hIlo : intMultiples E (m * d) ≤ lineCoeffs (E` using `E) La v := by`.

Introduce `x hx`. Rewrite `hx` using `[mem_intMultiples]`. Generalize the expression as in `ho : ((m * d : ℕ) : E)⁻¹ * x = o at hx`. Establish `hxo : x = (m : E) * ((d : E) * o)`. Rewrite using `[← ho]`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Express the relevant statement in the definitionally equal form `x • v ∈ La`. Rewrite using `[hxo, ← smul_smul]`. Use `hdual _ fun z hz => ?_` and prove the remaining obligations.

Rewrite using `[hsmul, map_mul, cn, mul_comm (d : E), mul_assoc]`. Conclude with `(ci o hx).mul (hdvx z hz)`. Establish `hIup : ∀ a ∈ lineCoeffs (E` using `E) La v, IsIntegral ℤ ((d : E) * a) := by`. Introduce `a ha`. Establish `ha' : a • v ∈ La` using `ha`.

Establish `h1 : IsIntegral ℤ (conjHom F E a * j₀)`. Use `hint _ ha' x₁ hx₁` as an intermediate fact. Rewrite `this` using `[hsmul, hx₁j]`. Then use the resulting hypothesis. Establish `h2 : conjHom F E ((d : E) * a) = conjHom F E a * j₀ * ((d : E) * j₀⁻¹)`. Rewrite using `[map_mul, cn]`.

Clear the denominators using the available nonvanishing facts. Use `ci _ ((h1.mul hdj₀))` as an intermediate fact. Rewrite `this` using `[← h2, cc]`. Then use the resulting hypothesis. Use `set q := B x₁ x₁ / (conjHom F E j₀ * j₀) with hq_def`. Establish `hq : conjHom F E q = q`.

Rewrite using `[hq_def, map_div₀, hsym, map_mul, cc, mul_comm j₀]`. Establish `hq2 : conjHom F E (q / 2) = q / 2` using `by rw [map_div₀, hq, map_ofNat]`. Establish `hqi : IsIntegral ℤ ((d : E) ^ 2 * q)`. Establish `e1 : (d : E) ^ 2 * q = B x₁ x₁ * ((d : E) * j₀⁻¹) * conjHom F E ((d : E) * j₀⁻¹)`. Rewrite using `[hq_def, map_mul, map_inv₀, cn]`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[e1]`. Conclude with `((hint _ hx₁ _ hx₁).mul hdj₀).mul (ci _ hdj₀)`. Use `set w := j₀⁻¹ • x₁ - (q / 2) • v with hw_def`. Establish `hBw : ∀ x, B w x = conjHom F E j₀⁻¹ * B x₁ x - q / 2 * B v x`.

Introduce `x`. Rewrite using `[hw_def, LinearMap.map_sub₂, hsmul, hsmul, hq2]`. Establish `hvw : B v w = 1`. Rewrite using `[hw_def, (B v).map_sub, (B v).map_smul, (B v).map_smul, smul_eq_mul, smul_eq_mul, hx₁j, hvv, mul_zero, sub_zero, inv_mul_cancel₀ hj₀0]`. Establish `hww : B w w = 0`.

Rewrite using `[hBw, hvw]`. Establish `hx₁v : B x₁ v = conjHom F E j₀` using `by rw [← hsym, hx₁j]`. Rewrite using `[hw_def, (B x₁).map_sub, (B x₁).map_smul, (B x₁).map_smul, smul_eq_mul, smul_eq_mul, hx₁v, map_inv₀, hq_def]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Establish `hw0 : w ≠ 0`. Introduce `h0`. Rewrite `hvw` using `[h0, map_zero]`. Conclude with `zero_ne_one hvw`. Establish `hKlo : intMultiples E k ≤ lineCoeffs (E` using `E) La w := by`.

Introduce `b hb`. Rewrite `hb` using `[mem_intMultiples]`. Generalize the expression as in `ho : ((k : ℕ) : E)⁻¹ * b = o at hb`. Establish `hbo : b = (k : E) * o` using `by rw [← ho]; field_simp`. Express the relevant statement in the definitionally equal form `b • w ∈ La`.

Rewrite using `[hw_def, smul_sub, smul_smul, smul_smul]`. Use `La.sub_mem (hsm ?_ hx₁) ?_` and prove the remaining obligations. Establish `: b * j₀⁻¹ = ((2 * m * d ^ 2 : ℕ) : E) * o * ((d : E) * j₀⁻¹)`. Rewrite using `[hbo, hk_def]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `(isIntegral_natCast_mul hb).mul hdj₀`. Apply `hIlo` to reduce the goal to its premises. Rewrite using `[mem_intMultiples]`.

Establish `: ((m * d : ℕ) : E)⁻¹ * (b * (q / 2)) = (d : E) ^ 2 * q * o`. Rewrite using `[hbo, hk_def]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Rewrite using `[this]`.

Conclude with `hqi.mul hb`. Establish `hKup : ∀ b ∈ lineCoeffs (E` using `E) La w, IsIntegral ℤ ((d : E) * b) := by`. Introduce `b hb`. Establish `hb' : b • w ∈ La` using `hb`. Use `hdvx _ hb'` as an intermediate fact.

Rewrite `this` using `[map_smul, smul_eq_mul, hvw, mul_one]`. Then use the resulting hypothesis. Use `⟨v, w, hvl, ⟨hvv, hww, hvw⟩, ⟨⟨hIlo, fun a ha => ?_, LineCoeffsFG.proof W La v hLat.fg hv0⟩, ⟨hKlo, fun b hb => ?_, LineCoeffsFG.proof W La w hLat.fg hw0⟩⟩, fun x hx => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[nsmul_eq_mul, mem_intMultiples]`. Establish `: ((m * d : ℕ) : E)⁻¹ * ((m * d * d : ℕ) * a) = (d : E) * a` using `by push_cast; field_simp`. Rewrite using `[this]`.

Conclude with `hIup a ha`. Rewrite using `[nsmul_eq_mul, mem_intMultiples]`. Establish `: ((k : ℕ) : E)⁻¹ * ((k * d : ℕ) * b) = (d : E) * b` using `by push_cast; field_simp`. Rewrite using `[this]`. Conclude with `hKup b hb`.

Apply `hIlo` to reduce the goal to its premises. Rewrite using `[mem_intMultiples]`. Establish `: ((m * d : ℕ) : E)⁻¹ * (((k * d : ℕ) : E) * B w x) = 2 * (d : E) ^ 2 * conjHom F E ((d : E) * j₀⁻¹) * B x₁ x - (d : E) ^ 2 * q * ((d : E) * B v x)`. Rewrite using `[hBw, hk_def, map_mul, cn]`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[this]`. Use `IsIntegral.sub ?_ (hqi.mul (hdvx x hx))` and prove the remaining obligations. Establish `h2 : IsIntegral ℤ (2 * (d : E) ^ 2)`. Use `isIntegral_natCast_mul (n := 2 * d ^ 2) (isIntegral_one : IsIntegral ℤ (1 : E))` as an intermediate fact.

Simplify using `using this`. Conclude with `(h2.mul (ci _ hdj₀)).mul (hint _ hx₁ _ hx)`. Apply `hKlo` to reduce the goal to its premises. Rewrite using `[mem_intMultiples]`. Establish `: ((k : ℕ) : E)⁻¹ * (((k * d : ℕ) : E) * B v x) = (d : E) * B v x` using `by push_cast; field_simp`.

Rewrite using `[this]`. Conclude with `hdvx x hx`.
-/
theorem LineNormalForm.proof (h : HermitianForm F E W) : LineNormalForm.Statement h := by
  classical
  intro D
  set B := h.toSesq

  have cc : ∀ a : E, conjHom F E (conjHom F E a) = a := fun a => conj_conj (F := F) a
  have ci : ∀ a : E, IsIntegral ℤ a → IsIntegral ℤ (conjHom F E a) :=
    fun a ha => ha.map (conjHom F E).toIntAlgHom
  have cn : ∀ N : ℕ, conjHom F E (N : E) = N := fun N => map_natCast _ N
  have hsym : ∀ x y, conjHom F E (B x y) = B y x := fun x y => h.isSymm.eq x y
  have hsmul : ∀ (a : E) x y, B (a • x) y = conjHom F E a * B x y := by
    intro a x y
    rw [LinearMap.map_smulₛₗ₂, smul_eq_mul]

  obtain ⟨T, hT, hTJ⟩ := IdealClassesFinite.proof E
  obtain ⟨d, hd, hdT⟩ := exists_common_multiple hT.toFinset
    (fun J n => J.FG → J ≠ ⊥ → (∀ j ∈ J, IsIntegral ℤ ((n : E) * j)) ∧
        ∃ j₀ ∈ J, j₀ ≠ 0 ∧ IsIntegral ℤ ((n : E) * j₀⁻¹))
    (fun J a b hJ hab hfg hne => by
      obtain ⟨h1, j₀, hj₀, hj₀0, h2⟩ := hJ hfg hne
      exact ⟨fun j hj => isIntegral_mul_of_dvd (h1 j hj) hab, j₀, hj₀, hj₀0,
        isIntegral_mul_of_dvd h2 hab⟩)
    (fun J _ => by
      by_cases hfg : J.FG
      · by_cases hne : J = ⊥
        · exact ⟨1, one_pos, fun _ h => absurd hne h⟩
        · obtain ⟨a, ha, haJ⟩ := exists_den_of_fg hfg
          obtain ⟨j₀, hj₀, hj₀0⟩ : ∃ j₀ ∈ J, j₀ ≠ 0 := by
            by_contra hc
            push Not at hc
            exact hne ((AddSubgroup.eq_bot_iff_forall J).2 hc)
          obtain ⟨b, hb, hbj⟩ := exists_nat_mul_isIntegral j₀⁻¹
          exact ⟨a * b, Nat.mul_pos ha hb, fun _ _ =>
            ⟨fun j hj => isIntegral_mul_of_dvd (haJ j hj) (dvd_mul_right a b), j₀, hj₀, hj₀0,
              isIntegral_mul_of_dvd hbj (dvd_mul_left b a)⟩⟩
      · exact ⟨1, one_pos, fun h _ => absurd h hfg⟩)
  set m := D.factorial with hm_def
  have hm : 0 < m := Nat.factorial_pos D
  have hmd : 0 < m * d := Nat.mul_pos hm hd
  set k := 2 * m * d ^ 3 with hk_def
  have hk : 0 < k := by positivity
  have hm0 : (m : E) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have hd0 : (d : E) ≠ 0 := Nat.cast_ne_zero.2 hd.ne'
  have hk0 : (k : E) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  refine ⟨{A | intMultiples E (m * d) ≤ A ∧ (∀ x ∈ A, (m * d * d) • x ∈ intMultiples E (m * d)) ∧
      A.FG} ×ˢ {A | intMultiples E k ≤ A ∧ (∀ x ∈ A, (k * d) • x ∈ intMultiples E k) ∧ A.FG},
    (finite_sandwich _ (by positivity)).prod (finite_sandwich _ (by positivity)), k * d,
    Nat.mul_pos hk hd, ?_⟩
  intro La l hD hl
  have hLat := hD.isLattice
  have hint : ∀ x ∈ La, ∀ y ∈ La, IsIntegral ℤ (B x y) := fun x hx y hy =>
    (mem_integralClosure_iff ℤ E).1 (hD.integral x hx y hy)
  have hsm : ∀ {a : E}, IsIntegral ℤ a → ∀ {x}, x ∈ La → a • x ∈ La :=
    fun ha _ hx => hLat.smul_mem ⟨_, ha⟩ _ hx

  have hdual : ∀ y, (∀ x ∈ La, IsIntegral ℤ (B y x)) → (m : E) • y ∈ La := by
    intro y hy
    have hy' : y ∈ dualLattice h La := fun x hx => (mem_integralClosure_iff ℤ E).2 (hy x hx)
    obtain ⟨t, ht⟩ : La.relIndex (dualLattice h La) ∣ m := Nat.dvd_factorial (Nat.pos_of_ne_zero hD.index_ne_zero) hD.index_le
    rw [Nat.cast_smul_eq_nsmul, ht, mul_nsmul]
    exact La.nsmul_mem (La.nsmul_relIndex_mem hy') t

  obtain ⟨v₁, hv₁l, hv₁0⟩ : ∃ v₁ ∈ l, v₁ ≠ 0 := by
    refine Submodule.exists_mem_ne_zero_of_ne_bot fun h0 => ?_
    have := hl.1
    rw [h0, finrank_bot] at this
    exact zero_ne_one this
  set J₁ := La.map (B v₁).toAddMonoidHom with hJ₁_def
  have hJ₁fg : J₁.FG := fg_map_of_fg hLat.fg _
  have hJ₁ne : J₁ ≠ ⊥ := by
    intro h0
    apply hv₁0
    apply h.nonsingular.1
    rw [map_zero]
    refine LinearMap.ext_on hLat.span_eq_top (fun x hx => ?_)
    have : B v₁ x ∈ J₁ := ⟨x, hx, rfl⟩
    rw [h0, AddSubgroup.mem_bot] at this
    simpa using this
  have hJ₁st : ∀ a : 𝓞 E, ∀ x ∈ J₁, (a : E) * x ∈ J₁ := by
    rintro a _ ⟨x, hx, rfl⟩
    exact ⟨(a : E) • x, hLat.smul_mem a x hx, by simp⟩
  obtain ⟨J, hJT, c, hc, hJ₁⟩ := hTJ J₁ hJ₁fg hJ₁ne hJ₁st
  have hJfg : J.FG := by
    refine fg_of_le_fg (fun j hj => ?_) (fg_map_of_fg hJ₁fg (AddMonoidHom.mulLeft c⁻¹))
    refine ⟨c * j, ?_, ?_⟩
    · rw [hJ₁]; exact ⟨j, hj, rfl⟩
    · simp [← mul_assoc, inv_mul_cancel₀ hc]
  have hJne : J ≠ ⊥ := by
    intro h0
    exact hJ₁ne (by rw [hJ₁, h0, AddSubgroup.map_bot])
  obtain ⟨hdJ, j₀, hj₀J, hj₀0, hdj₀⟩ := hdT J (hT.mem_toFinset.2 hJT) hJfg hJne
  set v := conjHom F E c⁻¹ • v₁ with hv_def
  have hBv : ∀ x, B v x = c⁻¹ * B v₁ x := by
    intro x; rw [hv_def, hsmul, cc]
  have hvJ : ∀ x ∈ La, B v x ∈ J := by
    intro x hx
    have : B v₁ x ∈ J₁ := ⟨x, hx, rfl⟩
    rw [hJ₁] at this
    obtain ⟨j, hj, hjx⟩ := this
    rw [hBv, ← hjx]
    simpa [← mul_assoc, inv_mul_cancel₀ hc] using hj
  have hJv : ∀ j ∈ J, ∃ x ∈ La, B v x = j := by
    intro j hj
    have : c * j ∈ J₁ := by rw [hJ₁]; exact ⟨j, hj, rfl⟩
    obtain ⟨x, hx, hxj⟩ := this
    refine ⟨x, hx, ?_⟩
    rw [hBv]
    have hxj' : B v₁ x = c * j := hxj
    rw [hxj', ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  have hv0 : v ≠ 0 := smul_ne_zero ((map_ne_zero _).2 (inv_ne_zero hc)) hv₁0
  have hvl : v ∈ l := l.smul_mem _ hv₁l
  have hvv : B v v = 0 := hl.2 v hvl v hvl
  have hdvx : ∀ x ∈ La, IsIntegral ℤ ((d : E) * B v x) := fun x hx => hdJ _ (hvJ x hx)
  obtain ⟨x₁, hx₁, hx₁j⟩ := hJv j₀ hj₀J
  have hcj₀ : conjHom F E j₀ ≠ 0 := (map_ne_zero _).2 hj₀0

  have hIlo : intMultiples E (m * d) ≤ lineCoeffs (E := E) La v := by
    intro x hx
    rw [mem_intMultiples] at hx
    generalize ho : ((m * d : ℕ) : E)⁻¹ * x = o at hx
    have hxo : x = (m : E) * ((d : E) * o) := by
      rw [← ho]; push_cast; field_simp
    change x • v ∈ La
    rw [hxo, ← smul_smul]
    refine hdual _ fun z hz => ?_
    rw [hsmul, map_mul, cn, mul_comm (d : E), mul_assoc]
    exact (ci o hx).mul (hdvx z hz)
  have hIup : ∀ a ∈ lineCoeffs (E := E) La v, IsIntegral ℤ ((d : E) * a) := by
    intro a ha
    have ha' : a • v ∈ La := ha
    have h1 : IsIntegral ℤ (conjHom F E a * j₀) := by
      have := hint _ ha' x₁ hx₁
      rwa [hsmul, hx₁j] at this
    have h2 : conjHom F E ((d : E) * a) = conjHom F E a * j₀ * ((d : E) * j₀⁻¹) := by
      rw [map_mul, cn]; field_simp
    have := ci _ ((h1.mul hdj₀))
    rwa [← h2, cc] at this

  set q := B x₁ x₁ / (conjHom F E j₀ * j₀) with hq_def
  have hq : conjHom F E q = q := by
    rw [hq_def, map_div₀, hsym, map_mul, cc, mul_comm j₀]
  have hq2 : conjHom F E (q / 2) = q / 2 := by rw [map_div₀, hq, map_ofNat]
  have hqi : IsIntegral ℤ ((d : E) ^ 2 * q) := by
    have e1 : (d : E) ^ 2 * q = B x₁ x₁ * ((d : E) * j₀⁻¹) * conjHom F E ((d : E) * j₀⁻¹) := by
      rw [hq_def, map_mul, map_inv₀, cn]; field_simp
    rw [e1]
    exact ((hint _ hx₁ _ hx₁).mul hdj₀).mul (ci _ hdj₀)
  set w := j₀⁻¹ • x₁ - (q / 2) • v with hw_def
  have hBw : ∀ x, B w x = conjHom F E j₀⁻¹ * B x₁ x - q / 2 * B v x := by
    intro x
    rw [hw_def, LinearMap.map_sub₂, hsmul, hsmul, hq2]
  have hvw : B v w = 1 := by
    rw [hw_def, (B v).map_sub, (B v).map_smul, (B v).map_smul, smul_eq_mul, smul_eq_mul, hx₁j, hvv, mul_zero,
      sub_zero, inv_mul_cancel₀ hj₀0]
  have hww : B w w = 0 := by
    rw [hBw, hvw]
    have hx₁v : B x₁ v = conjHom F E j₀ := by rw [← hsym, hx₁j]
    rw [hw_def, (B x₁).map_sub, (B x₁).map_smul, (B x₁).map_smul, smul_eq_mul, smul_eq_mul, hx₁v,
      map_inv₀, hq_def]
    field_simp
    ring
  have hw0 : w ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hvw
    exact zero_ne_one hvw

  have hKlo : intMultiples E k ≤ lineCoeffs (E := E) La w := by
    intro b hb
    rw [mem_intMultiples] at hb
    generalize ho : ((k : ℕ) : E)⁻¹ * b = o at hb
    have hbo : b = (k : E) * o := by rw [← ho]; field_simp
    change b • w ∈ La
    rw [hw_def, smul_sub, smul_smul, smul_smul]
    refine La.sub_mem (hsm ?_ hx₁) ?_
    · have : b * j₀⁻¹ = ((2 * m * d ^ 2 : ℕ) : E) * o * ((d : E) * j₀⁻¹) := by
        rw [hbo, hk_def]; push_cast; ring
      rw [this]
      exact (isIntegral_natCast_mul hb).mul hdj₀
    · apply hIlo
      rw [mem_intMultiples]
      have : ((m * d : ℕ) : E)⁻¹ * (b * (q / 2)) = (d : E) ^ 2 * q * o := by
        rw [hbo, hk_def]; push_cast; field_simp
      rw [this]
      exact hqi.mul hb
  have hKup : ∀ b ∈ lineCoeffs (E := E) La w, IsIntegral ℤ ((d : E) * b) := by
    intro b hb
    have hb' : b • w ∈ La := hb
    have := hdvx _ hb'
    rwa [map_smul, smul_eq_mul, hvw, mul_one] at this
  refine ⟨v, w, hvl, ⟨hvv, hww, hvw⟩, ⟨⟨hIlo, fun a ha => ?_, LineCoeffsFG.proof W La v hLat.fg hv0⟩,
    ⟨hKlo, fun b hb => ?_, LineCoeffsFG.proof W La w hLat.fg hw0⟩⟩, fun x hx => ⟨?_, ?_⟩⟩
  · rw [nsmul_eq_mul, mem_intMultiples]
    have : ((m * d : ℕ) : E)⁻¹ * ((m * d * d : ℕ) * a) = (d : E) * a := by
      push_cast; field_simp
    rw [this]; exact hIup a ha
  · rw [nsmul_eq_mul, mem_intMultiples]
    have : ((k : ℕ) : E)⁻¹ * ((k * d : ℕ) * b) = (d : E) * b := by
      push_cast; field_simp
    rw [this]; exact hKup b hb

  · apply hIlo
    rw [mem_intMultiples]
    have : ((m * d : ℕ) : E)⁻¹ * (((k * d : ℕ) : E) * B w x) =
        2 * (d : E) ^ 2 * conjHom F E ((d : E) * j₀⁻¹) * B x₁ x - (d : E) ^ 2 * q * ((d : E) * B v x) := by
      rw [hBw, hk_def, map_mul, cn]; push_cast; field_simp
    rw [this]
    refine IsIntegral.sub ?_ (hqi.mul (hdvx x hx))
    have h2 : IsIntegral ℤ (2 * (d : E) ^ 2) := by
      have := isIntegral_natCast_mul (n := 2 * d ^ 2) (isIntegral_one : IsIntegral ℤ (1 : E))
      simpa using this
    exact (h2.mul (ci _ hdj₀)).mul (hint _ hx₁ _ hx)
  · apply hKlo
    rw [mem_intMultiples]
    have : ((k : ℕ) : E)⁻¹ * (((k * d : ℕ) : E) * B v x) = (d : E) * B v x := by
      push_cast; field_simp
    rw [this]; exact hdvx x hx

end NormalForm

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
